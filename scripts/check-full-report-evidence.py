"""Validate report claims against immutable Git inputs; no network or builds.

GitHub run/job/artifact identity and the downloaded ZIP digest still require an
independent authenticated GitHub check. A local receipt cannot authenticate itself.
"""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path, PurePosixPath


def check(condition, message):
    if not condition:
        raise SystemExit("REPORT NOT ACCEPTED: " + message)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def relative_path(value, label):
    check(isinstance(value, str) and value != "", label + " is missing")
    path = PurePosixPath(value)
    check(not path.is_absolute() and ".." not in path.parts and path.as_posix() == value,
          label + " must be a normalized repository-relative path")
    return value


def check_receipt(receipt, report, report_bytes, commit, repository):
    """Check embedded claims and identifier formats, not external authenticity."""
    for key in ("commit", "report_sha256", "status", "stage", "challenge_trust_level",
                "warnings", "run_id", "job_id", "artifact_id", "artifact_sha256",
                "workflow_commit", "report_path"):
        check(key in receipt, "receipt field is missing: " + key)
    for key, expected in (
        ("commit", commit), ("report_sha256", sha256(report_bytes)),
        ("status", report["status"]), ("stage", report["stage"]),
        ("challenge_trust_level", report["challenge"]["trust_level"]),
        ("warnings", report.get("warnings", [])),
    ):
        check(receipt[key] == expected, "receipt mismatch: " + key)
    relative_path(receipt["report_path"], "receipt report_path")
    for key in ("run_id", "job_id", "artifact_id"):
        check(type(receipt[key]) is int and receipt[key] > 0,
              "receipt identifier must be a positive integer: " + key)
    for key, digits in (("artifact_sha256", 64), ("workflow_commit", 40)):
        check(isinstance(receipt[key], str) and
              re.fullmatch(r"[0-9a-f]{" + str(digits) + r"}", receipt[key]) is not None,
              "receipt identifier has invalid format: " + key)
    check(receipt["workflow_commit"] == "d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44",
          "receipt verifier workflow pin mismatch")
    expected_url = f"https://github.com/{repository}/actions/runs/{receipt['run_id']}"
    check(report.get("workflow_url") == expected_url, "receipt workflow run URL mismatch")


def validate(report_path, repo, commit, component, receipts_path=None):
    report_bytes = report_path.read_bytes()
    j = json.loads(report_bytes)
    prefix = "" if component == "planar" else f"trials/{component}/project/"
    expected_repo = "matthewrosenzweigwork-max/" + (
        "LSI-2D-Diffusive-Coulomb-Gas-Lean-Public" if component == "planar"
        else "DGR-Singular-LSI-Lean-Public")
    check(re.fullmatch(r"[0-9a-f]{40}", commit) is not None,
          "candidate must be a full immutable commit hash")

    def blob(path):
        relative_path(path, "Git input path")
        return subprocess.check_output(["git", "-C", str(repo), "show", commit + ":" + path])

    def input_bytes(field, expected_path):
        record = j.get(field, {})
        check(record.get("path") == expected_path, field + " input path mismatch")
        data = blob(expected_path)
        check(record.get("sha256") == sha256(data), field + " file hash mismatch")
        return data

    check(j.get("status") == "pass" and j.get("phase") == "verification" and
          j.get("stage") == "complete", "full verification did not complete with pass")
    check(j.get("errors") == [], "report contains errors")
    check(j.get("source", {}).get("commit") == commit, "source commit mismatch")
    check(j["source"].get("repository") == expected_repo, "source repository mismatch")
    check(j["source"].get("project_path", "") == prefix.rstrip("/"), "project path mismatch")
    check(j.get("lean_toolchain") == "leanprover/lean4:v4.35.0-rc2", "Lean toolchain mismatch")
    check(j.get("toolchain_commit") == "11acb17ec6b07a8f9e9173e6845197929540936b",
          "Lean source commit mismatch")
    check(j.get("execution_profile") == "palomar-standard-v1", "execution profile mismatch")
    check(j.get("mathlib_toolchain") == [{"revision": "065356127b1dc0016f66b7283ce0ce2c4055aa55",
          "toolchain": "leanprover/lean4:v4.35.0-rc2"}], "Mathlib pin mismatch")
    config_bytes = input_bytes("comparator", prefix + "comparator.json")
    config = json.loads(config_bytes)
    actual = j.get("comparator", {})
    for key in ("challenge_module", "solution_module", "theorem_names", "definition_names", "permitted_axioms"):
        check(actual.get(key, []) == config.get(key, []), "Comparator selection mismatch: " + key)
    for field, module_key in (("challenge", "challenge_module"), ("solution", "solution_module")):
        check(j.get(field, {}).get("module") == config[module_key], field + " module mismatch")
        input_bytes(field, prefix + config[module_key].replace(".", "/") + ".lean")
    lake_format = j.get("lakefile", {}).get("format")
    check(lake_format in ("lean", "toml"), "unknown Lake configuration format")
    input_bytes("lakefile", prefix + "lakefile." + lake_format)
    input_bytes("lake_manifest", prefix + "lake-manifest.json")
    input_bytes("formalization", prefix + "formalization.yaml")
    check(j.get("lean_toolchain_path") == prefix + "lean-toolchain", "Lean toolchain path mismatch")
    check(blob(prefix + "lean-toolchain").decode().strip() == j["lean_toolchain"],
          "Lean toolchain file contents mismatch")
    challenge = j["challenge"]
    check(challenge.get("trust_level") == "high" and challenge.get("untrusted_sources") == [],
          "Challenge provenance did not receive high trust")
    check({k.get("name") for k in j.get("kernels", [])} == {"nanoda", "con-ron"},
          "independent kernel configuration mismatch")
    protected_bytes = j.get("protected_config", "").encode()
    protected = json.loads(protected_bytes)
    check(sha256(protected_bytes) == j.get("protected_config_sha256"), "protected configuration hash mismatch")
    for key in ("theorem_names", "definition_names", "permitted_axioms"):
        check(protected.get(key, []) == config.get(key, []), "protected Comparator selection mismatch: " + key)
    check(protected.get("solution_module") == config["solution_module"], "protected Solution module mismatch")
    check(set(protected.get("external_kernels", {})) == {"nanoda", "con-ron"},
          "protected independent kernels missing")
    log = j.get("comparator_log_tail", "")
    for message in ("con-ron kernel accepts the solution", "nanoda kernel accepts the solution",
                    "Lean default kernel accepts the solution", "Your solution is okay!"):
        check(message in log, "kernel acceptance evidence missing: " + message)
    license_info = j.get("license", {})
    check(license_info.get("declared_identifier") == "Apache-2.0" and
          license_info.get("detected_identifier") == "Apache-2.0", "license mismatch")
    license_path = relative_path(license_info.get("path"), "license path")
    check(license_info.get("sha256") == sha256(blob(license_path)), "license bytes mismatch")
    if receipts_path is not None:
        receipts = json.loads(receipts_path.read_text())
        check(component in receipts, "component receipt is missing: " + component)
        receipt = receipts[component]
        check_receipt(receipt, j, report_bytes, commit, expected_repo)
        # Private receipt paths are relative to the workspace containing this ledger.
        check((receipts_path.parent.parent / receipt["report_path"]).resolve() == report_path.resolve(),
              "receipt report path does not identify this report")
    index_path = report_path.parent.parent / "FULL_PREFLIGHT_EVIDENCE.json"
    if index_path.is_file():
        index = json.loads(index_path.read_text())
        records = [r for r in index["records"] if r["component"] == component]
        check(index.get("repository") == expected_repo, "report index repository mismatch")
        check(index.get("candidate_commit") == commit and len(records) == 1,
              "report index candidate/component mismatch")
        check_receipt(records[0], j, report_bytes, commit, expected_repo)
        check((repo / records[0]["report_path"]).resolve() == report_path.resolve(),
              "report index path does not identify this report")
        check(records[0].get("theorem_names") == config["theorem_names"] and
              records[0].get("definition_names", []) == config.get("definition_names", []),
              "report index Comparator selection mismatch")
        check(records[0].get("challenge_sha256") == challenge["sha256"],
              "report index Challenge hash mismatch")
    return {"accepted": True, "component": component, "commit": commit,
            "theorems": len(config["theorem_names"]), "definitions": len(config.get("definition_names", [])),
            "challenge_lines": challenge.get("lines"), "workflow_url": j.get("workflow_url"),
            "warnings": j.get("warnings", []),
            "receipt_checked": receipts_path is not None or index_path.is_file(),
            "preserved_index_checked": index_path.is_file(),
            "artifact_provenance": "requires independent authenticated GitHub run/job/artifact/digest verification"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path)
    parser.add_argument("repo", type=Path)
    parser.add_argument("commit")
    parser.add_argument("component", choices=["periodic", "whole-space", "planar"])
    parser.add_argument("--receipts", type=Path, help="Private component receipt ledger; also check its consistency")
    args = parser.parse_args()
    print(json.dumps(validate(args.report, args.repo, args.commit, args.component, args.receipts), indent=2))


if __name__ == "__main__":
    main()
