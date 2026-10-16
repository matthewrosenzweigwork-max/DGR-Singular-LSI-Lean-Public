#!/usr/bin/env python3
"""Inventory a committed source snapshot without running Lean or Lake.

Usage: python3 scripts/release_inventory.py [git-revision]
This is a lexical preparation aid, not Palomar's parser or verifier.
"""
import io
import json
from pathlib import PurePosixPath, Path
import re
import subprocess
import sys
import tarfile

root = Path(__file__).resolve().parents[1]
revision = sys.argv[1] if len(sys.argv) > 1 else "HEAD"
commit = subprocess.check_output(["git", "rev-parse", "--verify", revision + "^{commit}"], cwd=root, text=True).strip()
archive = subprocess.check_output(["git", "archive", commit], cwd=root)

def leading_module(text):
    i = 0
    while i < len(text):
        if text[i].isspace():
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end + 1
        elif text.startswith("/-", i):
            i += 2
            depth = 1
            while i < len(text) and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
        else:
            break
    return re.match(r"module\b", text[i:]) is not None

files = []
missing = []
header_count = 0
exempt_count = 0
symlinks = []
lfs = []
artifacts = []
tracked_bytes = 0
regular_files = 0
suffixes = {".olean", ".ilean", ".a", ".bc", ".dll", ".dylib", ".o", ".obj", ".so", ".trace"}
with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
    for member in tar:
        path = PurePosixPath(member.name)
        if member.issym() or member.islnk():
            symlinks.append(member.name)
        if not member.isfile():
            continue
        data = tar.extractfile(member).read()
        tracked_bytes += len(data)
        regular_files += 1
        if data.startswith(b"version https://git-lfs.github.com/spec/v1"):
            lfs.append(member.name)
        if ".lake" in path.parts or ".git" in path.parts:
            continue
        if path.suffix in suffixes:
            artifacts.append(member.name)
        if path.suffix != ".lean":
            continue
        lines = len(re.split(rb"\r\n|\n", data)) - int(data.endswith(b"\n")) if data else 0
        files.append({"path": member.name, "physical_lines": lines, "bytes": len(data)})
        has_header = leading_module(data.decode("utf-8"))
        exempt = path.name == "lakefile.lean"
        header_count += int(has_header)
        exempt_count += int(exempt)
        if not has_header and not exempt:
            missing.append(member.name)

groups = {}
for path in missing:
    parent = str(PurePosixPath(path).parent)
    groups[parent] = groups.get(parent, 0) + 1
print(json.dumps({
    "commit": commit,
    "method": "git archive; lexical leading-token scan; LF/CRLF physical line count; no Lean build",
    "regular_files": regular_files,
    "regular_file_bytes": tracked_bytes,
    "lean_files_outside_git_and_lake": len(files),
    "module_headers_found": header_count,
    "lakefile_header_exemptions": exempt_count,
    "missing_module_headers": len(missing),
    "missing_headers_by_directory": dict(sorted(groups.items())),
    "missing_header_examples": missing[:10],
    "over_10000_lines": [f for f in files if f["physical_lines"] > 10000],
    "largest_lean_files": sorted(files, key=lambda f: (-f["physical_lines"], f["path"]))[:10],
    "symlinks": symlinks,
    "lfs_pointers": lfs,
    "compiled_artifacts_outside_lake": artifacts,
    "submodules": [line for line in subprocess.check_output(["git", "ls-tree", "-r", commit], cwd=root, text=True).splitlines() if line.startswith("160000 ")],
    "limitations": "Not a Lean-parser, dependency-authentication, build, axiom, correspondence, Comparator, or registry check."
}, indent=2))
