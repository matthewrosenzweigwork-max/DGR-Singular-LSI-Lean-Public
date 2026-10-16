# Public release preparation

Status on 16 October 2026: this `release-preparation-2026-10-16` branch contains documentation, metadata, licensing, and byte-integrity automation. Its accepted source inputs and toolchain pins are unchanged. The owner-approved Apache-2.0 license is present; existing third-party notices are retained.

The [hosted frozen-source integrity check](https://github.com/matthewrosenzweigwork-max/DGR-Singular-LSI-Lean-Public/actions/runs/38929862538) passed for all 485 manifest inputs. The inventory and staged plan below describe this frozen branch. Compatibility migration, complete statement metadata, and fresh verification are tracked separately on [`palomar-migration-2026-10-16`](https://github.com/matthewrosenzweigwork-max/DGR-Singular-LSI-Lean-Public/tree/palomar-migration-2026-10-16). Neither branch changes public `main`, and no Palomar intake or registration has been performed.

The separate compatibility candidate now has passing full reports for both components at `587bf340cfd5fcf808d37105532d470dd3552b3b`. The [permanent report copies and exact reproduction commands](palomar/FULL_PREFLIGHT_EVIDENCE.md) supersede the prospective migration/verification steps below. The inventory remains an account of the frozen baseline, and the old metadata draft is historical. Review and any later intake or main update remain separate owner decisions.

## Snapshot and build

The accepted public baseline is `933ab9a859aaa54a26246a4aeac1d92972c20c2d`, copied from upstream `664d3fdb102267d3e7440fd4889dc2fe1a354855`. The existing `SOURCE_MANIFEST.json` binds 485 inputs. Both projects pin `leanprover/lean4:v4.33.0` and canonical Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. Reading that Mathlib revision's `lean-toolchain` confirmed an exact match.

From the repository root:

```sh
python3 scripts/check-source-integrity.py
(cd trials/periodic/project && lake exe cache get && lake build)
(cd trials/whole-space/project && lake exe cache get && lake build)
```

The Python check was run successfully during this preparation. The Lake commands are the configured library build commands and were not run here. They do not build the separate application files. Reproducing those checks requires restoring their source-path setup and original checking commands from the historical campaign. Historical verification is described in the README, but its full logs and certificates are absent from this public mirror.

## Concrete inventory

[RELEASE_INVENTORY.json](RELEASE_INVENTORY.json) records the accepted commit's static scan. Reproduce it with:

```sh
python3 scripts/release_inventory.py 933ab9a859aaa54a26246a4aeac1d92972c20c2d
```

- 490 regular tracked files, totaling 3,354,973 bytes; 479 Lean files including two `lakefile.lean` files.
- Zero module headers found. The two Lakefiles are exempt from the header rule, leaving 477 files needing migration.
- No file exceeds 10,000 physical lines; the largest has 758. No submodule gitlinks, symlinks, Git LFS pointers, or listed compiled artifacts were found in the submitted tree.
- Both committed manifests use public HTTPS GitHub Git URLs and full lowercase 40-character commit revisions. These syntactic checks do not authenticate dependency bytes.
- There is no root Lake project, completed `formalization.yaml`, Challenge/Solution pair, Comparator configuration, or current full Palomar workflow report.
- Lean 4.33.0 is below the currently declared Palomar minimum, v4.35.0-rc2. A new toolchain also requires a matching new Mathlib pin and source migration.

These are lexical/source inventory checks, not a Lean parser run or certification of registry compliance. Dependencies fetched in a future build were not scanned.

## Scope and layout choices

The periodic component covers LSI and Poincaré results. The whole-space component covers Riesz Poincaré results and makes no whole-space Riesz LSI claim. Preserve this distinction in titles, abstracts, theorem selections, and any registry entry.

The existing `trials/periodic/project` and `trials/whole-space/project` are independent Lake projects with the same package/library name `tablet`/`Tablet`. Keep their builds separate. A practical first submission design is one project path and one Comparator configuration for each component; each configuration is a separate registry entry. Confirm the current project's metadata-root/path handling before authoring these files. An umbrella project with namespaced modules would require additional source changes. The all-source rule applies to the whole submitted repository, so selecting one subproject does not exempt the other from module migration.

Existing application adapters import project-specific `Tablet.*` definitions and cannot serve unchanged as a permitted Challenge. The statement-definition surface needs deliberate reconstruction against approved dependencies; no claim is made that it already fits the Challenge limits.

## Decisions and evidence still needed

- The owner authorized Apache-2.0 for both repositories and confirmed authority on behalf of the authors. The root license and draft SPDX metadata now agree. Existing third-party notices remain intact.
- Confirm the human author and responsible-maintainer lists, precise paper/source titles and identifiers, source relationships, historical automation roles, and completed review status. Existing citations establish attribution, not a new endorsement of a submission.
- Select the principal declarations to register and document all their actual hypotheses and limitations. Supporting targets do not automatically become advertised principal results. A fresh statement/argument correspondence audit remains distinct from a kernel check.
- Recover or link the exact historical machine-readable receipts and logs from the original verification campaigns if they will be cited as release evidence. The public summaries alone do not reproduce those runs.

[formalization.yaml.draft](formalization.yaml.draft) supplies a conservative abstract and proposed classification. Empty provenance and automation fields are deliberate unresolved decisions. Do not copy it to the project root as submission-ready metadata. No Comparator configuration is supplied: its theorem list cannot be finalized before the statement surface is designed.

## Staged route to Palomar

1. Review and commit the documentation changes separately from the accepted source snapshot. Keep the accepted commit and manifests available as the reproducible historical baseline.
2. Create a separate submission-migration branch. Choose an accepted Lean release at or above the current minimum together with canonical Mathlib at an exactly matching Lean toolchain; regenerate manifests only there. Port every committed Lean file, including contained projects and applications, to the module system with appropriate public declarations/imports and exposed bodies. Adding a header alone is insufficient. Rebuild and recheck the changed interfaces.
3. Construct a small Challenge using only the allowed canonical dependency closure. Project-specific definitions needed for the statement must be stated directly in that audited file, with their ordinary mathematical meaning, rather than imported from the project. Prove the corresponding Solution declarations and compare the actual types/definition values. Preserve all main claims attributed to the selected formalization and disclose limitations. Aim below 300 lines/32 KiB; the hard Challenge caps are 1,000 physical lines and 100 KiB.
4. Complete the v0.4 metadata, approved root license, and one Comparator configuration per intended entry. Use only the permitted standard axioms (`propext`, `Classical.choice`, `Quot.sound`) in Solution closures. Recheck full dependency identities, artifacts, source visibility, and correspondence on the new commit.
5. Re-read and pin the actual current verifier commit before adding or running CI. The reusable `PalomarRegistry/PalomarSubmission/.github/workflows/submission.yml` reference and its `pipeline_commit` must be the same full SHA; use `mode: full`, `execution_profile: palomar-standard-v1`, and the exact repository commit/project/configuration paths. Require a passing mechanical report. The completed separate candidate workflow and preserved reports are linked above; this frozen branch runs integrity and evidence checks.
6. Review the resulting exact-commit reports before any intake or registration. Intake authorization and its temporary tag/gist mechanism are separate later actions; no tag, gist, submission, or registry entry has been created here.

The current verifier describes bundled `lake comparator`, `leanexport`, `leanchecker`, NanoDa and con-ron under bubblewrap. Older policy passages describing other tool names must not be used as a current execution recipe. Historical checks are evidence about their recorded snapshot, not a pass of today's reusable workflow.

## Sources checked on 16 October 2026

- [Current contribution policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md), read in GitHub HTML rather than relying on a cached raw copy.
- [Current intake and preflight instructions](https://submit.palomar-registry.org/llms.txt).
- [Minimum toolchain declaration](https://github.com/PalomarRegistry/PalomarSubmission/blob/main/toolchains.json).
- [Verifier and reusable-workflow documentation](https://github.com/PalomarRegistry/PalomarSubmission).

These are preparation references, not a pinned verifier choice. Recheck them when scheduling a migration or full preflight.
