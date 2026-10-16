# Exact-commit full preflight evidence

Both components passed the full Palomar preflight at candidate commit
[`587bf340cfd5fcf808d37105532d470dd3552b3b`](https://github.com/matthewrosenzweigwork-max/DGR-Singular-LSI-Lean-Public/tree/587bf340cfd5fcf808d37105532d470dd3552b3b).
The [completed workflow](https://github.com/matthewrosenzweigwork-max/DGR-Singular-LSI-Lean-Public/actions/runs/38946980451)
and both verification jobs succeeded. This is mechanical preflight evidence;
no Palomar intake, authorization tag/gist, registry registration, or main update
has been performed.

| Component | Selected theorems | Challenge | Result |
|---|---:|---:|---|
| Periodic LSI and Poincare | 3 complete endpoints | 286 lines, high trust | pass, complete, no warnings |
| Whole-space Riesz Poincare | 3 complete endpoints | 296 lines, high trust | pass, complete, no warnings |

The whole-space component makes no logarithmic Sobolev claim. The candidate's
design and bounded source-review records document the exact hypotheses, fixed
physical definitions, complete conjunction clauses, and compatibility changes.
The automated source review is distinct from external human review or a full
manuscript argument audit.

## Preserved reports and pins

The raw [periodic report](reports/periodic-mechanical-report.json) and
[whole-space report](reports/whole-space-mechanical-report.json) are preserved
here so the evidence survives GitHub artifact expiration.
[FULL_PREFLIGHT_EVIDENCE.json](FULL_PREFLIGHT_EVIDENCE.json) records their SHA256
hashes, the verified downloaded archive digests, job/artifact IDs, selected
declarations, Challenge hashes, and immutable candidate commit.

- Verifier workflow and `pipeline_commit`: `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`.
  The completed GitHub run's referenced-workflow metadata confirms this SHA.
- Execution profile: `palomar-standard-v1`, full mode, including Comparator and
  the configured NanoDa and con-ron independent kernels.
- Lean: `leanprover/lean4:v4.35.0-rc2`, source commit `11acb17ec6b07a8f9e9173e6845197929540936b`.
- Canonical Mathlib: `065356127b1dc0016f66b7283ce0ce2c4055aa55`, with the same Lean toolchain.
- Declared and detected project license: Apache-2.0. Third-party notices remain in force.

The accepted frozen public baseline remains
`933ab9a859aaa54a26246a4aeac1d92972c20c2d`, with its original 485-input manifest.
This preparation branch retains those source/configuration bytes and old pins;
the separate verified candidate records each migration change in its ledger.
Evidence files on this branch do not change the verified candidate commit.

## Reproduction

In a checkout of the candidate commit, use the committed locks and run:

```sh
python3 scripts/check_migration.py
(cd trials/periodic/project && lake exe cache get && lake build Tablet Challenge Solution)
(cd trials/whole-space/project && lake exe cache get && lake build Tablet Challenge Solution)
```

These compile the libraries and compact surfaces. The linked full workflow is
the evidence for Comparator, provenance and independent-kernel verification.
The source libraries also passed separate hosted source builds before the
cache-only Challenge correspondence adjustment, which the full run rebuilt.

To validate the preserved reports against the actual candidate Git objects
from this preparation checkout, fetch the migration branch if using a shallow
clone, then run:

```sh
python3 scripts/check-full-report-evidence.py docs/palomar/reports/periodic-mechanical-report.json . 587bf340cfd5fcf808d37105532d470dd3552b3b periodic
python3 scripts/check-full-report-evidence.py docs/palomar/reports/whole-space-mechanical-report.json . 587bf340cfd5fcf808d37105532d470dd3552b3b whole-space
```

Intake and publication remain separate owner decisions. A later changed commit
requires its own full report.
