# Singular Riesz functional inequalities in Lean

[![Palomar full preflight](https://github.com/matthewrosenzweigwork-max/DGR-Singular-LSI-Lean-Public/actions/workflows/palomar-full.yml/badge.svg?branch=palomar-migration-2026-10-16)](https://github.com/matthewrosenzweigwork-max/DGR-Singular-LSI-Lean-Public/actions/workflows/palomar-full.yml?query=branch%3Apalomar-migration-2026-10-16)

Matias Delgadino, Rishabh Gvalani, and Matthew Rosenzweig.

This repository formalizes periodic logarithmic Sobolev and Poincaré inequalities and whole-space Riesz Poincaré inequalities. The whole-space component makes no logarithmic Sobolev claim. Precise hypotheses and conclusions are given by the linked declarations.

This branch is a compatibility candidate for Palomar. Its new toolchain, module interfaces, and documented API repairs require fresh exact-commit verification; historical checks do not certify the migrated sources. No Palomar intake or registration has been performed.

## Sources and statements

- [Periodic library](trials/periodic/project/Tablet.lean): uniform, modulated, and external-potential full-gradient inequalities.
- [Whole-space library](trials/whole-space/project/Tablet.lean): bounded-Hessian and growth-class closed Poincaré inequalities.
- [Periodic Challenge](trials/periodic/project/Challenge.lean) and [whole-space Challenge](trials/whole-space/project/Challenge.lean): compact statements using canonical Mathlib, with exact physical definitions and hypotheses.
- Each project's `Solution.lean` imports the existing implementation; `comparator.json` selects every Challenge hole. Its `formalization.yaml` records provenance, authorship, automation, and scope.
- [Periodic application checks](trials/periodic/applications/) and [whole-space application checks](trials/whole-space/applications/) retain historical specializations outside the Lake library roots.

## Build and verification

Both independent projects pin Lean `v4.35.0-rc2` and canonical Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`. Install elan from its official distribution and retain the committed dependency locks. From the repository root:

```sh
python3 scripts/check_migration.py
(cd trials/periodic/project && lake exe cache get && lake build Tablet Challenge Solution)
(cd trials/whole-space/project && lake exe cache get && lake build Tablet Challenge Solution)
```

These commands compile source and statements. They do not substitute for Palomar's Comparator, independent kernels, and provenance checks. The [full verification workflow](.github/workflows/palomar-full.yml) pins the reusable verifier and `pipeline_commit` to `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`, with `mode: full` and `palomar-standard-v1`. Only its actual report for an exact commit establishes a pass. See [workflow runs](https://github.com/matthewrosenzweigwork-max/DGR-Singular-LSI-Lean-Public/actions) and [migration status](docs/palomar/MIGRATION_STATUS.md).

## Frozen provenance

The accepted public baseline is `933ab9a859aaa54a26246a4aeac1d92972c20c2d`, copied from upstream `664d3fdb102267d3e7440fd4889dc2fe1a354855`. It pins Lean 4.33.0 and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. `SOURCE_MANIFEST.json` preserves the SHA-256 and original Git blob identities of its 485 inputs. Run `python3 scripts/check-source-integrity.py` on that frozen baseline or the separate preparation branch.

On this migration branch, the original checker intentionally rejects changed inputs. [MIGRATION_LEDGER.json](docs/palomar/MIGRATION_LEDGER.json) records before/after hashes and distinguishes module-interface changes from explicit API repairs. No frozen manifest has been rewritten to imply that new bytes are the accepted old bytes.

The historical snapshot passed builds, kernel replays, and type/axiom checks in its original campaign. Those records concern that snapshot; the public mirror omits full historical logs and certificates. The selected permitted logical axioms are `propext`, `Classical.choice`, and `Quot.sound`. Kernel acceptance and correspondence to written mathematics remain separate review questions.

## Citation and license

See [CITATION.bib](CITATION.bib) and [CITATION.cff](CITATION.cff). This software release accompanies the mathematical work.

Original repository code is licensed under [Apache-2.0](LICENSE). Existing third-party notices and dependency licenses remain in force; see [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md). The [release inventory](docs/RELEASE_PREPARATION.md) describes the separately preserved frozen snapshot.
