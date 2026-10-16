# Singular Riesz functional inequalities in Lean

Matias Delgadino, Rishabh Gvalani, and Matthew Rosenzweig.

This repository contains the Lean proof sources for periodic logarithmic Sobolev and Poincaré inequalities and whole-space Riesz Poincaré inequalities. Precise assumptions and conclusions are given by the declarations linked below. The whole-space component does not claim a whole-space logarithmic Sobolev inequality.

## Proof sources

- [Periodic library](trials/periodic/project/Tablet.lean): 312 proof modules, including the uniform, modulated, and external-potential full-gradient inequalities.
- [Whole-space library](trials/whole-space/project/Tablet.lean): 154 proof modules, including bounded-Hessian and growth-class closed Poincaré inequalities.
- [Periodic application checks](trials/periodic/applications/) and [whole-space application checks](trials/whole-space/applications/) provide concrete specialization and statement checks.

All 466 proof modules are dependencies of their respective library entrypoint. The proof files, application files, toolchain declarations, and dependency manifests are unchanged from the source snapshot. Historical duplicate trees, archived ZIP files, and operational logs are omitted.

## Build

Install elan from its official distribution. From the repository root, build the two independent projects in separate subshells:

```sh
(cd trials/periodic/project && lake exe cache get && lake build)
(cd trials/whole-space/project && lake exe cache get && lake build)
```

Both projects pin Lean 4.33.0 and Mathlib commit `db584cd6d46c92f209a44c0f1c829460d327499d`. The exact transitive dependency revisions are in each `lake-manifest.json`.

These commands build the `Tablet` libraries. The application files are outside their Lake source directories and are not additional default build targets. Their historical checking commands and logs are not included in this mirror.

To run a Lean kernel replay after building, use `lake env leanchecker Tablet.ModuleName`, replacing `ModuleName` with the module being checked. Application checks are supplied separately and may require adding their containing directory to the Lean search path.

## Provenance and verification

`SOURCE_MANIFEST.json` records the SHA-256 and original Git blob identity of every copied input. Run `python3 scripts/check-source-integrity.py` to check those bytes.

The source snapshot had successful source builds, kernel replays, and type/axiom checks in its original verification campaign; its GitHub verification run on 14 October 2026 also passed. This clean mirror preserves the checked proof bytes. Publication of this mirror is not a new independent kernel-verification run. Standard logical axioms permitted by the source projects are `propext`, `Classical.choice`, and `Quot.sound`.

The upstream snapshot is commit `664d3fdb102267d3e7440fd4889dc2fe1a354855`. No upstream runtime Git history is imported. Historical certificates and logs remain in the authors' original repository.

## Citation

See [CITATION.bib](CITATION.bib). This repository is a software source release; it is not a substitute for the forthcoming mathematical paper.

## Release status and license

The frozen public source baseline is commit `933ab9a859aaa54a26246a4aeac1d92972c20c2d`. Check its 485 source/configuration inputs from the repository root:

```sh
python3 scripts/check-source-integrity.py
```

The original repository code is licensed under [Apache-2.0](LICENSE). Existing third-party source notices and dependency licenses remain in force; see [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).

Both components of the separate compatibility candidate passed full Palomar preflight at [`587bf340cfd5fcf808d37105532d470dd3552b3b`](https://github.com/matthewrosenzweigwork-max/DGR-Singular-LSI-Lean-Public/tree/587bf340cfd5fcf808d37105532d470dd3552b3b). See the [preserved reports, exact pins and build commands](docs/palomar/FULL_PREFLIGHT_EVIDENCE.md). No intake, registration, or main update has been performed.

The [release inventory and staged plan](docs/RELEASE_PREPARATION.md) describe this frozen baseline branch. Its historical metadata draft is retained as a reference; the verified candidate contains the active metadata, Challenge/Solution pairs, compatibility ledger and review records.
