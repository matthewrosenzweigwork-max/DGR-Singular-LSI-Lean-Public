# Singular Riesz functional inequalities in Lean

Matias Delgadino, Rishabh Gvalani, and Matthew Rosenzweig.

This repository contains the Lean proof sources for periodic logarithmic Sobolev and Poincaré inequalities and whole-space Riesz Poincaré inequalities. Precise assumptions and conclusions are given by the declarations linked below. The whole-space component does not claim a whole-space logarithmic Sobolev inequality.

## Proof sources

- [Periodic library](trials/periodic/project/Tablet.lean): 312 proof modules, including the uniform, modulated, and external-potential full-gradient inequalities.
- [Whole-space library](trials/whole-space/project/Tablet.lean): 154 proof modules, including bounded-Hessian and growth-class closed Poincaré inequalities.
- [Periodic application checks](trials/periodic/applications/) and [whole-space application checks](trials/whole-space/applications/) provide concrete specialization and statement checks.

All 466 proof modules are dependencies of their respective library entrypoint. The proof files, application files, toolchain declarations, and dependency manifests are unchanged from the source snapshot. Historical duplicate trees, archived ZIP files, and operational logs are omitted.

## Build

Install elan from its official distribution. In either `trials/periodic/project` or `trials/whole-space/project`, run:

```sh
lake exe cache get
lake build
```

Both projects pin Lean 4.33.0 and Mathlib commit `db584cd6d46c92f209a44c0f1c829460d327499d`. The exact transitive dependency revisions are in each `lake-manifest.json`.

To run a Lean kernel replay after building, use `lake env leanchecker Tablet.ModuleName`, replacing `ModuleName` with the module being checked. Application checks are supplied separately and may require adding their containing directory to the Lean search path.

## Provenance and verification

`SOURCE_MANIFEST.json` records the SHA-256 and original Git blob identity of every copied input. Run `python3 scripts/check-source-integrity.py` to check those bytes.

The source snapshot had successful source builds, kernel replays, and type/axiom checks in its original verification campaign; its GitHub verification run on 14 October 2026 also passed. This clean mirror preserves the checked proof bytes. Publication of this mirror is not a new independent kernel-verification run. Standard logical axioms permitted by the source projects are `propext`, `Classical.choice`, and `Quot.sound`.

The upstream snapshot is commit `664d3fdb102267d3e7440fd4889dc2fe1a354855`. No upstream runtime Git history is imported. Historical certificates and logs remain in the authors' original repository.

## Citation

See [CITATION.bib](CITATION.bib). This repository is a software source release; it is not a substitute for the forthcoming mathematical paper.

No new license is assigned by this publication. Third-party dependencies retain their respective licenses.
