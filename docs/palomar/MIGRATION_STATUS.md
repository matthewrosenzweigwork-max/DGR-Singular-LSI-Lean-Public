# Compatibility candidate status

This branch is a compatibility candidate pending full exact-commit verification. Its frozen `main` and `release-preparation-2026-10-16` branches remain separately reproducible. The first module-interface pass preserved original theorem/proof text. Subsequent minimal API repairs are documented in the component COMPATIBILITY_REPAIRS.md records and hash ledger. Original theorem statements, mathematical definitions, hypotheses and permitted axioms are retained.

The target is the lowest version currently accepted by Palomar: Lean v4.35.0-rc2, with canonical Mathlib release commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`. The new dependency lock is assembled from that exact Mathlib revision's manifest, retaining the package's own Mathlib entry. Lake has not yet revalidated this candidate lock. API incompatibilities may still require explicit repairs.

The module transformation inserts `module`, changes the existing header imports to `public import`, and inserts `@[expose] public section` after them. The 18 existing module files in the planar baseline are preserved. This preserves source text and intended cross-module visibility, but does not establish type correctness under the new compiler.

`MIGRATION_LEDGER.json` records each changed original input's before/after SHA256. Run `python3 scripts/check_migration.py` for the current candidate. The original integrity checker remains unchanged and intentionally rejects the changed migration inputs; run it on the frozen baseline or preparation branch. No frozen manifest has been rewritten to imply these are the accepted old bytes.

The tiny module/import/exposed-definition syntax smoke passed with the already-installed Lean v4.35.0-rc3. This is a syntax aid only, not an rc2 test or a project build. The candidate's actual rc2 build must run on Linux CI.

## Compute route

The least disruptive build route is GitHub-hosted `ubuntu-24.04`, already used for the original joint repository's cold verification. `migration-build.yml` has independent jobs for the independent projects, two Lean runtime threads per job, a 120-minute job timeout, fresh project objects, and retained logs. It does not represent a Palomar pass or an independent correspondence audit. It starts only on a push to this migration branch or manual dispatch.

Project compilation and dependency-cache retrieval run on GitHub-hosted Linux. The Mac is used for source review, normal Git, and lightweight validation; unrelated active verification campaigns remain untouched.

The exact inspected Palomar workflow commit is `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`. Its hosted profile is defined in `verification-profile.json`, separately from the Namespace catalogue. `palomar-standard-v1` uses `ubuntu-24.04`, requires at least 14 GiB effective RAM and 20 GiB free workspace, and has a 350-minute job limit / 19,800-second execution budget. `full-preflight.yml.draft` pins the workflow and pipeline input to that same SHA. The draft is retained as a reference; the active palomar-full.yml workflow now uses the same exact pin and full mode, with the current source commit. No intake or registration is performed.

## Challenge reuse and remaining work

The original repository at `664d3fdb102267d3e7440fd4889dc2fe1a354855` contains source certificates, type/axiom inventories, and portable cold-verification scripts, but no files named Challenge, Solution, or Comparator. Its verification workflow can guide the source build; it cannot replace the registry's required small statement surface.

The draft Comparator selections keep all three periodic endpoint families (`UniformFullGradientInequalities`, `ModulatedFullGradientInequalities`, and `ExternalPotentialFullGradientInequalities`) and the whole-space bounded-Hessian/positive-cutoff/zero-cutoff endpoints. The two components need separate project paths and configurations because both use `Tablet`. The whole-space selection is Poincaré only. The Challenge must reconstruct `BoundedBackground`, canonical/Riesz laws, gradient closures and entropy on the periodic side, and reference/Gibbs laws, potential classes, multiplier classes, and closed physical energy on the whole-space side, with exact accepted definitions and hypotheses.

The compact Challenge/Solution pairs and real comparator.json configurations are now present, with source/design records and exact statement selections. Each component has formalization.yaml, including source provenance, human responsibility, Apache-2.0 and candid automation/review disclosures. The pinned local metadata/config validators and static all-source module/line check pass. Current-source kernel/Comparator verification remains governed by the exact-commit full workflow reports. No intake, registration, tag/gist authorization flow, credential creation, main update, or unrelated-campaign change is authorized by these files.
