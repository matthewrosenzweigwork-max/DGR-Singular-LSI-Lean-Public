# Compatibility candidate status

This branch is an unbuilt compatibility candidate. Its frozen `main` and `release-preparation-2026-10-16` branches remain separately reproducible. No manuscript claim, original theorem text, proof body, hypothesis, or axiom has been rewritten by this first migration pass.

The target is the lowest version currently accepted by Palomar: Lean v4.35.0-rc2, with canonical Mathlib release commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`. The new dependency lock is assembled from that exact Mathlib revision's manifest, retaining the package's own Mathlib entry. Lake has not yet revalidated this candidate lock. API incompatibilities may still require explicit repairs.

The module transformation inserts `module`, changes the existing header imports to `public import`, and inserts `@[expose] public section` after them. The 18 existing module files in the planar baseline are preserved. This preserves source text and intended cross-module visibility, but does not establish type correctness under the new compiler.

`MIGRATION_LEDGER.json` records each changed original input's before/after SHA256. Run `python3 scripts/check_migration.py` for the current candidate. The original integrity checker remains unchanged and intentionally rejects the changed migration inputs; run it on the frozen baseline or preparation branch. No frozen manifest has been rewritten to imply these are the accepted old bytes.

The tiny module/import/exposed-definition syntax smoke passed with the already-installed Lean v4.35.0-rc3. This is a syntax aid only, not an rc2 test or a project build. The candidate's actual rc2 build must run on Linux CI.

## Compute route

The least disruptive build route is GitHub-hosted `ubuntu-24.04`, already used for the original joint repository's cold verification. `migration-build.yml` has independent jobs for the independent projects, two Lean runtime threads per job, a 120-minute job timeout, fresh project objects, and retained logs. It does not represent a Palomar pass or an independent correspondence audit. It starts only on a push to this migration branch or manual dispatch.

The Mac has 24 GiB RAM, 10 logical CPUs, and only about 11 GiB free disk; no project compilation or cache retrieval was attempted there. The connected x86_64 Linux workstation has 31 GiB physical RAM and ample disk, but it contains the active Coulomb migration campaign at `/home/mrosenz2/projects/coulomb-migration`; no new job, clone, or write was made in that workspace. Historical DGRHS AWS scripts belong to a different campaign and are not a route for this release. The historical planar aarch64 direct-verification authority expired on 12 October and is not reused.

The exact inspected Palomar workflow commit is `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`. Its hosted profile is defined in `verification-profile.json`, separately from the Namespace catalogue. `palomar-standard-v1` uses `ubuntu-24.04`, requires at least 14 GiB effective RAM and 20 GiB free workspace, and has a 350-minute job limit / 19,800-second execution budget. `full-preflight.yml.draft` pins the workflow and pipeline input to that same SHA. It remains inert because the compact Challenge is unresolved.

## Challenge reuse and remaining work

The original repository at `664d3fdb102267d3e7440fd4889dc2fe1a354855` contains source certificates, type/axiom inventories, and portable cold-verification scripts, but no files named Challenge, Solution, or Comparator. Its verification workflow can guide the source build; it cannot replace the registry's required small statement surface.

The draft Comparator selections keep all three periodic endpoint families (`UniformFullGradientInequalities`, `ModulatedFullGradientInequalities`, and `ExternalPotentialFullGradientInequalities`) and the whole-space bounded-Hessian/positive-cutoff/zero-cutoff endpoints. The two components need separate project paths and configurations because both use `Tablet`. The whole-space selection is Poincaré only. The Challenge must reconstruct `BoundedBackground`, canonical/Riesz laws, gradient closures and entropy on the periodic side, and reference/Gibbs laws, potential classes, multiplier classes, and closed physical energy on the whole-space side, with exact accepted definitions and hypotheses.

The Comparator JSON drafts pass static shape checks but have no Challenge/Solution files and are not submission configurations. A formalization metadata draft, root Apache-2.0 license, and third-party notices are present; remaining source/automation fields must be supported by the original records. After the new build passes, construct and independently check the compact statement surface, complete metadata, run the exact-commit full reusable workflow, and review its real report. No intake, registration, tag/gist authorization flow, credential creation, main update, or unrelated-campaign change is authorized by these files.
