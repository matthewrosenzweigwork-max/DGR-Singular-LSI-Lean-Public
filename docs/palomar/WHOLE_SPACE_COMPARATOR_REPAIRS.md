# Whole-space comparator investigation

## Report and mathematical reconstruction

Full preflight `38942746877`, source
`4d4fa1c85acbf45bac1d7a9a8a9483b0a3fad88d`, built the Solution but stopped
in the comparator with:

```text
Const does not match between challenge and target 'ClosedPhysicalEnergy'
```

`ClosedPhysicalEnergy` means the squared L² norm of the gradient component
of a pair in scalar/vector-valued L² spaces. On the closed gradient graph,
this is the closed Dirichlet energy. Both environments use this exact
source declaration:

```lean
noncomputable def ClosedPhysicalEnergy {d N : ℕ}
    {P : MeasureTheory.Measure (ParticleConfig d N)}
    (q : MeasureTheory.Lp ℝ 2 P × MeasureTheory.Lp (ParticleConfig d N) 2 P) : ℝ :=
  ‖q.2‖ ^ 2
```

`Solution` imports the original endpoint and its fixed definitions; it does
not import the Challenge. No alternate energy definition, extra axiom or
definition hole was introduced.

## Whole fixed-surface source audit

After removing Challenge docstrings and the original per-file node/body
markers, every one of the following 26 declaration texts occurs verbatim
in the Challenge. This checks binder spellings, explicit versus implicit
binders, definitions versus abbreviations, structure fields/extensions, and
source bodies. It does **not** establish equality of elaborated constants.

- `OneParticle`: exact declaration source match
- `ParticleConfig`: exact declaration source match
- `ReferencePartition`: exact declaration source match
- `ReferenceLaw`: exact declaration source match
- `ConfigurationReference`: exact declaration source match
- `RieszKernel`: exact declaration source match
- `ParticlePosition`: exact declaration source match
- `PairInteraction`: exact declaration source match
- `CollisionSet`: exact declaration source match
- `InteractionWeight`: exact declaration source match
- `GibbsPartition`: exact declaration source match
- `GibbsLaw`: exact declaration source match
- `LawVariance`: exact declaration source match
- `EuclideanGradient`: exact declaration source match
- `PhysicalEnergy`: exact declaration source match
- `SmoothGradientCore`: exact declaration source match
- `ClosedGradientGraph`: exact declaration source match
- `ClosedPhysicalEnergy`: exact declaration source match
- `BoundedMultiplier`: exact declaration source match
- `EuclideanHessian`: exact declaration source match
- `EuclideanLaplacian`: exact declaration source match
- `PotentialBounds`: exact declaration source match
- `TwoSidedPotential`: exact declaration source match
- `ForceExponent`: exact declaration source match
- `ShiftedReference`: exact declaration source match
- `GrowthClassPotential`: exact declaration source match

The three complete endpoint statement texts also retain their accepted
mathematical scope, including all conjunction clauses of the two growth
endpoints. No source-level alias or binder discrepancy was found.

## Why compiler success does not settle this error

At pinned Lean `v4.35.0-rc2`,
[Lake/Check/Compare.lean](https://github.com/leanprover/lean4/blob/v4.35.0-rc2/src/lake/Lake/Check/Compare.lean)
compares ordinary dependencies using raw `ConstantInfo` equality. This
checks elaborated values and metadata, not just definitional equivalence.
The monolithic Challenge and separately compiled original modules have
different surrounding imports/scopes; instance selection or declaration
metadata must therefore be inspected in the elaborated output before a
mathematics-preserving correspondence fix can be identified. These are
possible causes, not established findings.

The saved report identifies the first differing constant but does not
include either complete elaborated declaration. The next diagnostic should
compare all 26 elaborated types, values, universe parameters, safety and
reducibility information in both environments at once, then rerun the
actual comparator closure. This avoids guessing an energy replacement or
cycling one constant at a time.

No Challenge/Solution declaration has been changed in this investigation
stage. No build, commit, configuration, ledger or workflow edit was
performed.

## Diagnostic script and smoke validation

Added `scripts/compare_whole_space_constants.lean`. Run it after both
whole-space modules are built, from `trials/whole-space/project`:

```sh
lake env lean --run ../../../scripts/compare_whole_space_constants.lean
```

The script uses `Lean.importModules` twice to obtain **separate**
environments, never an environment containing both conflicting surfaces.
It inspects all 26 fixed roots and the three configured theorem statements,
then enumerates all constants attributed to the Challenge module, including
generated structure fields, constructors, recursors, instances and helpers.
Ordinary declarations use raw `ConstantInfo` equality. The three named
theorems use kind/`ConstantVal` comparison so their intentionally different
proofs are not treated as mismatches.

Output is JSON Lines. For each differing constant, each differing field is
printed with both values: raw expression representations for type/value,
universe parameter names, reducibility kind/height, safety, mutual-block
`all` lists, and all kind-specific inductive/constructor/recursor fields.
Missing declarations are reported separately. An unexpected raw mismatch
with equal serialized fields triggers a complete field dump. A summary
reports counts. This diagnostic does not declare comparator acceptance; a
successful run exits zero even when it finds mismatches.

A tiny Lean-only smoke using installed Lean `v4.35.0-rc3` passed. It compiled
two minimal modules in `/tmp/palomar-whole-constant-smoke`, loaded them into
separate environments and compared 44 named/generated constants. It
confirmed equality of a generated structure field and detected an
intentional `ClosedPhysicalEnergy` value difference (`1` versus `2`) in
the `value` field. Its expected missing-root messages reflect that tiny
fixture's subset of names. The script's `main` is public and executable
with `lean --run`. No project compilation, Mathlib cache or source build
was performed locally. The hosted run must still test it under pinned rc2
and inspect the actual declarations.
