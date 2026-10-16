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

## Confirmed cause and cache-boundary repair

The hosted diagnostic at source `392b80e` succeeded. Its hash-verified output
`migration-reference-evidence/whole-constant-inspection-392b80e/constants.jsonl`
checks 69 declarations: 60 equal and nine different or missing. All actual
root-value differences are references to compiler-generated proof auxiliaries,
not different formulas, instances, universes or mathematical hypotheses.

The seven differing fixed roots are `ClosedGradientGraph`,
`ClosedPhysicalEnergy`, `ForceExponent`, `ParticlePosition`, `ReferenceLaw`,
`RieszKernel`, and `SmoothGradientCore`. The two additional differences concern
the numbering/types of `SmoothGradientCore._proof_2` and `_proof_3`; reuse
also suppresses an auxiliary generated in the separate-module build.
For example, the compact Challenge's energy references auxiliary proofs
created earlier by `SmoothGradientCore` and `ConfigurationReference`, while
the original separately compiled energy references its own `_proof_1`,
`_proof_2`, and `_proof_3`.

Pinned Lean's
[AuxLemma.lean](https://github.com/leanprover/lean4/blob/v4.35.0-rc2/src/Lean/Meta/Tactic/AuxLemma.lean)
registers `auxLemmasExt` as a local cache. Its `mkAuxLemma` uses the proof
type as a cache key. The source explicitly states that this cache is not
persisted in `.olean` files. Thus each original single-node module begins
with a fresh cache, but simply concatenating the definitions allows an
earlier declaration's proof auxiliary to be reused. Lake's strict raw
constant comparison observes those different proof references.

### Selected transparent administrative fix

Added these two canonical Lean imports to the Challenge:

```lean
public meta import Lean.Meta.Tactic.AuxLemma
public meta import Lean.Elab.Command
```

Immediately before each of the 26 copied original declarations, added the
following readable command recreating the original source-module boundary:

```lean
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
```

This command changes only the auxiliary-proof **cache**. It never alters
the logical constant map, declarations, kernel options, mathematical
instances or axioms. It does not disable checking, weaken any definition,
introduce an extra comparator hole, or import project source. An explanatory
comment is included directly in the Challenge. The parent inspected current
Palomar policy and verifier source: canonical Lean imports remain allowed,
and neither source imposes a ban on this transparent cache-only command.
Registry trust and verification outcomes still require the hosted rerun.

An ordinary `section ... end` boundary was tested and does not clear this
cache. No standard cache-reset option was found in the inspected definition
abstraction path. Using explicit named auxiliary proof reconstructions
would require expanding and maintaining implementation-specific instance
arguments; recreating the original cache boundary preserves the copied
mathematical declarations verbatim instead.

### Tiny Lean-only reproduction

Using installed Lean `v4.35.0-rc3`, compiled minimal exposed modules in
`/tmp/palomar-aux-cache-smoke`. The first module defines:

```lean
def ReferencePartition : Fin (1+1) := ⟨1, by decide⟩
```

A second module imports it and defines:

```lean
def ClosedPhysicalEnergy : Fin (1+1) := ⟨1, by decide⟩
```

A merged module containing the same two declarations, even with a section
around the second, reuses `ReferencePartition._proof_1`; raw comparison of
`ClosedPhysicalEnergy` fails. A merged module with the cache-only command
before both declarations creates `ClosedPhysicalEnergy._proof_1` separately.
The diagnostic confirms exact equality of both root `ConstantInfo` values
and both generated proof auxiliaries with the separate-module target.
All fixture compilation and diagnostic commands exited zero after using
the module system's required `public meta import` form for both Lean
implementation imports. No project compilation or Mathlib cache ran locally.

### Exact source preservation and pending verification

The patch changes only those two imports, an explanatory comment, and the
26 cache commands (which replace blank lines). Removing exactly these
administrative additions reproduces the previous Challenge byte for byte.
All 26 mathematical definition/structure texts, all three complete endpoint
statements, existing docstrings and comparator holes are therefore unchanged.
The final Challenge is **296 physical lines / 18,323 UTF-8 bytes**, remaining
inside both preferred limits. Solution and original project proofs are
untouched. No configuration, workflow, ledger, commit or push was made by
this subtask.

| Challenge SHA-256 before | Challenge SHA-256 after |
|---|---|
| `cb1ab8d40e77e43b51c471d5d78bd5726ebcbfea52d5c142cfed81f4442ffd23` | `7050ed2b11b1b80830e338c97bb5d0fb326a4c38df82842168cd905ad877da75` |

Hosted all-constant diagnostics and full exact-commit comparator/kernel
verification remain necessary; the tiny fixture proves the mechanism but
is not a whole-space verification receipt.
