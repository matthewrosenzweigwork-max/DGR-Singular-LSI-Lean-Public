# Whole-space Challenge design

## Scope and construction

`trials/whole-space/project/Challenge.lean` is a self-contained statement surface
for the whole-space **Poincare** results. It contains 296 physical lines and
18,323 UTF-8 bytes. It imports canonical Lean and Mathlib modules, including the
multivariate standard Gaussian law, and has no project-specific import.

The three configured theorem targets retain their full accepted statements:

- `BoundedHessianAllCutoffsClosedPI`: a positive common constant for two-sided
  Hessian bounds, bounded multipliers, all particle counts at least two,
  coupling in `[0, B]`, and every nonnegative cutoff.
- `GrowthClassPositiveCutoffClosedPI`: all three conjunction clauses: a constant
  uniform over a fixed growth class, the fixed-potential formulation, and the
  standard Gaussian formulation, with positive cutoff.
- `GrowthClassZeroCutoffClosedPI`: the same three clauses with cutoff equal to
  zero.

All three retain `d >= 3`, `0 < s <= d - 2`, the exact order of quantifiers and
constant dependencies, and the original closed-gradient energy and variance.
There is no whole-space LSI claim and no replacement conditional theorem.

## Fixed mathematical objects

The statement dependency closure contributes the following 26 definitions and
structures, copied verbatim from the module-interface migration of accepted
snapshot `933ab9a859aaa54a26246a4aeac1d92972c20c2d` (only Tablet node markers and
per-file import/interface wrappers were removed):

- `OneParticle`
- `ParticleConfig`
- `ReferencePartition`
- `ReferenceLaw`
- `ConfigurationReference`
- `RieszKernel`
- `ParticlePosition`
- `PairInteraction`
- `CollisionSet`
- `InteractionWeight`
- `GibbsPartition`
- `GibbsLaw`
- `LawVariance`
- `EuclideanGradient`
- `PhysicalEnergy`
- `SmoothGradientCore`
- `ClosedGradientGraph`
- `ClosedPhysicalEnergy`
- `BoundedMultiplier`
- `EuclideanHessian`
- `EuclideanLaplacian`
- `PotentialBounds`
- `TwoSidedPotential`
- `ForceExponent`
- `ShiftedReference`
- `GrowthClassPotential`

In particular, the singular kernel and collision convention, reference
normalization, Gibbs product configuration law, closure of the compact smooth
gradient core in the product of L2 spaces, squared L2 gradient energy, Hessian
bounds, bounded multiplier ratio, centered local bounds, and all-parameter
growth condition are fixed definitions rather than comparator holes.

## Solution and comparator

`Solution.lean` imports `Tablet.BoundedHessianAllCutoffsClosedPI`, which publicly
exports the three original proofs and their original global declarations. It
does not import `Challenge`. The two modules are separate environments with
identically named fixed declarations and theorem types. This avoids changing
any accepted proof or transporting between newly invented structures.

`comparator.json` names all three theorem holes and no definition holes. Its
permitted axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`.
Only the Challenge has `sorry`, one on each configured theorem; the Solution
contains no newly introduced proof hole or axiom. Mechanical comparison must
confirm equality of the complete declaration closure, and the full registry
pipeline must check the Solution's actual transitive axioms and kernels.

## Checks and next build step

A local static check passed: every fixed declaration text and every complete
theorem statement occurs exactly as extracted from its accepted Tablet source;
all three holes are configured; every direct Challenge import is Mathlib; file
size is below both preferred limits (300 lines / 32 KiB); Solution has no new
hole. These are source checks, not compilation or verification receipts.

No Lean compilation or full Palomar workflow was run for this subtask. Parent
CI must add/build the `Challenge` and `Solution` roots explicitly in the Lake
configuration, compile with the pinned `v4.35.0-rc2` / Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55` pair, and execute the full comparator
workflow against an exact commit. The copy construction makes no mathematical
migration claim until those checks pass.

## Mathematical documentation

Every one of the 26 fixed definitions/structures now has a mathematical
docstring. These explain the potential/multiplier classes, normalizing
constants and measures, singular collision convention, derivatives, and
closed-gradient graph and energy. Declaration bodies and theorem statements
are unchanged. The documented Challenge remains within the preferred
300-line / 32 KiB limits (296 lines / 18,323 bytes).

Two canonical Lean meta imports support explicit auxiliary-proof cache boundaries before the copied definitions. Only the nonlogical auxiliary-lemma memoization table is cleared; logical constants and kernel options are retained. This reproduces the original per-module auxiliary names without changing mathematical formulas or statements. See `WHOLE_SPACE_COMPARATOR_REPAIRS.md`; the exact-commit full report remains required.
