# Periodic compatibility repairs

## `IndependentVarianceMGF`: nonnegative product monotonicity

The Linux source-build run [38927874907, job117063976644](https://github.com/matthewrosenzweigwork-max/DGR-Singular-LSI-Lean-Public/actions/runs/38927874907/job/117063976644)
reported an application error at `Tablet/IndependentVarianceMGF.lean:93`.

At pinned Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`, the
ordered-monoid lemma named `Finset.prod_le_prod` takes only a pointwise comparison
and requires multiplication to preserve order for arbitrary factors. The
nonnegative-factor version applicable to real products is now named
`Finset.prod_le_prod₀`; it takes the two existing hypotheses, nonnegativity of
each left factor and its comparison with the corresponding right factor.

The repair changes only that lemma name (adds the subscript zero). It retains
the original proofs of nonnegativity of the exponential integrals and of their
individual MGF bounds, with the same product and resulting estimate. No theorem
statement, definition, analytic assumption, or mathematical argument changes.

The exact pinned source signatures were inspected in:

- [Ordered-monoid product lemma](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean#L99)
- [Nonnegative-factor product lemma](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean#L36)

Static inspection confirms a single lemma-identifier replacement in this source
module. Compilation remains to be checked by the next Linux CI run; no Mac
build was performed.

## Follow-up scan: the same nonnegative product API

A scan restricted to `trials/periodic/project/Tablet` found seven additional
applications with the same two existing premises: nonnegative left factors and
pointwise comparison. Only the lemma identifier was changed to
`Finset.prod_le_prod₀`, using the exact pinned signature linked above:

| Module | Applications | Existing factor nonnegativity |
| --- | ---: | --- |
| `CenteredProductMean` | 2 | Nonnegative background density |
| `ProductBackgroundFacts` | 2 | Positive lower bound / background density |
| `FiniteRademacherEvenMoment` | 1 | Positive real hyperbolic cosine |
| `TorusSmoothFourierSummable` | 1 | `1 + kᵢ²` via `positivity` |
| `PairMomentBounds` | 1 | Nonnegative background density |

The `apply` form in `TorusSmoothFourierSummable` continues to supply the first
nonnegativity premise explicitly and proves the second pointwise comparison in
the following unchanged tactic block. All theorem signatures and all other
proof text remain unchanged. No old `Finset.prod_le_prod` application remains in
the periodic Tablet sources.

## Remove unused inner-product scope

`JumpL2Construction` used `open scoped InnerProduct`, which is no longer a valid
scope. Every inner product in the module is already written explicitly as
`inner ℝ ...`; there is no angle-bracket notation. The unused scope command was
removed. Existing valid `InnerProductSpace` scopes in other modules were retained.

## Scan for old `MemLp` pair constructors/projections

The pinned [MemLp definition](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Function/LpSeminorm/Defs.lean#L133)
identifies `MemLp f p μ` with `eLpNorm f p μ < ∞`; measurability is recovered by
`MemLp.aestronglyMeasurable`. Static scans of explicitly typed `MemLp` hypotheses,
their `.1`/`.2` uses, constructors, and `eLpNorm` sites found no unambiguous old
pair constructor/projection requiring another change in periodic Tablet. In
particular, `hLpε.1` and `hLpε.2` in `RieszCoulombTranslatedFormBound` project a
genuine conjunction of `MemLp` with an integral estimate and must be retained.
No speculative MemLp edits were made. CI remains responsible for detecting
uses hidden behind inferred local types and subsequent elaboration errors.
