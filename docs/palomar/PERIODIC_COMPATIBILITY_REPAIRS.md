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

`JumpL2Construction` writes all inner products explicitly as `inner ℝ ...`.
The `open scoped InnerProduct` command was removed, and its three adjoint dagger
uses were replaced by explicit `ContinuousLinearMap.adjoint` applications. The
[pinned adjoint source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/InnerProductSpace/Adjoint.lean#L104)
defines the dagger as exactly that function, so the operators are unchanged.
Existing `InnerProductSpace` scopes in other modules were retained.

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

## Coordinate-map measurability after the Pi API change

The pinned [MeasurableSpace constructions](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean#L533)
provide `Measurable.of_eval` with a single family of coordinate-measurability
proofs. The deprecated `measurable_pi_lambda` alias has the same signature; its
old additional explicit function argument is no longer accepted.

All 31 old explicit-function applications in the periodic Tablet tree were
changed from `measurable_pi_lambda _ ...` to `Measurable.of_eval ...`, preserving
the supplied coordinate proofs. Modules: `SplitCoordinateEquivalence` (2),
`CenteredEnergyProbabilityControls` (2), `ProductDeletionConditionalEntropy` (4),
`CenteredInteractionEntropyLower` (2), `ProductConditionalEntropyTensorization`
(2), `FiniteProductEntropyShearer` (10), `CenteredCanonicalEntropyLower` (2),
`SplitStationarityTransfer` (1), `ProductDisjointBlockLaw` (2),
`DisjointBlockMarginalEntropy` (2), and `HeatCenteredEnergyAveraging` (2).
(The total is 31 applications.) The equivalence's forward/inverse functions and
all other defined objects are unchanged; only their measurability certificates
use the supported invocation. Existing `apply measurable_pi_lambda` uses already
have the correct arity and were retained.

## Norm comparison measurability and exponent API

The pinned [LpSeminorm basic lemmas](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean#L408)
require explicit measurability certificates for both functions in
`eLpNorm_congr_norm_ae`. `MayerConvolutionBounds` and its counterpart
`PositiveFourierConvolution` now provide the existing Lp measurability proofs
before the unchanged pointwise real/complex norm equality. They also provide
explicit existing measurability to `eLpNorm_one_eq_lintegral_enorm` and
`eLpNorm_le_of_ae_bound`, the latter obtained from the already-established
convolution MemLp fact.

The pinned [exponent comparison](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean#L106)
now covers nonmeasurable functions through the totalized norm and accepts only
the exponent inequality. Its obsolete extra measurability argument was removed
in those two modules and in `RieszCoulombTranslatedFormBound`. No assumption is
removed from a theorem statement: each is an invocation of the new library
lemma, in a proof whose functions already have the required measurability.

These edits address diagnostics from full preflight commit
`7c214cc881fd32d92f56750dda8251946f6734b1`. Its bounded log omitted the locations
and goals for the `RieszZeroCutoffSmooth` failures. No speculative edits to that
module were made. Full source-build diagnostics and subsequent CI are required.

## Confirmed diagnostic build at `ced0f99`: map probability

[Diagnostic run 38931158085, job 117075181181](https://github.com/matthewrosenzweigwork-max/DGR-Singular-LSI-Lean-Public/actions/runs/38931158085/job/117075181181)
confirmed that `Measure.isProbabilityMeasure_map` has been removed. The seven
periodic calls now use `(Measure.isProbabilityMeasure_map_iff hmeas).mpr
inferInstance`, retaining each site's original almost-everywhere measurability
proof and existing source probability-measure instance. Sites: two in
`RieszCenteredSquareEntropyLower`, and one each in
`ProductDeletionConditionalEntropy`, `CenteredInteractionEntropyLower`,
`FiniteProductEntropyShearer`, `SplitConditionalSquareEntropyIdentity`, and
`SplitStationarityTransfer`. The supported lemma is in the pinned
[Probability source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean#L124).
No theorem hypothesis or resulting measure changes.

## Bounded elaboration budget for `RieszZeroCutoffSmooth`

The same diagnostic job reported a deterministic `whnf` timeout at the default
200,000-heartbeat budget for `RieszZeroCutoffSmooth`. The theorem now has
`set_option maxHeartbeats 800000 in` immediately before its declaration, applying
only to this one existing proof. The proof text, statement, definitions, and
assumptions are unchanged. This is a finite, fourfold elaboration budget increase;
no global or unlimited resource option is introduced.

## Convert goal handling in `RieszCenteredFourierTailOperator`

The diagnostic job showed that `convert hs using 1` now leaves only the algebraic
equality between `M * σ * ‖f‖ * ‖g‖` and
`M * (σ / C) * ‖f‖ * ‖g‖ * C`. The old first `rfl` bullet therefore targeted the
non-reflexive algebraic goal, and the next bullet had no goal. The repair applies
the original `field_simp [hC.ne']` and `ring` steps uniformly after `convert`,
without positional bullets. The existing `hC : 0 < C` supplies exactly the
nonzero denominator fact used by the original argument. No estimate, assumption,
or mathematical construction changes.

All repairs in this batch are based on the complete diagnostic log. No Mac
build was performed; hosted compilation and Palomar verification remain pending.
