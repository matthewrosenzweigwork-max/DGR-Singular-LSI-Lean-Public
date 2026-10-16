# Whole-space compatibility repairs

These targeted changes address the first whole-space Linux CI errors after the
module/toolchain migration. They preserve theorem statements, hypotheses,
conclusions, physical definitions, and proof strategy. No local Lean build was
run; parent Linux CI must validate them.

## ReferenceKernelSchur.lean

Removed this unused line:

```lean
open scoped InnerProduct
```

At pinned Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`,
[InnerProductSpace/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/InnerProductSpace/Defs.lean)
defines the `InnerProductSpace`, `RealInnerProductSpace`, and
`ComplexInnerProductSpace` notation scopes. The old `InnerProduct` opening is
invalid. This file writes every inner product explicitly as `inner ℝ ...`, so
it requires no scoped inner-product notation at all. No statement or proof
expression changed.

## CriticalNormControls.lean

Before:

```lean
have hmem : MemLp ψ p μ := ⟨hψ, hcap.trans_lt hT⟩
```

After:

```lean
have hmem : MemLp ψ p μ := hcap.trans_lt hT
```

At the pinned version,
[LpSeminorm/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Function/LpSeminorm/Defs.lean)
defines `MemLp f p μ` directly as `eLpNorm f p μ < ∞`, rather than a pair of
strong measurability and finiteness. The existing bounds already prove that
inequality. The theorem's measurability hypothesis remains intact and is used
by subsequent steps.

The same pinned source adds an explicit measurability argument to the norm
power identity. Supplied the existing hypothesis explicitly:

```lean
-- Before
rw [eLpNorm_nnreal_pow_eq_lintegral hp0] at H
-- After
rw [eLpNorm_nnreal_pow_eq_lintegral hp0 hψ] at H
```

This avoids a subsequent unresolved argument; it changes no bound or exponent.

## Challenge layout

Moved the existing whole-space Challenge comment below every import command.
It remains 245 physical lines / 12,445 UTF-8 bytes. All declarations and all
three complete theorem statements are unchanged.

## Static validation

Exact theorem-header comparisons against the current committed migration
sources passed for both repaired files. No new axiom, proof hole, hypothesis,
definition, or mathematical assertion was introduced. No ledger, script,
configuration, manifest, workflow, license, or metadata was edited in this
repair subtask. No commit or push was performed.

SHA-256 values before and after these repairs:

| File | Before | After |
|---|---|---|
| `trials/whole-space/project/Tablet/ReferenceKernelSchur.lean` | `ba25d11deebca2dec9035b2ce0f6b365a9c9c71fe9beacecb09a430c2b74d4af` | `00ceeedc67ffb13b526eb9268a16feba8a6fd097ecdea8d9676ad556672a9c6d` |
| `trials/whole-space/project/Tablet/CriticalNormControls.lean` | `7935a2523817126360b000f65f13d631ff6faf08a0a619f6a8fa9a2bcf06dffb` | `69c4d7dd51e76bbd97c162e4ea7e42d859c7a9d0c3412d80649711b715bedb78` |

## Proactive follow-up scan

Scanned only `trials/whole-space/project/Tablet` for old MemLp pair
constructors/projections and two-argument finite-product comparisons.
The following unambiguous source-level API repairs were applied.

### Finite products

Changed only the theorem name `Finset.prod_le_prod` to
`Finset.prod_le_prod₀` at both uses in each of:

- `FiniteGibbsProductBoundedTilt.lean`
- `FiniteGibbsCommonDensity.lean`
- `GibbsLocalDensityBounds.lean`

All six calls already provide precisely nonnegativity of the left factors
and pointwise comparison. The pinned
[GroupWithZero/Finset.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean)
defines that two-argument theorem as `prod_le_prod₀`; the unsuffixed name
now denotes the ordered-monoid one-argument comparison. Arguments, products,
and bounds were preserved in all six repairs.

### MemLp projections

In `NativeGibbsLargeNJumpGap.lean`, changed
`hf.1.aemeasurable` to `hf.aestronglyMeasurable.aemeasurable`.
In `NativeGibbsSameLabel.lean`, made the same replacement for the
MemLp proof `hX` obtained from the conditional slice theorem.

In `NativeGibbsJumpOperator.lean`:

| Before | After |
|---|---|
| `hf.2.ne` | `hf.ne` |
| `(hf.mono_measure hdom).1` | `(hf.mono_measure hdom).aestronglyMeasurable` |
| `eLpNorm_sub_le hs.2.1.1 hs.1.1 (by norm_num)` | `eLpNorm_sub_le (by norm_num)` |
| `hs.2.1.2.ne` (twice) | `hs.2.1.ne` |
| `hs.1.2.ne` (twice) | `hs.1.ne` |

Here `hs` is the unchanged threefold conjunction of endpoint MemLp facts;
only obsolete projections inside an individual MemLp fact were removed.
The triangle inequality change follows the pinned
[TriangleInequality.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Function/LpSeminorm/TriangleInequality.lean):
`eLpNorm_sub_le` now requires only the exponent condition. Its two function
arguments remain inferred from the same inequality. The map-measure identity
still takes measurability, supplied through the named MemLp method.

The other apparent projections examined were projections from Integrable,
explicit conjunctions or products, and were left unchanged. No ambiguous
MemLp/product call was changed. The scan is not a substitute for compilation.

For all six files, the entire text preceding the main theorem body marker
was checked unchanged against HEAD. Updated SHA-256 values:

| File | Before follow-up | After follow-up |
|---|---|---|
| `FiniteGibbsProductBoundedTilt.lean` | `3d4fb0bd6f43d966cb10df030442323244f0dd1e2ce7316f26d33b7e3d8dbd83` | `0b5a948ca8313859392c5ef349c663db5ad294a52dd925053ca8b189fc8a5abc` |
| `FiniteGibbsCommonDensity.lean` | `8d1b01b07e9e6291f3ae70eaad4cdbe8cbf9806f60fb795043741e4575e40acd` | `3ce2a88b94c1c094090e814bde8bf46db995111a79389eaa84e1212290b5cfa1` |
| `GibbsLocalDensityBounds.lean` | `cbe07bd8d837b642caa2dd763e889dcac15effbebbca4a9659cacbab85dc42c8` | `af6aef52f4f96a603312f37a5286e9a117adb8c76b89f29d269742d784dfffff` |
| `NativeGibbsLargeNJumpGap.lean` | `2fa322bff4a7e191fcc95a4aac04660fb2bfa9299cc713b98f63a9016636d6df` | `1d7a7e9d678e7e01293f8eca0e3db5ecdda541b497ea26fc339688d64f8d68c6` |
| `NativeGibbsSameLabel.lean` | `fa50aca8a1e8b007ce8e354240eb8e01a0e7827115ba5eec2e7563a477f21d72` | `4ebe1660bb512c826cfbabef06304c9c73d84d3431d57926eda728a34b4f4946` |
| `NativeGibbsJumpOperator.lean` | `59ad4818aaa00f36969d0cbef11ae902ccf86c67319b20a65cc01058d532b38c` | `40704a5117feec5e294bd3bc56770fb4a18454c17653e82be8f1b2a1121e42c9` |

The Challenge now has mathematical docstrings on every one of its 26 fixed
objects/structures. After removing only those comments, the 26 definition
texts and three complete theorem statements still match their source copies.
Its final size is 291 physical lines / 16,135 UTF-8 bytes. No local compilation,
commit, push, ledger or configuration change was performed.

## Full-preflight Solution-build repairs, run 38929137152

The full workflow at source `7c214cc` stopped in Solution compilation. The
saved report `migration-reference-evidence/whole-report-7c214cc.json` records
six failed targets in `diagnostics[0].explanation`; its build-log tail is
truncated to 20 KiB. All six have targeted repairs, with one additional use
of exactly the same norm-congruence API repaired in `WeakPotentialForm`.
These repairs are not a successful-build receipt; Linux CI must rerun.

### Norm congruence requires measurability

The pinned
[LpSeminorm/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean)
requires measurability of both functions before the norm equality argument
to `eLpNorm_congr_norm_ae`. In `EuclideanSobolev.lean`, the old call only
supplied the pointwise norm identity. It now also supplies the continuous
Fréchet derivative's measurability and the gradient's measurability.
The gradient continuity proof composes `hf.continuous_fderiv` with the
continuous inverse of the Riesz dual isometry, exactly as already used by
other project lemmas. `WeakPotentialForm.lean` has the same call in the
reverse direction; it receives the same two arguments in that order.
No additional assumption was added: both facts follow from the existing C¹
hypothesis. The norm equality and Sobolev constants are unchanged.

### Probability of image measures

At the pinned version,
[Typeclasses/Probability.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean)
provides an instance for the image of a probability measure and retains
`Measure.isProbabilityMeasure_map_iff` for measurable maps.

In `ConfigurationReferenceProbability.lean`, removed the call to the
nonexistent `Measure.isProbabilityMeasure_map`. The existing proof of
continuity/measurability of row flattening is preserved, and the final step is:

```lean
exact (MeasureTheory.Measure.isProbabilityMeasure_map_iff
  hflat.measurable.aemeasurable).mpr inferInstance
```

In `ConfigurationLawTranslation.lean`, replaced
`Measure.isProbabilityMeasure_map (oneShift a).measurable.aemeasurable`
by `inferInstance` for the already specified translated probability measure.
The translation map and its measurability arguments in the subsequent
product/map identities remain unchanged.

### Other reported compatibility failures

- `WeightedMeanJointL2.lean`: replaced `hw.2.2.1.1` by
  `hw.2.2.1.aestronglyMeasurable`. The outer conjunction still supplies
  the same MemLp fact, whose old first projection no longer exists.
- `SoftRieszReferencePositive.lean`: removed the unused invalid opening
  `open scoped InnerProduct`. No inner-product notation uses that scope.
- `EuclideanHardy.lean`: removed `funext n` and
  `simp only [Pi.div_apply]` after `convert hh using 1`; CI reports that
  the preceding conversion now closes the goal, making both tactics dead.

### Static validation and hashes

All theorem headers, including private supporting lemmas, were compared
against HEAD and are unchanged in these seven files. Top-level definition
and abbreviation declarations are unchanged. No axiom or hole was introduced.
No local Lean build, commit, push, ledger or configuration edit was performed.

| File | Before this repair | After this repair |
|---|---|---|
| `EuclideanHardy.lean` | `34f5f7550ec83bd198f93a787ea0c51c12146105c65546c7fdd81ed351f77182` | `a8c486c670da7f6a78bab2e317e5744c0a167b4f6f21405d7a13efbff526c661` |
| `WeightedMeanJointL2.lean` | `92a4f9a3e939576cd6faeaae29ef930acc77f83d9dd8c327394b55aa0503a80e` | `356fde83c912da3582f9b87ca94ad8eccef26ef733e39ac1b4dfbc25f7e2c9f2` |
| `SoftRieszReferencePositive.lean` | `37433227c8afaab47afedcdf17aa63e723336f2329eac6c09e5c2a6f2d298f0b` | `1eb428038515caf0c0a96e1502218d5b7df2b563c9867a2d095f9e30341d5742` |
| `ConfigurationReferenceProbability.lean` | `5c6e75b52a7c7442280af0a76b9d1fe8c31a7cd0eeb20652fbada03891716d07` | `810f7c5f999e756fa7287ba53205a05eaf801a89d8f8eb5b6761513d17195e4d` |
| `EuclideanSobolev.lean` | `061ea96bedf01f206e7b7fb4a36cad953cddb3dc611f13881bfa7d5fab25609b` | `07c48a58440465f86428cd283e474804c51380fb8be20ee12b7fc06c9f4f56d7` |
| `ConfigurationLawTranslation.lean` | `7072224dbfbbc47dc57c7d6f0d9ebdaa136aa59ffa9cb2f315180a61f610b347` | `74d2bd53f34077957628ffcf7f9b55ef0c8fe44699b0d691e29fcb5d19961270` |
| `WeakPotentialForm.lean` | `447a1094ceeb6186cd87943b87df48f615cbf9239b8af1e85ddd2db50bd2e8e8` | `16cb0239f75c211ac7a58c9ccffab2dfe37f5408933a915b2205dbf14324ed25` |

## Complete source-build log repairs, source ced0f99

Reviewed every actual `error:` in
`migration-reference-evidence/whole-build-ced0f99.log`. Its five failing
modules receive only the following compatibility edits. Warnings and
deprecations unrelated to failures are left unchanged. Linux CI must check
these edits; no local compilation was run.

### NativeReferenceMayerOperator

Removed the unused `open scoped InnerProduct`, the same obsolete scope
opening repaired earlier in two other modules.

### WeakPotentialForm

- The `eLpNorm_mono` call in `ramp_level_lp_lower` now passes
  `aestronglyMeasurable_const.indicator hE` before the unchanged
  pointwise norm comparison. This establishes the lower indicator function's
  measurability from the existing measurable level set.
- The indicator norm formula receives `hE.nullMeasurableSet` in place of `hE`,
  following the pinned
  [Indicator.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Function/LpSeminorm/Indicator.lean)
  signature. Neither set nor indicator constant changes.
- The norm-power identity in `ramp_level_sobolev` receives
  `(Hr.continuous_fderiv (by norm_num)).aestronglyMeasurable`, derived from
  the already proved C¹ regularity of the same ramp composition.

These resolve the subsequent level-bound and measurability goals without
changing the ramp, level set, exponent, or inequality.

### FiniteGibbsCompactNormalizedSobolev

The proof-local `have gradient_L2` helper previously invoked the norm-integral
identity without proving measurability of its arbitrary gradient argument.
The upgraded norm definition requires that measurability explicitly. The
local helper now accepts
`hgm : AEStronglyMeasurable (EuclideanGradient g) volume` and passes it to
`eLpNorm_eq_lintegral_rpow_enorm_toReal`. At the helper's sole use, `g` is
the smooth transformed approximation `tr (fn n)`; the existing
`continuous_gradient` and `htr` facts supply `hgm`. This adds no public
hypothesis, changes no declaration statement, and changes neither the energy
nor the approximation.

The limit norm bound also receives the existing
`(htr f hf).continuous.aestronglyMeasurable` proof before its unchanged
pointwise limit. The pinned
[LpSpace/Complete.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Function/LpSpace/Complete.lean)
requires measurability of the limit as a separate argument.

### Remaining MemLp projections

- `NativeGibbsJumpVariance.lean`: `hj.1.mono_ac hAC` becomes
  `hj.aestronglyMeasurable.mono_ac hAC`.
- `NativeGibbsTransformedL2.lean`: `(hmem i).1.1.prodMk_left` becomes
  `(hmem i).1.aestronglyMeasurable.prodMk_left`.

The outer conjunction projection in the second expression is retained; only
the obsolete projection inside its MemLp fact is replaced.

### Validation and deferred unused source

Compared every public and private theorem header and top-level definition,
abbreviation and structure declaration against HEAD: all are unchanged in
the five repaired files. No hole or axiom was introduced. No ledger,
configuration, workflow, README, formalization metadata or source-review
file was edited by this batch. No commit or push was performed.

The unbuilt `AtomicNormalizedSobolev.lean` contains analogous old norm-integral
and limit API uses. It was not among actual errors in this log and was left
untouched for this narrowly scoped repair; it needs attention if a later
build adds that module.

| File | Before this repair | After this repair |
|---|---|---|
| `NativeReferenceMayerOperator.lean` | `f8169b5282d5d0ca61a05b8728e3c2a42b8c7df490ad4672b86415e022f64884` | `7369bda6dd4a97a8a7aa018ffbd4b36f3c4909d24036344ebd350c15b094fa0b` |
| `WeakPotentialForm.lean` | `16cb0239f75c211ac7a58c9ccffab2dfe37f5408933a915b2205dbf14324ed25` | `0d005719419ef16e4ac098e7215d6bf697a1f22349ad337e58905f9fe7ac94eb` |
| `FiniteGibbsCompactNormalizedSobolev.lean` | `ab93dabff31ef3105871d22f43236604d8817b835b01be1f146237aa0449b3d2` | `c4855a319c6501dfad599dd588d93048799cf81d22d1659bcd93ce6fa28175b9` |
| `NativeGibbsJumpVariance.lean` | `0a5ff3a0fedefdd774bb3a5a584bec4b0f62444aad978d5894169e61a5c6716a` | `df4e59d81918dcb6f54557fc012bf0c845e8c2a4ecddc804153b5c1e72f3d237` |
| `NativeGibbsTransformedL2.lean` | `4ff2d7afb5b836b43168d82b8ad1ebf9732143898025d27710cd5669b5dd05cc` | `16a13d141f17256692935bd74ea32e4e4a76a19c338377a03229b4f647d7eb1b` |
