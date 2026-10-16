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
