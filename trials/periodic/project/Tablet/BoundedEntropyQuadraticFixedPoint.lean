module

public import Tablet.L2EntropyQuadraticMinimum
public import Tablet.EntropyQuadraticMinimumConsistency
public import Tablet.GibbsLinearEntropyMinimum

@[expose] public section
open MeasureTheory
open scoped Topology

-- [TABLET NODE: BoundedEntropyQuadraticFixedPoint]
theorem BoundedEntropyQuadraticFixedPoint {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (β L C : ℝ) (hβ : 0 ≤ β) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (a : Lp ℝ 2 μ) (ha : ∀ᵐ x ∂μ, |a x| ≤ L)
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hpos : ∀ f, 0 ≤ inner ℝ f (T f))
    (hself : ∀ u v, inner ℝ u (T v) = inner ℝ (T u) v)
    (hpotential : ∀ r : Lp ℝ 2 μ,
      (∀ᵐ x ∂μ, r x ∈ Set.Icc 0 (Real.exp (2*(L+β*C)))) →
      (∫ x, r x ∂μ) = 1 → ∀ᵐ x ∂μ, |(T r) x| ≤ C) :
    ∃ r : Lp ℝ 2 μ,
      (∀ᵐ x ∂μ, 0 < r x ∧ r x ≤ Real.exp (2*(L+β*C))) ∧
      (∫ x, r x ∂μ) = 1 ∧
      (∀ᵐ x ∂μ, r x = Real.exp (a x-β*(T r) x) /
        (∫ y, Real.exp (a y-β*(T r) y) ∂μ)) := by
-- BODY
  let K := L+β*C
  let M := Real.exp (2*K)
  have hK : 0 ≤ K := add_nonneg hL (mul_nonneg hβ hC)
  have hM : 1 ≤ M := Real.one_le_exp_iff.mpr (by dsimp [K]; positivity)
  have hMp : 0 < M := Real.exp_pos _
  obtain ⟨r, hr, hrm, hmin⟩ := L2EntropyQuadraticMinimum μ M β hM hβ a T hpos
  let A : Ω → ℝ := fun x => β*(T r) x-a x
  have hAm : AEStronglyMeasurable A μ :=
    (Lp.aestronglyMeasurable (T r)).const_mul β |>.sub (Lp.aestronglyMeasurable a)
  have hTr := hpotential r hr hrm
  have hAb : ∀ᵐ x ∂μ, |A x| ≤ K := by
    filter_upwards [ha, hTr] with x hax htx
    calc
      |A x| ≤ |β*(T r) x|+|a x| := abs_sub _ _
      _ ≤ β*C+L := by rw [abs_mul, abs_of_nonneg hβ]; gcongr
      _ = K := by dsimp [K]; ring
  obtain ⟨_, ν, hνeq, hνb, hνm, _, hνmin⟩ := GibbsLinearEntropyMinimum μ A K hK hAm hAb
  have hν : ∀ᵐ x ∂μ, ν x ∈ Set.Icc 0 M := hνb.mono fun _ hx => ⟨hx.1.le, hx.2⟩
  have hid (f : Lp ℝ 2 μ) :
      (∫ x, f x*A x ∂μ) = -inner ℝ f (a-β • T r) := by
    rw [L2.inner_def, ← integral_neg]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub a (β • T r), Lp.coeFn_smul β (T r)] with x hx hy
    change f x*A x = -inner ℝ (f x) ((a-β • T r) x)
    rw [hx]
    simp only [Pi.sub_apply, hy, Pi.smul_apply, smul_eq_mul]
    simp [RCLike.inner_apply, A]
    ring
  have hlinear : ∀ f : Lp ℝ 2 μ, (∀ᵐ x ∂μ, f x ∈ Set.Icc 0 M) → (∫ x, f x ∂μ) = 1 →
      (∫ x, ν x*Real.log (ν x) ∂μ)-inner ℝ ν (a-β • T r) ≤
      (∫ x, f x*Real.log (f x) ∂μ)-inner ℝ f (a-β • T r) := by
    intro f hf hfm
    simpa only [hid, sub_eq_add_neg] using hνmin M hMp le_rfl f hf hfm
  have heq := EntropyQuadraticMinimumConsistency μ M β hMp a T hself r ν hr hν hrm hνm hmin hlinear
  refine ⟨r, heq ▸ hνb, hrm, ?_⟩
  rw [← heq] at hνeq
  simpa only [A, neg_sub, neg_mul] using hνeq
