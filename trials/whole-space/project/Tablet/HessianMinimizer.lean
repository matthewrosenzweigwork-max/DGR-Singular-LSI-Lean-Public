module

public import Tablet.HessianQuadraticSupport
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

-- [TABLET NODE: HessianMinimizer]
theorem HessianMinimizer {d : ℕ} (V : OneParticle d → ℝ)
    (κ : ℝ) (hκ : 0 < κ) (hV : PotentialBounds d κ V) :
    (∃ C : ℝ, ∀ x, κ / 4 * ‖x‖ ^ 2 - C ≤ V x) ∧
    ∃ a : OneParticle d, (∀ x, V a ≤ V x) ∧
      (∀ b, (∀ x, V b ≤ V x) → b = a) ∧ fderiv ℝ V a = 0 ∧
      (∀ x, V a + κ / 2 * ‖x - a‖ ^ 2 ≤ V x) ∧
      (∀ x, κ * ‖x - a‖ ≤ ‖EuclideanGradient V x‖) := by
-- BODY
  let A : ℝ := ‖fderiv ℝ V 0‖
  let C : ℝ := A ^ 2 / κ - V 0
  have hC : ∀ x, κ / 4 * ‖x‖ ^ 2 - C ≤ V x := by
    intro x
    have hs := (HessianQuadraticSupport V κ hV 0 x).2
    simp only [sub_zero] at hs
    have hnorm := (fderiv ℝ V 0).le_opNorm x
    have hlin : -A * ‖x‖ ≤ fderiv ℝ V 0 x := by
      have hnegative : -(‖fderiv ℝ V 0 x‖) ≤ fderiv ℝ V 0 x := by
        simpa [Real.norm_eq_abs] using neg_abs_le (fderiv ℝ V 0 x)
      dsimp [A]
      linarith
    have hcanc : κ * (A ^ 2 / κ) = A ^ 2 := mul_div_cancel₀ _ (ne_of_gt hκ)
    have hproduct : 0 ≤ κ * (κ / 4 * ‖x‖ ^ 2 - A * ‖x‖ + A ^ 2 / κ) := by
      rw [mul_add, mul_sub, hcanc]
      nlinarith [sq_nonneg (κ * ‖x‖ / 2 - A)]
    have hyoung : 0 ≤ κ / 4 * ‖x‖ ^ 2 - A * ‖x‖ + A ^ 2 / κ :=
      nonneg_of_mul_nonneg_right hproduct hκ
    dsimp [C]
    linarith
  have hcoercive : Filter.Tendsto V (Filter.cocompact (OneParticle d)) Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    have hn : Filter.Tendsto (fun x : OneParticle d => ‖x‖)
        (Filter.cocompact (OneParticle d)) Filter.atTop := tendsto_norm_cocompact_atTop
    have he := hn.eventually (Filter.eventually_ge_atTop (max 1 (4 * (b + C) / κ)))
    filter_upwards [he] with x hx
    have h1 : 1 ≤ ‖x‖ := (le_max_left _ _).trans hx
    have hR : 4 * (b + C) / κ ≤ ‖x‖ := (le_max_right _ _).trans hx
    have hprod : 4 * (b + C) ≤ ‖x‖ * κ := (div_le_iff₀ hκ).mp hR
    have hsquare : ‖x‖ ≤ ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
    have hscaled := mul_le_mul_of_nonneg_left hsquare (le_of_lt hκ)
    nlinarith [hC x]
  obtain ⟨a, ha⟩ := hV.regularity.continuous.exists_forall_le hcoercive
  have hlocal : IsLocalMin V a := Filter.Eventually.of_forall ha
  have hzero : fderiv ℝ V a = 0 := hlocal.fderiv_eq_zero
  have hquad : ∀ x, V a + κ / 2 * ‖x - a‖ ^ 2 ≤ V x := by
    intro x
    simpa [hzero] using (HessianQuadraticSupport V κ hV a x).2
  refine ⟨⟨C, hC⟩, a, ha, ?_, hzero, hquad, ?_⟩
  · intro b hb
    have hsq : ‖b - a‖ ^ 2 = 0 := by
      have hnonneg := sq_nonneg ‖b - a‖
      have hq := hquad b
      have hba := hb a
      nlinarith
    have : ‖b - a‖ = 0 := (sq_eq_zero_iff).mp hsq
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  · intro x
    by_cases hx : x = a
    · simp [hx]
    have hr : 0 < ‖x - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
    have h1 := hquad x
    have h2 := (HessianQuadraticSupport V κ hV x a).2
    have hdiff : a - x = -(x - a) := by abel
    rw [hdiff, map_neg, norm_neg] at h2
    have hpoint : κ * ‖x - a‖ ^ 2 ≤ fderiv ℝ V x (x - a) := by linarith
    have hnorm := (fderiv ℝ V x).le_opNorm (x - a)
    have hreal : fderiv ℝ V x (x - a) ≤ ‖fderiv ℝ V x (x - a)‖ := by
      simpa [Real.norm_eq_abs] using le_abs_self (fderiv ℝ V x (x - a))
    have hdual : ‖fderiv ℝ V x‖ = ‖EuclideanGradient V x‖ := by
      simp [EuclideanGradient, gradient]
    rw [hdual] at hnorm
    have hmul : (κ * ‖x - a‖) * ‖x - a‖ ≤ ‖EuclideanGradient V x‖ * ‖x - a‖ := by
      nlinarith [hpoint, hnorm, hreal]
    exact le_of_mul_le_mul_right hmul hr
