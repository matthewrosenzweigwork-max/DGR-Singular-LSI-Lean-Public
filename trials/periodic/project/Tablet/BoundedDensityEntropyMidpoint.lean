import Tablet.BoundedEntropyStrongConvexity

open MeasureTheory

-- [TABLET NODE: BoundedDensityEntropyMidpoint]
theorem BoundedDensityEntropyMidpoint {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (u v : Ω → ℝ) (M : ℝ) (hM : 0 < M)
    (hum : AEStronglyMeasurable u μ) (hvm : AEStronglyMeasurable v μ)
    (hub : ∀ᵐ x ∂μ, u x ∈ Set.Icc 0 M)
    (hvb : ∀ᵐ x ∂μ, v x ∈ Set.Icc 0 M) :
    Integrable (fun x => u x * Real.log (u x)) μ ∧
    Integrable (fun x => v x * Real.log (v x)) μ ∧
    Integrable (fun x => (u x - v x) ^ 2) μ ∧
    (∫ x, ((u x + v x) / 2) * Real.log ((u x + v x) / 2) ∂μ) ≤
      ((∫ x, u x * Real.log (u x) ∂μ) + (∫ x, v x * Real.log (v x) ∂μ)) / 2 -
        (∫ x, (u x - v x) ^ 2 ∂μ) / (8 * M) := by
-- BODY
  have hint (a : Ω → ℝ) (ham : AEStronglyMeasurable a μ)
      (hab : ∀ᵐ x ∂μ, a x ∈ Set.Icc 0 M) :
      Integrable (fun x => a x * Real.log (a x)) μ := by
    obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) M)).exists_bound_of_continuousOn
      Real.continuous_mul_log.continuousOn
    apply (integrable_const C).mono'
      (Real.continuous_mul_log.comp_aestronglyMeasurable ham)
    exact hab.mono fun x hx => hC (a x) hx
  have hui := hint u hum hub
  have hvi := hint v hvm hvb
  have hm : AEStronglyMeasurable (fun x => (u x + v x) / 2) μ := (continuous_id.div_const 2).comp_aestronglyMeasurable (hum.add hvm)
  have hmb : ∀ᵐ x ∂μ, (u x + v x) / 2 ∈ Set.Icc 0 M := by
    filter_upwards [hub, hvb] with x hx hy
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hmi := hint _ hm hmb
  have hsq : Integrable (fun x => (u x - v x) ^ 2) μ := by
    apply (integrable_const (M ^ 2)).mono' ((continuous_id.pow 2).comp_aestronglyMeasurable (hum.sub hvm))
    filter_upwards [hub, hvb] with x hx hy
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change (u x - v x) ^ 2 ≤ M ^ 2
    have hl : 0 ≤ M - (u x - v x) := by linarith [hx.1, hx.2, hy.1, hy.2]
    have hr : 0 ≤ M + (u x - v x) := by linarith [hx.1, hx.2, hy.1, hy.2]
    nlinarith [mul_nonneg hl hr]
  refine ⟨hui, hvi, hsq, ?_⟩
  have hr : Integrable (fun x => (u x * Real.log (u x) + v x * Real.log (v x)) / 2 -
      (u x - v x) ^ 2 / (8 * M)) μ := ((hui.add hvi).div_const 2).sub (hsq.div_const _)
  have hh := integral_mono_ae hmi hr (by
    filter_upwards [hub, hvb] with x hx hy
    exact BoundedEntropyStrongConvexity M hM (u x) (v x) hx hy)
  have hsum : Integrable (fun x => u x * Real.log (u x) + v x * Real.log (v x)) μ := hui.add hvi
  rw [integral_sub (hsum.div_const 2) (hsq.div_const (8 * M)),
    integral_div, integral_div, integral_add hui hvi] at hh
  exact hh
