import Tablet.ExtendedEntropy
import Tablet.EntropyVariational
-- [TABLET NODE: EntropyExtension]
theorem EntropyExtension {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (u : Ω → ℝ) (hu : Measurable u) (hn : ∀ᵐ x ∂μ, 0 ≤ u x)
    (hi : MeasureTheory.Integrable u μ) :
    (ExtendedEntropy μ u < ⊤ ↔
      MeasureTheory.Integrable (fun x => u x * Real.log (u x)) μ) ∧
    (MeasureTheory.Integrable (fun x => u x * Real.log (u x)) μ →
      ExtendedEntropy μ u = ENNReal.ofReal (Entropy μ u)) := by
-- BODY
  have hb_nonneg : 0 ≤ ∫ x, u x ∂μ := MeasureTheory.integral_nonneg_of_ae hn
  by_cases hb0 : (∫ x, u x ∂μ) = 0
  · have hu0 : u =ᵐ[μ] 0 :=
      (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hn hi).mp hb0
    have hulog : (fun x => u x * Real.log (u x)) =ᵐ[μ] 0 := by
      filter_upwards [hu0] with x hx
      simp [hx]
    have hlog : MeasureTheory.Integrable (fun x => u x * Real.log (u x)) μ :=
      (MeasureTheory.integrable_zero Ω ℝ μ).congr hulog.symm
    have hent : Entropy μ u = 0 :=
      (EntropyVariational μ u hu hn hi hlog).2.2 hb0
    constructor
    · constructor
      · intro _
        exact hlog
      · intro _
        simp [ExtendedEntropy, hb0]
    · intro _
      simp [ExtendedEntropy, hb0, hent]
  · have hb : 0 < ∫ x, u x ∂μ := lt_of_le_of_ne hb_nonneg (Ne.symm hb0)
    let b : ℝ := ∫ x, u x ∂μ
    let v : Ω → ℝ := fun x => u x * Real.log (u x / b) - u x + b
    have hbp : 0 < b := hb
    have hbne : b ≠ 0 := hb0
    have log_identity (z : ℝ) :
        z * Real.log (z / b) = z * Real.log z - z * Real.log b := by
      by_cases hz : z = 0
      · simp [hz]
      · rw [Real.log_div hz hbne]
        ring
    have hvnonneg : ∀ᵐ x ∂μ, 0 ≤ v x := by
      filter_upwards [hn] with x hx
      change 0 ≤ u x * Real.log (u x / b) - u x + b
      by_cases hz : u x = 0
      · simp [hz, hbp.le]
      · have hxp : 0 < u x := lt_of_le_of_ne hx (Ne.symm hz)
        have h := mul_le_mul_of_nonneg_left
          (Real.log_le_sub_one_of_pos (div_pos hbp hxp)) hx
        rw [Real.log_div hbne hz] at h
        have hdiv : u x * (b / u x) = b := by field_simp
        rw [log_identity (u x)]
        nlinarith
    have hvmeas : Measurable v :=
      ((hu.mul (Real.measurable_log.comp (hu.div_const b))).sub hu).add measurable_const
    have hc : MeasureTheory.Integrable
        (fun x => u x * Real.log b + u x - b) μ :=
      ((hi.mul_const (Real.log b)).add hi).sub (MeasureTheory.integrable_const b)
    have hi_equiv : MeasureTheory.Integrable v μ ↔
        MeasureTheory.Integrable (fun x => u x * Real.log (u x)) μ := by
      constructor
      · intro hv
        exact (hv.add hc).congr (Filter.Eventually.of_forall fun x => by
          change (u x * Real.log (u x / b) - u x + b) +
            (u x * Real.log b + u x - b) = u x * Real.log (u x)
          rw [log_identity (u x)]
          ring)
      · intro hlog
        exact (hlog.sub hc).congr (Filter.Eventually.of_forall fun x => by
          change u x * Real.log (u x) - (u x * Real.log b + u x - b) =
            u x * Real.log (u x / b) - u x + b
          rw [log_identity (u x)]
          ring)
    have hfinite : (∫⁻ x, ENNReal.ofReal (v x) ∂μ) < ⊤ ↔
        MeasureTheory.Integrable v μ := by
      rw [lt_top_iff_ne_top]
      exact MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
        hvmeas.aestronglyMeasurable hvnonneg
    have hext : ExtendedEntropy μ u = ∫⁻ x, ENNReal.ofReal (v x) ∂μ := by
      simp only [ExtendedEntropy, hb0, if_false]
      rfl
    rw [hext]
    refine ⟨hfinite.trans hi_equiv, ?_⟩
    intro hlog
    have hv : MeasureTheory.Integrable v μ := hi_equiv.mpr hlog
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hv hvnonneg]
    congr 1
    exact ((EntropyVariational μ u hu hn hi hlog).2.1 hb).symm
