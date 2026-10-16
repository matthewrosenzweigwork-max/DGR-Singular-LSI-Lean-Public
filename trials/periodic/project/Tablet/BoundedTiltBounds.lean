import Tablet.NormalizedTilt
-- [TABLET NODE: BoundedTiltBounds]
theorem BoundedTiltBounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (w : Ω → ℝ) (l u : ℝ) (hl : 0 < l)
    (hw : Measurable w) (hb : ∀ᵐ x ∂μ, l ≤ w x ∧ w x ≤ u) :
    MeasureTheory.Integrable w μ ∧
    l ≤ (∫ x, w x ∂μ) ∧ (∫ x, w x ∂μ) ≤ u ∧
    (∀ᵐ x ∂μ, l / (∫ y, w y ∂μ) ≤ w x / (∫ y, w y ∂μ) ∧
      w x / (∫ y, w y ∂μ) ≤ u / (∫ y, w y ∂μ)) ∧
    (u / (∫ y, w y ∂μ)) / (l / (∫ y, w y ∂μ)) = u / l := by
-- BODY
  classical
  have hi : MeasureTheory.Integrable w μ := by
    apply (MeasureTheory.integrable_const (max |l| |u| : ℝ)).mono' hw.aestronglyMeasurable
    filter_upwards [hb] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (le_trans (le_of_lt hl) hx.1)]
    exact hx.2.trans (le_abs_self u |>.trans (le_max_right _ _))
  have hzlo : l ≤ ∫ x, w x ∂μ := by
    simpa using MeasureTheory.integral_mono_ae (MeasureTheory.integrable_const l) hi
      (hb.mono fun _ hx => hx.1)
  have hzhi : (∫ x, w x ∂μ) ≤ u := by
    simpa using MeasureTheory.integral_mono_ae hi (MeasureTheory.integrable_const u)
      (hb.mono fun _ hx => hx.2)
  have hz : 0 < ∫ x, w x ∂μ := hl.trans_le hzlo
  refine ⟨hi, hzlo, hzhi, ?_, ?_⟩
  · filter_upwards [hb] with x hx
    exact ⟨div_le_div_of_nonneg_right hx.1 (le_of_lt hz),
      div_le_div_of_nonneg_right hx.2 (le_of_lt hz)⟩
  · field_simp
