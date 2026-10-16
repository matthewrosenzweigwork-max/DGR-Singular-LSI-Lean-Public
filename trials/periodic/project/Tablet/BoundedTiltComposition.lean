import Tablet.BoundedDensityComparison
open MeasureTheory
-- [TABLET NODE: BoundedTiltComposition]
theorem BoundedTiltComposition {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (w b : Ω → ℝ) (l u : ℝ) (hw : Measurable w)
    (hwp : ∀ᵐ x ∂μ, 0 ≤ w x) (hwi : Integrable w μ) (hZ : 0 < ∫ x, w x ∂μ)
    (hb : Measurable b) (hl : 0 < l) (hbb : ∀ᵐ x ∂μ, l ≤ b x ∧ b x ≤ u) :
    NormalizedTilt μ (fun x => b x * w x) = NormalizedTilt (NormalizedTilt μ w) b := by
-- BODY
  have hbn : ∀ᵐ x ∂μ, 0 ≤ b x := hbb.mono fun x hx => hl.le.trans hx.1
  have hbabs : ∀ᵐ x ∂μ, ‖b x‖ ≤ max |l| |u| := by
    filter_upwards [hbb, hbn] with x hx hp
    rw [Real.norm_eq_abs, abs_of_nonneg hp]
    exact hx.2.trans ((le_abs_self u).trans (le_max_right _ _))
  have hbwi : Integrable (fun x => b x * w x) μ := hwi.bdd_mul hb.aestronglyMeasurable hbabs
  have hZbw : 0 < ∫ x, b x * w x ∂μ := by
    have hlow : l * ∫ x, w x ∂μ ≤ ∫ x, b x * w x ∂μ := by
      rw [← integral_const_mul]
      apply integral_mono_ae (hwi.const_mul l) hbwi
      filter_upwards [hbb, hwp] with x hx hp
      exact mul_le_mul_of_nonneg_right hx.1 hp
    exact (mul_pos hl hZ).trans_le hlow
  have ht := (TiltNormalization μ w hw hwp hwi hZ).2 b hb (by simpa only [mul_comm] using hbwi)
  simp only [NormalizedTilt] at ht ⊢
  rw [ht.2]
  rw [← withDensity_mul μ (by fun_prop) (by fun_prop)]
  apply withDensity_congr_ae
  filter_upwards [hwp, hbn] with x hx hbpos
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (div_nonneg hx hZ.le)]
  congr 1
  field_simp [ne_of_gt hZ, ne_of_gt hZbw] <;> ring
