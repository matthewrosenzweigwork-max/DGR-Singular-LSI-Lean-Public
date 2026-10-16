import Tablet.NormalizedTilt
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
-- [TABLET NODE: TiltNormalization]
theorem TiltNormalization {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (w : Ω → ℝ)
    (hw : Measurable w) (hpos : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hint : MeasureTheory.Integrable w μ) (hZ : 0 < ∫ x, w x ∂μ) :
    MeasureTheory.IsProbabilityMeasure (NormalizedTilt μ w) ∧
    (∀ (f : Ω → ℝ), Measurable f →
      MeasureTheory.Integrable (fun x => f x * w x) μ →
      MeasureTheory.Integrable f (NormalizedTilt μ w) ∧
      (∫ x, f x ∂NormalizedTilt μ w) =
        (∫ x, f x * w x ∂μ) / (∫ x, w x ∂μ)) := by
-- BODY
  let Z : ℝ := ∫ x, w x ∂μ
  have hZ0 : Z ≠ 0 := ne_of_gt hZ
  have hratio : ∀ᵐ x ∂μ, 0 ≤ w x / Z :=
    hpos.mono fun x hx => div_nonneg hx hZ.le
  have hrInt : MeasureTheory.Integrable (fun x => w x / Z) μ := hint.div_const Z
  have hrMeas : Measurable (fun x => w x / Z) := hw.div_const Z
  have hdMeas : Measurable (fun x => ENNReal.ofReal (w x / Z)) := hrMeas.ennreal_ofReal
  have hdFinite : ∀ᵐ x ∂μ, ENNReal.ofReal (w x / Z) < (⊤ : ENNReal) :=
    Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  have hdReal : (fun x => (ENNReal.ofReal (w x / Z)).toReal) =ᵐ[μ]
      (fun x => w x / Z) :=
    hratio.mono fun x hx => ENNReal.toReal_ofReal hx
  constructor
  · apply MeasureTheory.isProbabilityMeasure_iff.mpr
    change μ.withDensity (fun x => ENNReal.ofReal (w x / Z)) Set.univ = 1
    rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ]
    simp only [MeasureTheory.Measure.restrict_univ]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hrInt hratio,
      MeasureTheory.integral_div]
    simp [Z, hZ0]
  · intro f hf hfw
    have hscaled : MeasureTheory.Integrable (fun x => (w x / Z) * f x) μ := by
      have hh := hfw.div_const Z
      convert hh using 1
      ext x
      ring
    have hsmul : MeasureTheory.Integrable
        (fun x => (ENNReal.ofReal (w x / Z)).toReal • f x) μ := by
      apply hscaled.congr
      filter_upwards [hdReal] with x hx
      simp [hx, smul_eq_mul]
    constructor
    · exact (MeasureTheory.integrable_withDensity_iff_integrable_smul'
        hdMeas hdFinite).mpr hsmul
    · change (∫ x, f x ∂μ.withDensity (fun x => ENNReal.ofReal (w x / Z))) =
        (∫ x, f x * w x ∂μ) / Z
      rw [integral_withDensity_eq_integral_toReal_smul hdMeas hdFinite]
      calc
        (∫ x, (ENNReal.ofReal (w x / Z)).toReal • f x ∂μ) =
            ∫ x, (w x / Z) * f x ∂μ := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [hdReal] with x hx
          simp [hx, smul_eq_mul]
        _ = ∫ x, (f x * w x) / Z ∂μ := by
          congr 1
          ext x
          ring
        _ = _ := MeasureTheory.integral_div Z _
