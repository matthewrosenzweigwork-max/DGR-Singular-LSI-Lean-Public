module

public import Tablet.BoundedTiltBounds
public import Tablet.TiltNormalization

@[expose] public section
open MeasureTheory
-- [TABLET NODE: NormalizedTiltInverse]
theorem NormalizedTiltInverse {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (w : Ω → ℝ) (l u : ℝ)
    (hl : 0 < l) (hw : Measurable w) (hb : ∀ᵐ x ∂μ, l ≤ w x ∧ w x ≤ u) :
    NormalizedTilt (NormalizedTilt μ w) (fun x => 1 / w x) = μ := by
-- BODY
  let Z := ∫ x, w x ∂μ
  have hZ : 0 < Z := hl.trans_le (BoundedTiltBounds μ w l u hl hw hb).2.1
  have hwp : ∀ᵐ x ∂μ, 0 ≤ w x := hb.mono fun x hx => hl.le.trans hx.1
  have hwne : ∀ᵐ x ∂μ, w x ≠ 0 := hb.mono fun x hx => ne_of_gt (hl.trans_le hx.1)
  have hprod : (fun x => (1 / w x) * w x) =ᵐ[μ] (fun _ => (1 : ℝ)) := by
    filter_upwards [hwne] with x hx
    simp [hx]
  have hpi : Integrable (fun x => (1 / w x) * w x) μ := (integrable_const (1 : ℝ)).congr hprod.symm
  have hnorm := (TiltNormalization μ w hw hwp (BoundedTiltBounds μ w l u hl hw hb).1 hZ).2
    (fun x => 1 / w x) (measurable_const.div hw) hpi
  have hi : (∫ x, 1 / w x ∂NormalizedTilt μ w) = 1 / Z := by
    rw [hnorm.2, integral_congr_ae hprod]
    simp [Z]
  change (NormalizedTilt μ w).withDensity (fun x => ENNReal.ofReal ((1 / w x) /
    (∫ y, 1 / w y ∂NormalizedTilt μ w))) = μ
  rw [hi]
  change (μ.withDensity (fun x => ENNReal.ofReal (w x / Z))).withDensity
    (fun x => ENNReal.ofReal ((1 / w x) / (1 / Z))) = μ
  have hm : Measurable (fun x => ENNReal.ofReal ((1 / w x) / (1 / Z))) :=
    ((measurable_const.div hw : Measurable (fun x => (1 : ℝ) / w x)).div_const (1 / Z)).ennreal_ofReal
  rw [← withDensity_mul μ (hw.div_const Z).ennreal_ofReal hm]
  calc
    μ.withDensity (fun x => ENNReal.ofReal (w x / Z) * ENNReal.ofReal ((1 / w x) / (1 / Z))) =
        μ.withDensity (fun _ => 1) := by
      apply withDensity_congr_ae
      filter_upwards [hwne, hwp] with x hx hp
      rw [← ENNReal.ofReal_mul (div_nonneg hp hZ.le)]
      have he : w x / Z * ((1 / w x) / (1 / Z)) = 1 := by
        field_simp [hx, hZ.ne']
      rw [he]
      exact ENNReal.ofReal_one
    _ = μ := withDensity_one
