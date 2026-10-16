import Tablet.Preamble
import Mathlib.MeasureTheory.Integral.Prod
open MeasureTheory MeasureTheory.Measure
-- [TABLET NODE: BoundedJointDensityMarginal]
theorem BoundedJointDensityMarginal {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (η : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (u : X × Y → ℝ) (M : ℝ) (hM : 0 ≤ M) (hu : Measurable u)
    (hb : ∀ᵐ p ∂μ.prod η, u p ∈ Set.Icc 0 M) :
    ((μ.prod η).withDensity (fun p => ENNReal.ofReal (u p))).fst =
      μ.withDensity (fun x => ENNReal.ofReal (∫ y, u (x,y) ∂η)) := by
-- BODY
  have hsections := ae_ae_of_ae_prod hb
  apply Measure.ext
  intro s hs
  rw [fst_apply hs,withDensity_apply _ (hs.preimage measurable_fst),withDensity_apply _ hs]
  rw [← lintegral_indicator (hs.preimage measurable_fst),←lintegral_indicator hs]
  rw [lintegral_prod _ ((hu.ennreal_ofReal).indicator (hs.preimage measurable_fst)).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [hsections] with x hx
  by_cases hxs : x ∈ s
  · have hui : Integrable (fun y => u (x,y)) η := by
      apply Integrable.of_bound (hu.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable M
      filter_upwards [hx] with y hy
      change ‖u (x,y)‖ ≤ M
      simpa only [Real.norm_eq_abs,abs_of_nonneg hy.1] using hy.2
    simp only [Set.indicator,Set.mem_preimage,Prod.fst,hxs,if_pos]
    exact (ofReal_integral_eq_lintegral_ofReal hui (hx.mono fun y hy => hy.1)).symm
  · simp [Set.indicator,hxs]
