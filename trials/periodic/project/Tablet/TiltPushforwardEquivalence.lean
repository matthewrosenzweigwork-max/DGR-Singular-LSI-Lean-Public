module

public import Tablet.MeasurePreservingDensityTransport
public import Tablet.NormalizedTilt

@[expose] public section
open MeasureTheory

-- [TABLET NODE: TiltPushforwardEquivalence]
theorem TiltPushforwardEquivalence {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (e : X ≃ᵐ Y) (w : X → ℝ) (hw : Measurable w) :
    (NormalizedTilt μ w).map e = NormalizedTilt (μ.map e) (fun y => w (e.symm y)) := by
-- BODY
  have density_equiv_local 
      (μ : Measure X) (e : X ≃ᵐ Y) (w : X → ENNReal) (hw : Measurable w) :
      (μ.withDensity w).map e = (μ.map e).withDensity (fun y => w (e.symm y)) := by
    have hp : MeasurePreserving e μ (μ.map e) := ⟨e.measurable, rfl⟩
    have hh := MeasurePreservingDensityTransport μ (μ.map e) e hp
      (fun y => w (e.symm y)) (hw.comp e.symm.measurable)
    simpa only [Function.comp_def, MeasurableEquiv.symm_apply_apply] using hh

  have hg : Measurable (fun y : Y => w (e.symm y)) := hw.comp e.symm.measurable
  have hz : (∫ y,w (e.symm y)∂μ.map e)=(∫ x,w x∂μ) := by
    rw [integral_map e.measurable.aemeasurable hg.aestronglyMeasurable]
    simp only [MeasurableEquiv.symm_apply_apply]
  unfold NormalizedTilt
  rw [hz]
  exact density_equiv_local μ e _ (hw.div_const _).ennreal_ofReal
