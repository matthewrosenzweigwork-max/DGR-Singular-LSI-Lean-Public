module

public import Tablet.Preamble

@[expose] public section
-- [TABLET NODE: NormalizedTilt]
noncomputable def NormalizedTilt {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (w : Ω → ℝ) : MeasureTheory.Measure Ω :=
-- BODY
  μ.withDensity (fun x => ENNReal.ofReal (w x / ∫ y, w y ∂μ))
