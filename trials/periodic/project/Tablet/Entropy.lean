module

public import Tablet.Preamble

@[expose] public section
-- [TABLET NODE: Entropy]
noncomputable def Entropy {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (u : Ω → ℝ) : ℝ :=
-- BODY
  (∫ x, u x * Real.log (u x) ∂μ) -
    (∫ x, u x ∂μ) * Real.log (∫ x, u x ∂μ)
