import Tablet.Entropy
-- [TABLET NODE: ExtendedEntropy]
noncomputable def ExtendedEntropy {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (u : Ω → ℝ) : ENNReal :=
-- BODY
  let b := ∫ x, u x ∂μ
  if b = 0 then 0 else
    ∫⁻ x, ENNReal.ofReal (u x * Real.log (u x / b) - u x + b) ∂μ
