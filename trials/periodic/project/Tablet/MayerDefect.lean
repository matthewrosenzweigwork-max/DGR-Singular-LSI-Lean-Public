module

public import Tablet.Preamble

@[expose] public section
-- [TABLET NODE: MayerDefect]
noncomputable def MayerDefect {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (G : Ω → ℝ) (a : ℝ) : ℝ :=
-- BODY
  ∫ x, a * G x - 1 + Real.exp (-a * G x) ∂μ
