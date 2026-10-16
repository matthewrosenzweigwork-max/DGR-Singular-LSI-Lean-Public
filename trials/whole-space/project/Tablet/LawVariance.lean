module

public import Tablet.Preamble
public import Mathlib.Probability.Moments.Variance

@[expose] public section

-- [TABLET NODE: LawVariance]
noncomputable def LawVariance {α : Type*} [MeasurableSpace α]
    (P : MeasureTheory.Measure α) (f : α → ℝ) : ℝ :=
-- BODY
  ProbabilityTheory.variance f P
