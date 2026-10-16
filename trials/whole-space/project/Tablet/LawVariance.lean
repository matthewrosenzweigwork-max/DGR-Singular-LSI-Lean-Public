import Tablet.Preamble
import Mathlib.Probability.Moments.Variance

-- [TABLET NODE: LawVariance]
noncomputable def LawVariance {α : Type*} [MeasurableSpace α]
    (P : MeasureTheory.Measure α) (f : α → ℝ) : ℝ :=
-- BODY
  ProbabilityTheory.variance f P
