import Tablet.Preamble
import Mathlib.Analysis.Calculus.Gradient.Basic

-- [TABLET NODE: EuclideanGradient]
noncomputable def EuclideanGradient {ι : Type*} [Fintype ι]
    (f : EuclideanSpace ℝ ι → ℝ) (x : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι :=
-- BODY
  gradient f x
