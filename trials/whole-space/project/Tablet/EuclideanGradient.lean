module

public import Tablet.Preamble
public import Mathlib.Analysis.Calculus.Gradient.Basic

@[expose] public section

-- [TABLET NODE: EuclideanGradient]
noncomputable def EuclideanGradient {ι : Type*} [Fintype ι]
    (f : EuclideanSpace ℝ ι → ℝ) (x : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι :=
-- BODY
  gradient f x
