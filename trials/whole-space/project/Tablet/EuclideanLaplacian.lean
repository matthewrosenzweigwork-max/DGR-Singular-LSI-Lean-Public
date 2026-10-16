module

public import Tablet.EuclideanHessian
public import Mathlib.Analysis.InnerProductSpace.Laplacian

@[expose] public section

-- [TABLET NODE: EuclideanLaplacian]
noncomputable def EuclideanLaplacian {ι : Type*} [Fintype ι]
    (V : EuclideanSpace ℝ ι → ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
-- BODY
  Laplacian.laplacian V x
