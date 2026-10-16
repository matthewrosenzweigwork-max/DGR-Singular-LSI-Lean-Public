import Tablet.EuclideanHessian
import Mathlib.Analysis.InnerProductSpace.Laplacian

-- [TABLET NODE: EuclideanLaplacian]
noncomputable def EuclideanLaplacian {ι : Type*} [Fintype ι]
    (V : EuclideanSpace ℝ ι → ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
-- BODY
  Laplacian.laplacian V x
