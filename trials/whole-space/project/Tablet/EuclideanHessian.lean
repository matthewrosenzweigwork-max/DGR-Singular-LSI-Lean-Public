import Tablet.EuclideanGradient

-- [TABLET NODE: EuclideanHessian]
noncomputable def EuclideanHessian {ι : Type*} [Fintype ι]
    (V : EuclideanSpace ℝ ι → ℝ) (x u v : EuclideanSpace ℝ ι) : ℝ :=
-- BODY
  (fderiv ℝ (fderiv ℝ V) x u) v
