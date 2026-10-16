module

public import Tablet.EuclideanDerivativeCoordinates
public import Mathlib.Analysis.InnerProductSpace.Dual

@[expose] public section

-- [TABLET NODE: GradientNormIdentity]
theorem GradientNormIdentity {ι : Type*} [Fintype ι]
    (f : EuclideanSpace ℝ ι → ℝ) (x : EuclideanSpace ℝ ι) :
    ‖EuclideanGradient f x‖ ^ 2 =
      ∑ k, (fderiv ℝ f x (EuclideanSpace.basisFun ι ℝ k)) ^ 2 ∧
    ‖EuclideanGradient f x‖ = ‖fderiv ℝ f x‖ := by
-- BODY
  have hs : ‖EuclideanGradient f x‖ ^ 2 =
      ∑ k, (fderiv ℝ f x (EuclideanSpace.basisFun ι ℝ k)) ^ 2 := by
    simpa [(EuclideanDerivativeCoordinates f x).1] using
      EuclideanSpace.real_norm_sq_eq (EuclideanGradient f x)
  refine ⟨hs, ?_⟩
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [hs, (EuclideanSpace.basisFun ι ℝ).norm_dual]
