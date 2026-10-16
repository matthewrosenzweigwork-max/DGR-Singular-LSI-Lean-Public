module

public import Tablet.EuclideanLaplacian

@[expose] public section

-- [TABLET NODE: EuclideanDerivativeCoordinates]
theorem EuclideanDerivativeCoordinates {ι : Type*} [Fintype ι]
    (f : EuclideanSpace ℝ ι → ℝ) (x : EuclideanSpace ℝ ι) :
    EuclideanGradient f x = WithLp.toLp 2 (fun k =>
      fderiv ℝ f x (EuclideanSpace.basisFun ι ℝ k)) ∧
    EuclideanLaplacian f x = ∑ k,
      EuclideanHessian f x (EuclideanSpace.basisFun ι ℝ k)
        (EuclideanSpace.basisFun ι ℝ k) := by
-- BODY
  constructor
  · apply PiLp.ext
    intro k
    have h := congrArg (fun L : EuclideanSpace ℝ ι →L[ℝ] ℝ =>
      L (EuclideanSpace.basisFun ι ℝ k)) (toDual_gradient (f := f) (x := x))
    rw [InnerProductSpace.toDual_apply_apply, EuclideanSpace.inner_basisFun_real] at h
    exact h
  · simp only [EuclideanLaplacian,
      InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
        (EuclideanSpace.basisFun ι ℝ)]
    congr 1
    funext k
    rw [← bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
    rfl
