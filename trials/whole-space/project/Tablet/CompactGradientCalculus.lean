module

public import Tablet.EuclideanDerivativeCoordinates

@[expose] public section
open scoped ContDiff

-- [TABLET NODE: CompactGradientCalculus]
theorem CompactGradientCalculus {ι : Type*} [Fintype ι]
    (f : EuclideanSpace ℝ ι → ℝ) (hs : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    Continuous (EuclideanGradient f) ∧ HasCompactSupport (EuclideanGradient f) ∧
    ∀ (a : ℝ) (X : EuclideanSpace ℝ ι),
      EuclideanGradient (fun Y => f (a • Y)) X = a • EuclideanGradient f (a • X) := by
-- BODY
  have he : EuclideanGradient f = (fun X => WithLp.toLp 2
      (fun k => fderiv ℝ f X (EuclideanSpace.basisFun ι ℝ k))) :=
    funext (fun X => (EuclideanDerivativeCoordinates f X).1)
  refine ⟨?_, ?_, ?_⟩
  · rw [he]
    have hd := hs.continuous_fderiv (by simp)
    fun_prop
  · rw [he]
    exact (hc.fderiv (𝕜 := ℝ)).comp_left
      (g := fun L : EuclideanSpace ℝ ι →L[ℝ] ℝ =>
        WithLp.toLp 2 (fun k => L (EuclideanSpace.basisFun ι ℝ k))) (by ext k; simp)
  · intro a X
    have h := ((hs.differentiable (by simp)).differentiableAt.hasFDerivAt).comp X
      ((hasFDerivAt_id X).const_smul a)
    rw [(EuclideanDerivativeCoordinates _ X).1, (EuclideanDerivativeCoordinates f (a • X)).1]
    ext k
    change (fderiv ℝ (f ∘ (a • id)) X) (EuclideanSpace.basisFun ι ℝ k) =
      a * (fderiv ℝ f (a • X)) (EuclideanSpace.basisFun ι ℝ k)
    rw [h.fderiv]
    simp
