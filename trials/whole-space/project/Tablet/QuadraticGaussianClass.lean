module

public import Tablet.TwoSidedPotential
public import Tablet.GrowthClassPotential
public import Tablet.EuclideanDerivativeCoordinates
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Tactic.Ring

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter Metric
open scoped ContDiff ENNReal NNReal
noncomputable section

-- [TABLET NODE: QuadraticGaussianClass]
theorem QuadraticGaussianClass (d : ℕ) (s : ℝ) :
    let V : OneParticle d → ℝ := fun x => ‖x‖^2/2
    ContDiff ℝ ∞ V ∧ (∀ x, EuclideanGradient V x=x) ∧
      (∀ x u v, EuclideanHessian V x u v=inner ℝ u v) ∧
      (∀ x, EuclideanLaplacian V x=(d:ℝ)) ∧ TwoSidedPotential d 1 1 V ∧
      V 0=0 ∧ (∀ x, V 0 ≤ V x) ∧
      GrowthClassPotential d s 1 (fun R => R^2/2) (fun _ => (d:ℝ)) V := by
-- BODY
  let V : OneParticle d → ℝ := fun x => ‖x‖^2/2
  have heq : V = fun x => (1/2:ℝ)*‖x‖^2 := by
    funext x
    dsimp only [V]
    ring
  have hreg : ContDiff ℝ ∞ V := by
    rw [heq]
    exact contDiff_const.mul (contDiff_norm_sq ℝ)
  have hf : fderiv ℝ V = innerSL ℝ := by
    funext x
    rw [heq]
    rw [fderiv_const_mul (hasStrictFDerivAt_norm_sq x).differentiableAt, fderiv_norm_sq_apply]
    ext u
    simp only [smul_apply, smul_eq_mul, two_smul, add_apply]
    ring
  have hhess (x u v : OneParticle d) : EuclideanHessian V x u v=inner ℝ u v := by
    unfold EuclideanHessian
    rw [hf, ContinuousLinearMap.fderiv]
    rfl
  have hgrad (x : OneParticle d) : EuclideanGradient V x=x := by
    apply (InnerProductSpace.toDual ℝ (OneParticle d)).injective
    rw [EuclideanGradient,toDual_gradient,hf]
    rfl
  have hlap (x : OneParticle d) : EuclideanLaplacian V x=(d:ℝ) := by
    rw [(EuclideanDerivativeCoordinates V x).2]
    simp [hhess]
  have hreg2 : ContDiff ℝ 2 V := by
    rw [heq]
    exact contDiff_const.mul (contDiff_norm_sq ℝ)
  have htwo : TwoSidedPotential d 1 1 V := by
    refine ⟨⟨hreg2,?_⟩,?_⟩
    · intro x u
      simp [hhess]
    · intro x u
      simp [hhess]
  have hzero : V 0=0 := by simp [V]
  have hmin : ∀ x, V 0 ≤ V x := by
    intro x
    rw [hzero]
    dsimp only [V]
    positivity
  refine ⟨hreg,hgrad,hhess,hlap,htwo,hzero,hmin,?_⟩
  refine ⟨htwo.toPotentialBounds,⟨0,hmin,?_⟩,?_⟩
  · intro R hR x hx
    change V (x+0)-V 0 ≤ R^2/2
    rw [add_zero,hzero,sub_zero]
    dsimp only [V]
    nlinarith [norm_nonneg x]
  · intro a ha x
    rw [hlap]
    have hterm : 0 ≤ a*‖EuclideanGradient V x‖^ForceExponent s :=
      mul_nonneg ha.le (Real.rpow_nonneg (norm_nonneg _) _)
    linarith
