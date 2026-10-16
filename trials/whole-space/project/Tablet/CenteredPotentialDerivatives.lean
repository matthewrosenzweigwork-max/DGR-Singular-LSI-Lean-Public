import Tablet.ShiftedReference
import Tablet.BoundedMultiplier
import Tablet.EuclideanDerivativeCoordinates
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Operations
set_option autoImplicit false
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter Metric
open scoped ContDiff ENNReal NNReal
noncomputable section

-- [TABLET NODE: CenteredPotentialDerivatives]
theorem CenteredPotentialDerivatives {d : ℕ} (V b : OneParticle d → ℝ) (a : OneParticle d) :
    let W := (ShiftedReference V b a).1
    W 0 = 0 ∧
    (∀ x, EuclideanGradient W x = EuclideanGradient V (x+a)) ∧
    (∀ x u v, EuclideanHessian W x u v = EuclideanHessian V (x+a) u v) ∧
    (∀ x, EuclideanLaplacian W x = EuclideanLaplacian V (x+a)) ∧
    (ContDiff ℝ 2 V → ContDiff ℝ 2 W) ∧
    (∀ L : ℝ, BoundedMultiplier d L b → BoundedMultiplier d L (ShiftedReference V b a).2) := by
-- BODY
  let W := (ShiftedReference V b a).1
  have hfirst (x : OneParticle d) : fderiv ℝ W x = fderiv ℝ V (x+a) := by
    dsimp only [W, ShiftedReference]
    rw [fderiv_sub_const, fderiv_comp_add_right]
  have hsecond (x u v : OneParticle d) : EuclideanHessian W x u v = EuclideanHessian V (x+a) u v := by
    have hf : fderiv ℝ W = fun y => fderiv ℝ V (y+a) := funext hfirst
    unfold EuclideanHessian
    rw [hf, fderiv_comp_add_right]
  refine ⟨?_, ?_, hsecond, ?_, ?_, ?_⟩
  · simp [W, ShiftedReference]
  · intro x
    exact congrArg (InnerProductSpace.toDual ℝ (OneParticle d)).symm (hfirst x)
  · intro x
    rw [(EuclideanDerivativeCoordinates W x).2, (EuclideanDerivativeCoordinates V (x+a)).2]
    exact Finset.sum_congr rfl (fun i _ => hsecond x _ _)
  · intro hV
    exact (hV.comp (contDiff_id.add contDiff_const)).sub contDiff_const
  · intro L hb
    refine ⟨hb.measurable.comp (measurable_id.add measurable_const), ?_⟩
    obtain ⟨m,M,hm,hmM,hL,hbound⟩ := hb.bounds
    exact ⟨m,M,hm,hmM,hL,fun x => hbound (x+a)⟩
