module

public import Tablet.TwoSidedPotential
public import Tablet.GrowthClassPotential
public import Tablet.HessianMinimizer
public import Tablet.EuclideanDerivativeCoordinates

@[expose] public section

-- [TABLET NODE: BoundedHessianGrowthData]
theorem BoundedHessianGrowthData {d : ℕ} (V : OneParticle d → ℝ)
    (κ K s : ℝ) (hκ : 0 < κ) (hκK : κ ≤ K)
    (hV : TwoSidedPotential d κ K V) :
    (∀ x, EuclideanLaplacian V x ≤ (d : ℝ) * K) ∧
    GrowthClassPotential d s κ (fun R => K * R ^ 2 / 2)
      (fun _ => (d : ℝ) * K) V := by
-- BODY
  have htrace : ∀ x, EuclideanLaplacian V x ≤ (d : ℝ) * K := by
    intro x
    rw [(EuclideanDerivativeCoordinates V x).2]
    calc
      _ ≤ ∑ _i : Fin d, K := by
        apply Finset.sum_le_sum
        intro i _
        simpa using hV.upper x (EuclideanSpace.basisFun (Fin d) ℝ i)
      _ = _ := by simp
  obtain ⟨a, ha, _, hzero, _, _⟩ := (HessianMinimizer V κ hκ hV.toPotentialBounds).2
  have hneg : PotentialBounds d (-K) (fun x => -V x) := by
    refine ⟨hV.regularity.neg, ?_⟩
    intro x u
    have heq : EuclideanHessian (fun z => -V z) x u u = -EuclideanHessian V x u u := by
      have hfirst : fderiv ℝ (fun z => -V z) = fun z => -fderiv ℝ V z := by
        funext z
        exact fderiv_fun_neg
      unfold EuclideanHessian
      rw [hfirst, fderiv_fun_neg]
      simp
    rw [heq]
    nlinarith [hV.upper x u]
  refine ⟨htrace, ⟨hV.toPotentialBounds, ⟨a, ha, ?_⟩, ?_⟩⟩
  · intro R hR x hx
    have hs := (HessianQuadraticSupport (fun z => -V z) (-K) hneg a (x + a)).2
    rw [fderiv_fun_neg, hzero] at hs
    simp only [neg_zero, zero_apply,
      add_sub_cancel_right] at hs
    have hK : 0 ≤ K := hκ.le.trans hκK
    have hsq : ‖x‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg x]
    have hmul := mul_le_mul_of_nonneg_left hsq hK
    change V (x + a) - V a ≤ K * R ^ 2 / 2
    nlinarith
  · intro a ha x
    have hterm : 0 ≤ a * ‖EuclideanGradient V x‖ ^ ForceExponent s :=
      mul_nonneg ha.le (Real.rpow_nonneg (norm_nonneg _) _)
    linarith [htrace x]
