module

public import Tablet.OneParticle
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

-- [TABLET NODE: GaussianConfinementIntegral]
theorem GaussianConfinementIntegral {ι : Type*} [Fintype ι]
    (κ : ℝ) (hκ : 0 < κ) :
    (∫ x : EuclideanSpace ℝ ι, Real.exp (-(κ / 2) * ‖x‖ ^ 2)) =
        Real.sqrt (2 * Real.pi / κ) ^ Fintype.card ι ∧
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ ι => Real.exp (-(κ / 2) * ‖x‖ ^ 2)) ∧
    0 < ∫ x : EuclideanSpace ℝ ι, Real.exp (-(κ / 2) * ‖x‖ ^ 2) := by
-- BODY
  have heq : (∫ x : EuclideanSpace ℝ ι, Real.exp (-(κ / 2) * ‖x‖ ^ 2)) =
      Real.sqrt (2 * Real.pi / κ) ^ Fintype.card ι := by
    rw [← (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp ι).symm.integral_comp']
    have hfactor : ∀ x : EuclideanSpace ℝ ι,
        Real.exp (-(κ / 2) * ‖x‖ ^ 2) = ∏ i, Real.exp (-(κ / 2) * (x i) ^ 2) := by
      intro x
      rw [EuclideanSpace.real_norm_sq_eq, ← Real.exp_sum, ← Finset.mul_sum]
    simp only [hfactor]
    change (∫ x : ι → ℝ, ∏ i, Real.exp (-(κ / 2) * (x i) ^ 2)) = _
    rw [MeasureTheory.integral_fintype_prod_volume_eq_prod
      (fun (_ : ι) (t : ℝ) => Real.exp (-(κ / 2) * t ^ 2))]
    simp only [integral_gaussian, Finset.prod_const, Finset.card_univ]
    congr 2
    field_simp
  have hp : 0 < ∫ x : EuclideanSpace ℝ ι, Real.exp (-(κ / 2) * ‖x‖ ^ 2) := by
    rw [heq]
    exact pow_pos (Real.sqrt_pos.2 (div_pos (mul_pos (by norm_num) Real.pi_pos) hκ)) _
  exact ⟨heq, MeasureTheory.Integrable.of_integral_ne_zero (ne_of_gt hp), hp⟩
