import Tablet.CenteredPairEnergy
import Tablet.PairEnergy
-- [TABLET NODE: CenteredEnergyIdentity]
theorem CenteredEnergyIdentity {d N : ℕ} (hN : 1 ≤ N)
    (g r : UnitAddTorus (Fin d) → ℝ) (X : Configuration d N) :
    CenteredPairEnergy g r X = PairEnergy g X -
      ((N : ℝ)-1)/(N : ℝ) * ∑ i : Fin N, BackgroundPotential g r (X i) +
      ((N : ℝ)-1)/2 * BackgroundPairMean g r := by
-- BODY
  classical
  have hsum (f : Fin N → ℝ) :
      (∑ i : Fin N,∑ j : Fin N,if i < j then f i+f j else 0) =
        ((N : ℝ)-1) * ∑ i : Fin N,f i := by
    have hsplit (i j : Fin N) :
        (if i < j then f i+f j else 0) =
          (if i < j then f i else 0)+(if i < j then f j else 0) := by
      split_ifs <;>ring
    simp_rw [hsplit,Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j : Fin N => if i < j then f j else 0)]
    rw [←Finset.sum_add_distrib]
    have hrow (i : Fin N) :
        (∑ j : Fin N,if i < j then f i else 0)+
          (∑ j : Fin N,if j < i then f i else 0) = ((N : ℝ)-1)*f i := by
      rw [←Finset.sum_add_distrib]
      have hterm (j : Fin N) :
          (if i < j then f i else 0)+(if j < i then f i else 0) =
            f i-(if j=i then f i else 0) := by
        rcases lt_trichotomy i j with h|h|h
        · simp [h,ne_of_gt h,not_lt_of_gt h]
        · subst j;simp
        · simp [h,ne_of_lt h,not_lt_of_gt h]
      simp_rw [hterm]
      simp [Finset.sum_sub_distrib]
      ring
    simp_rw [hrow]
    exact (Finset.mul_sum _ _ _).symm
  have hcount : (∑ i : Fin N,∑ j : Fin N,if i < j then (1:ℝ) else 0) =
      (N : ℝ)*((N : ℝ)-1)/2 := by
    have hc := hsum (fun _ => (1:ℝ))
    have hterm (i j : Fin N) : (if i < j then (1:ℝ)+1 else 0) =
        2*(if i < j then (1:ℝ) else 0) := by split_ifs <;>ring
    simp_rw [hterm,←Finset.mul_sum] at hc
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hc
    linarith
  have hnp : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hterms (i j : Fin N) :
      (if i < j then CenteredKernel g r (X i) (X j) else 0) =
        (if i < j then g (X i-X j) else 0) -
        (if i < j then BackgroundPotential g r (X i)+BackgroundPotential g r (X j) else 0)+
        (if i < j then (1:ℝ) else 0)*BackgroundPairMean g r := by
    unfold CenteredKernel
    split_ifs <;>ring
  unfold CenteredPairEnergy PairEnergy
  simp_rw [hterms,Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.sum_mul]
  rw [hsum,hcount]
  field_simp
  <;>ring
