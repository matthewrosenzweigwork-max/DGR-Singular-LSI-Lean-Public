import Tablet.PairEnergy
import Tablet.Replacement
import Tablet.ConditionalPotential
-- [TABLET NODE: PairAlgebra]
theorem PairAlgebra {d N : ℕ} (g : UnitAddTorus (Fin d) → ℝ)
    (hg : ∀ x, g (-x) = g x) (β : ℝ) (X : Configuration d N) :
    (∀ (i : Fin N) (z : UnitAddTorus (Fin d)),
      β * PairEnergy g (Replacement X i z) - β * PairEnergy g X =
        ConditionalPotential g β X i z - ConditionalPotential g β X i (X i)) ∧
    (∑ i : Fin N, ConditionalPotential g β X i (X i)) =
      2 * β * PairEnergy g X := by
-- BODY
  classical
  have heven (x y : UnitAddTorus (Fin d)) : g (y - x) = g (x - y) := by
    simpa only [neg_sub] using hg (x - y)
  have hordered (Y : Configuration d N) :
      (∑ k : Fin N, ∑ j : Fin N, if j = k then 0 else g (Y k - Y j)) =
      2 * (∑ k : Fin N, ∑ j : Fin N, if k < j then g (Y k - Y j) else 0) := by
    have hterm (k j : Fin N) :
        (if j = k then (0 : ℝ) else g (Y k - Y j)) =
        (if k < j then g (Y k - Y j) else 0) +
        (if j < k then g (Y j - Y k) else 0) := by
      rcases lt_trichotomy k j with h | h | h
      · simp [h, ne_of_gt h, not_lt_of_gt h]
      · subst j; simp
      · simp [h, ne_of_lt h, not_lt_of_gt h, heven]
    simp_rw [hterm, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun k j : Fin N => if j < k then g (Y j - Y k) else 0)]
    ring
  constructor
  · intro i z
    let D : Fin N → ℝ := fun j => if j = i then 0 else g (z - X j) - g (X i - X j)
    have hterm (k j : Fin N) :
        (if j = k then (0 : ℝ) else g ((Replacement X i z) k - (Replacement X i z) j)) -
        (if j = k then 0 else g (X k - X j)) =
        (if k = i then D j else 0) + (if j = i then D k else 0) := by
      by_cases hk : k = i
      · subst k
        by_cases hj : j = i
        · subst j; simp [D]
        · simp [Replacement, hj, D]
      · by_cases hj : j = i
        · subst j
          simp [Replacement, hk, Ne.symm hk, D, heven]
        · simp [Replacement, hk, hj, D]
    have hdiff :
        (∑ k : Fin N, ∑ j : Fin N,
          if j = k then 0 else g ((Replacement X i z) k - (Replacement X i z) j)) -
        (∑ k : Fin N, ∑ j : Fin N, if j = k then 0 else g (X k - X j)) =
        2 * ∑ j : Fin N, D j := by
      rw [← Finset.sum_sub_distrib]
      simp_rw [← Finset.sum_sub_distrib, hterm, Finset.sum_add_distrib]
      simp [Finset.sum_ite_irrel]
      ring
    rw [hordered, hordered] at hdiff
    have hpairs :
        (∑ k : Fin N, ∑ j : Fin N,
          if k < j then g ((Replacement X i z) k - (Replacement X i z) j) else 0) -
        (∑ k : Fin N, ∑ j : Fin N, if k < j then g (X k - X j) else 0) =
        ∑ j : Fin N, D j := by linarith [hdiff]
    have hD : (∑ j : Fin N, D j) =
        (∑ j : Fin N, if j = i then 0 else g (z - X j)) -
        (∑ j : Fin N, if j = i then 0 else g (X i - X j)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases h : j = i <;> simp [D, h]
    dsimp [PairEnergy, ConditionalPotential]
    rw [div_eq_mul_inv]
    calc
      _ = (β * (N : ℝ)⁻¹) *
          ((∑ k : Fin N, ∑ j : Fin N,
            if k < j then g ((Replacement X i z) k - (Replacement X i z) j) else 0) -
           (∑ k : Fin N, ∑ j : Fin N, if k < j then g (X k - X j) else 0)) := by ring
      _ = _ := by rw [hpairs, hD]; ring
  · simp only [ConditionalPotential, ← Finset.mul_sum]
    rw [hordered]
    simp only [PairEnergy, div_eq_mul_inv]
    ring
