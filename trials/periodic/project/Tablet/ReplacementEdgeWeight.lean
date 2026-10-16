module

public import Tablet.PairAlgebra
public import Tablet.GibbsWeight

@[expose] public section
-- [TABLET NODE: ReplacementEdgeWeight]
theorem ReplacementEdgeWeight {d N : ℕ} (G q : UnitAddTorus (Fin d) → ℝ)
    (hGe : ∀ x, G (-x) = G x) (β : ℝ) (X : Configuration d N)
    (i : Fin N) (z : UnitAddTorus (Fin d)) :
    GibbsWeight G q β X * Real.exp (-ConditionalPotential G β X i z) * q z =
      GibbsWeight G q β (Replacement X i z) *
        Real.exp (-ConditionalPotential G β (Replacement X i z) i (X i)) * q (X i) ∧
    (∀ v, ConditionalPotential G β (Replacement X i z) i v = ConditionalPotential G β X i v) := by
-- BODY
  classical
  have hu : ∀ v, ConditionalPotential G β (Replacement X i z) i v = ConditionalPotential G β X i v := by
    intro v
    unfold ConditionalPotential
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hji : j = i
    · simp only [hji, ↓reduceIte]
    · simp only [hji, ↓reduceIte, Replacement, Function.update_of_ne hji]
  have hp : ProductDensity q (Replacement X i z) * q (X i) = ProductDensity q X * q z := by
    have h0 := Finset.mul_prod_erase (Finset.univ : Finset (Fin N)) (fun j => q (X j)) (Finset.mem_univ i)
    have h1 := Finset.mul_prod_erase (Finset.univ : Finset (Fin N)) (fun j => q (Replacement X i z j)) (Finset.mem_univ i)
    have he : (∏ j ∈ (Finset.univ : Finset (Fin N)).erase i, q (Replacement X i z j)) =
        ∏ j ∈ (Finset.univ : Finset (Fin N)).erase i, q (X j) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp only [Replacement, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    have hzi : Replacement X i z i = z := by simp only [Replacement, Function.update_self]
    rw [hzi] at h1
    unfold ProductDensity
    rw [← h0, ← h1, he]
    ring
  have he := (PairAlgebra G hGe β X).1 i z
  constructor
  · rw [hu]
    have he' : -β * PairEnergy G X - ConditionalPotential G β X i z =
        -β * PairEnergy G (Replacement X i z) - ConditionalPotential G β X i (X i) := by linarith
    unfold GibbsWeight
    calc
      _ = Real.exp (-β * PairEnergy G X - ConditionalPotential G β X i z) * (ProductDensity q X * q z) := by rw [sub_eq_add_neg, Real.exp_add]; ring
      _ = Real.exp (-β * PairEnergy G (Replacement X i z) - ConditionalPotential G β X i (X i)) * (ProductDensity q (Replacement X i z) * q (X i)) := by rw [he', hp]
      _ = _ := by rw [sub_eq_add_neg, Real.exp_add]; ring
  · exact hu
