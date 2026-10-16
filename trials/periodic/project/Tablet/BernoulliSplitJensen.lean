module

public import Tablet.Preamble
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Logic.Equiv.Prod

@[expose] public section
-- [TABLET NODE: BernoulliSplitJensen]
theorem BernoulliSplitJensen (N : ℕ) (a : Fin N → Fin N → ℝ)
    (hdiag : ∀ i, a i i = 0) (t : ℝ)
    (Φ : ℝ → ℝ) (hΦ : ConvexOn ℝ Set.univ Φ) :
    Φ (t * ∑ i,∑ j,a i j) ≤
      (Fintype.card (Fin N → Bool) : ℝ)⁻¹ *
        ∑ σ : Fin N → Bool, Φ
          (4*t*∑ i,∑ j,if σ i = true ∧ σ j = false then a i j else 0) := by
-- BODY
  classical
  let C : ℝ := Fintype.card (Fin N → Bool)
  have hC : C ≠ 0 := by
    dsimp [C]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Fin N → Bool) ≠ 0)
  have hC0 : 0 ≤ C⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hpair (i j : Fin N) (hij : i ≠ j) :
      (∑ σ : Fin N → Bool,if σ i = true ∧ σ j = false then (1 : ℝ) else 0) = C/4 := by
    let j' : {k : Fin N // k ≠ i} := ⟨j,Ne.symm hij⟩
    let e : (Fin N → Bool) ≃ Bool × (Bool ×
        ({k : {k : Fin N // k ≠ i} // k ≠ j'} → Bool)) :=
      (Equiv.funSplitAt i Bool).trans
        (Equiv.prodCongr (Equiv.refl Bool) (Equiv.funSplitAt j' Bool))
    have hsum : (∑ σ : Fin N → Bool,if σ i = true ∧ σ j = false then (1 : ℝ) else 0) =
        ∑ v : Bool × (Bool × ({k : {k : Fin N // k ≠ i} // k ≠ j'} → Bool)),
          if v.1 = true ∧ v.2.1 = false then (1 : ℝ) else 0 :=
      Fintype.sum_equiv e _ _ (fun σ => rfl)
    have hcard : C = 4 *
        (Fintype.card ({k : {k : Fin N // k ≠ i} // k ≠ j'} → Bool) : ℝ) := by
      have h := Fintype.card_congr e
      simp only [Fintype.card_prod,Fintype.card_bool] at h
      have hc : (Fintype.card (Fin N → Bool) : ℝ) =
          2*(2*(Fintype.card ({k : {k : Fin N // k ≠ i} // k ≠ j'} → Bool) : ℝ)) := by
        exact_mod_cast h
      dsimp [C]
      linarith
    rw [hsum,hcard]
    simp only [Fintype.sum_prod_type,Fintype.sum_bool]
    simp
  have hterm (i j : Fin N) :
      (∑ σ : Fin N → Bool,if σ i = true ∧ σ j = false then a i j else 0) = C/4*a i j := by
    by_cases hij : i=j
    · subst j
      simp [hdiag]
    · have ht (σ : Fin N → Bool) :
          (if σ i = true ∧ σ j = false then a i j else 0) =
            (if σ i = true ∧ σ j = false then (1 : ℝ) else 0)*a i j := by
        split_ifs <;>ring
      simp_rw [ht,←Finset.sum_mul]
      rw [hpair i j hij]
  let A : (Fin N → Bool) → ℝ := fun σ =>
    4*t*∑ i,∑ j,if σ i = true ∧ σ j = false then a i j else 0
  have hmean : (∑ σ : Fin N → Bool,C⁻¹*A σ) = t*∑ i,∑ j,a i j := by
    dsimp [A]
    simp_rw [mul_assoc,←Finset.mul_sum]
    have hswap : (∑ σ : Fin N → Bool,∑ i,∑ j,
        if σ i = true ∧ σ j = false then a i j else 0) =
        ∑ i,∑ j,∑ σ : Fin N → Bool,if σ i = true ∧ σ j = false then a i j else 0 := by
      have hrow (i : Fin N) := Finset.sum_comm (s := (Finset.univ : Finset (Fin N → Bool)))
        (t := (Finset.univ : Finset (Fin N)))
        (f := fun σ j => if σ i = true ∧ σ j = false then a i j else 0)
      rw [Finset.sum_comm]
      simp_rw [hrow]
    rw [hswap]
    simp_rw [hterm,←Finset.mul_sum]
    field_simp
  have hweights : (∑ σ : Fin N → Bool,C⁻¹) = 1 := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    change C*C⁻¹=1
    exact mul_inv_cancel₀ hC
  have hj := hΦ.map_sum_le
    (t := (Finset.univ : Finset (Fin N → Bool)))
    (w := fun _ => C⁻¹) (p := A)
    (fun _ _ => hC0) hweights (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul] at hj
  rw [hmean] at hj
  simpa only [A,←Finset.mul_sum] using hj
