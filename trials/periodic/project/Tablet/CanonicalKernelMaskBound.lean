module

public import Tablet.CenteredMaskConvexBound
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section
open MeasureTheory
-- [TABLET NODE: CanonicalKernelMaskBound]
theorem CanonicalKernelMaskBound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ)
    (q : Fin N → Fin N → Ω → Ω → ℝ)
    (hq : ∀ i j, Measurable (fun p : Ω × Ω => q i j p.1 p.2))
    (A : ℝ) (hA : 0 ≤ A) (hb : ∀ i j x y, |q i j x y| ≤ A)
    (hrow : ∀ i j y, (∫ x, q i j x y ∂μ) = 0)
    (hcol : ∀ i j x, (∫ y, q i j x y ∂μ) = 0)
    (α β : Fin N → Bool) (t : ℝ)
    (Φ : ℝ → ℝ) (hΦ : ConvexOn ℝ Set.univ Φ) (hΦc : Continuous Φ) :
    (∫ p : (Fin N → Ω) × (Fin N → Ω),
      Φ (t*∑ i,∑ j,if α i = true ∧ β j = true then q i j (p.1 i) (p.2 j) else 0)
      ∂(Measure.pi (fun _ : Fin N => μ)).prod (Measure.pi (fun _ : Fin N => μ))) ≤
    (∫ p : (Fin N → Ω) × (Fin N → Ω),Φ (t*∑ i,∑ j,q i j (p.1 i) (p.2 j))
      ∂(Measure.pi (fun _ : Fin N => μ)).prod (Measure.pi (fun _ : Fin N => μ))) := by
-- BODY
  classical
  let ν := Measure.pi (fun _ : Fin N => μ)
  let S (α β : Fin N → Bool) (p : (Fin N → Ω) × (Fin N → Ω)) :=
    ∑ i,∑ j,if α i = true ∧ β j = true then q i j (p.1 i) (p.2 j) else 0
  let E (α β : Fin N → Bool) := fun p : (Fin N → Ω) × (Fin N → Ω) => Φ (t*S α β p)
  let all : Fin N → Bool := fun _ => true
  have sum_bound (f : Fin N → ℝ) (h : ∀ i, |f i| ≤ A) : |∑ i,f i| ≤ (N : ℝ)*A := by
    calc
      _ ≤ ∑ i,|f i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin N,A := Finset.sum_le_sum (fun i _ => h i)
      _ = _ := by simp
  have hmS (α β : Fin N → Bool) : Measurable (S α β) := by
    apply Finset.measurable_fun_sum
    intro i hi
    apply Finset.measurable_fun_sum
    intro j hj
    by_cases h : α i = true ∧ β j = true
    · simp only [S,h,ite_true]
      have hp : Measurable (fun p : (Fin N → Ω) × (Fin N → Ω) => (p.1 i,p.2 j)) :=
        ((measurable_pi_apply i).comp measurable_fst).prodMk
          ((measurable_pi_apply j).comp measurable_snd)
      have hh := (hq i j).comp hp
      exact hh
    · simp only [h,ite_false]
      exact measurable_const
  have hbS (α β : Fin N → Bool) (p : (Fin N → Ω) × (Fin N → Ω)) :
      |S α β p| ≤ (N : ℝ)^2*A := by
    have hterm (i j : Fin N) :
        |if α i = true ∧ β j = true then q i j (p.1 i) (p.2 j) else 0| ≤ A := by
      split_ifs
      · exact hb i j _ _
      · simpa using hA
    calc
      _ ≤ ∑ i : Fin N,|∑ j : Fin N,if α i = true ∧ β j = true then q i j (p.1 i) (p.2 j) else 0| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin N,(N : ℝ)*A := Finset.sum_le_sum (fun i _ => sum_bound _ (hterm i))
      _ = _ := by simp;ring
  let C := |t| * ((N : ℝ)^2*A)
  have hC : 0 ≤ C := mul_nonneg (abs_nonneg _) (mul_nonneg (sq_nonneg _) hA)
  obtain ⟨D,hD⟩ := (isCompact_Icc : IsCompact (Set.Icc (-C) C)).exists_bound_of_continuousOn hΦc.continuousOn
  have hEi (α β : Fin N → Bool) : Integrable (E α β) (ν.prod ν) := by
    apply Integrable.of_bound (hΦc.measurable.comp ((hmS α β).const_mul t)).aestronglyMeasurable D
    exact Filter.Eventually.of_forall fun p => hD _ (by
      change -C ≤ t*S α β p ∧ t*S α β p ≤ C
      apply abs_le.mp
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hbS α β p) (abs_nonneg t))
  have hΨ : ConvexOn ℝ Set.univ (fun z => Φ (t*z)) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    simpa only [smul_eq_mul,mul_add,mul_left_comm t] using
      hΦ.2 (Set.mem_univ (t*x)) (Set.mem_univ (t*y)) ha hb hab
  have hΨc : Continuous (fun z => Φ (t*z)) := hΦc.comp (continuous_const.mul continuous_id)
  have hqxi (i j : Fin N) (y : Ω) : Integrable (fun x => q i j x y) μ :=
    Integrable.of_bound ((hq i j).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable A
      (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb i j x y))
  have hqyi (i j : Fin N) (x : Ω) : Integrable (fun y => q i j x y) μ :=
    Integrable.of_bound ((hq i j).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable A
      (Filter.Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs] using hb i j x y))
  have hrows (Y : Fin N → Ω) : (∫ X, E α β (X,Y) ∂ν) ≤ ∫ X,E all β (X,Y) ∂ν := by
    let f : Fin N → Ω → ℝ := fun i x => ∑ j,if β j = true then q i j x (Y j) else 0
    have hfm (i : Fin N) : Measurable (f i) := by
      apply Finset.measurable_fun_sum
      intro j hj
      by_cases h : β j = true
      · simp only [h,ite_true]
        have hp : Measurable (fun x : Ω => (x,Y j)) := measurable_id.prodMk measurable_const
        have hh := (hq i j).comp hp
        exact hh
      · simp only [h,ite_false];exact measurable_const
    have hfb (i : Fin N) (x : Ω) : |f i x| ≤ (N : ℝ)*A := by
      apply sum_bound
      intro j
      split_ifs
      · exact hb i j x (Y j)
      · simpa using hA
    have hfi (i j : Fin N) : Integrable (fun x => if β j = true then q i j x (Y j) else 0) μ := by
      split_ifs
      · exact hqxi i j (Y j)
      · exact integrable_const 0
    have hmean (i : Fin N) : (∫ x,f i x ∂μ) = 0 := by
      dsimp [f]
      rw [integral_finset_sum _ (fun j _ => hfi i j)]
      apply Finset.sum_eq_zero
      intro j hj
      by_cases h : β j = true
      · simpa only [h,ite_true] using hrow i j (Y j)
      · simp [h]
    have hmask := CenteredMaskConvexBound μ N f hfm ((N : ℝ)*A)
      (mul_nonneg (Nat.cast_nonneg N) hA) hfb hmean α (fun z => Φ (t*z)) hΨ hΨc
    have hterm (X : Fin N → Ω) (i : Fin N) :
        (if α i = true then f i (X i) else 0) =
          ∑ j,if α i = true ∧ β j = true then q i j (X i) (Y j) else 0 := by
      by_cases h : α i = true <;>simp [f,h]
    simp_rw [hterm] at hmask
    simpa [E,S,all,f] using hmask
  have hcols (X : Fin N → Ω) : (∫ Y,E all β (X,Y) ∂ν) ≤ ∫ Y,E all all (X,Y) ∂ν := by
    let f : Fin N → Ω → ℝ := fun j y => ∑ i,q i j (X i) y
    have hfm (j : Fin N) : Measurable (f j) :=
      Finset.measurable_fun_sum _ (fun i _ => (hq i j).comp (measurable_const.prodMk measurable_id))
    have hfb (j : Fin N) (y : Ω) : |f j y| ≤ (N : ℝ)*A :=
      sum_bound _ (fun i => hb i j (X i) y)
    have hmean (j : Fin N) : (∫ y,f j y ∂μ) = 0 := by
      dsimp [f]
      rw [integral_finset_sum _ (fun i _ => hqyi i j (X i))]
      simp [hcol]
    have hmask := CenteredMaskConvexBound μ N f hfm ((N : ℝ)*A)
      (mul_nonneg (Nat.cast_nonneg N) hA) hfb hmean β (fun z => Φ (t*z)) hΨ hΨc
    have hterm (Y : Fin N → Ω) (j : Fin N) :
        (if β j = true then f j (Y j) else 0) =
          ∑ i,if β j = true then q i j (X i) (Y j) else 0 := by
      by_cases h : β j = true <;>simp [f,h]
    simp only [hterm] at hmask
    have hs1 (Y : Fin N → Ω) : (∑ j : Fin N,∑ i : Fin N,if β j = true then q i j (X i) (Y j) else 0) =
        ∑ i : Fin N,∑ j : Fin N,if β j = true then q i j (X i) (Y j) else 0 := Finset.sum_comm
    have hs2 (Y : Fin N → Ω) : (∑ j : Fin N,∑ i : Fin N,q i j (X i) (Y j)) =
        ∑ i : Fin N,∑ j : Fin N,q i j (X i) (Y j) := Finset.sum_comm
    dsimp [f] at hmask
    simp_rw [hs1,hs2] at hmask
    simpa [E,S,all] using hmask
  change (∫ p,E α β p ∂ν.prod ν) ≤ ∫ p,E all all p ∂ν.prod ν
  calc
    _ = ∫ Y,∫ X,E α β (X,Y) ∂ν ∂ν := integral_prod_symm _ (hEi α β)
    _ ≤ ∫ Y,∫ X,E all β (X,Y) ∂ν ∂ν :=
      integral_mono_ae (hEi α β).integral_prod_right (hEi all β).integral_prod_right
        (Filter.Eventually.of_forall hrows)
    _ = ∫ X,∫ Y,E all β (X,Y) ∂ν ∂ν := by
      rw [←integral_prod_symm _ (hEi all β),integral_prod _ (hEi all β)]
    _ ≤ ∫ X,∫ Y,E all all (X,Y) ∂ν ∂ν :=
      integral_mono_ae (hEi all β).integral_prod_left (hEi all all).integral_prod_left
        (Filter.Eventually.of_forall hcols)
    _ = _ := (integral_prod _ (hEi all all)).symm
