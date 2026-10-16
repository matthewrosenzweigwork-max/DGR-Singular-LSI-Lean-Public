import Tablet.Preamble
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
open MeasureTheory ProbabilityTheory
-- [TABLET NODE: CanonicalL2SumVariance]
theorem CanonicalL2SumVariance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ)
    (q : Ω → Ω → ℝ) (hq : Measurable (fun p : Ω × Ω => q p.1 p.2))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hb : ∀ x y,|q x y|≤A)
    (hm : ∀ y,(∫ x,q x y ∂μ)=0) (hv : ∀ y,(∫ x,(q x y)^2 ∂μ)≤B^2) :
    (∫ X : Fin N → Ω,∫ y,(∑ i,q (X i) y)^2 ∂μ
      ∂Measure.pi (fun _ : Fin N => μ)) ≤ (N : ℝ)*B^2 := by
-- BODY
  classical
  let ν := Measure.pi (fun _ : Fin N => μ)
  let S (X : Fin N → Ω) (y : Ω) := ∑ i,q (X i) y
  have hmS : Measurable (fun p : (Fin N → Ω) × Ω => (S p.1 p.2)^2) := by
    apply Measurable.pow_const
    apply Finset.measurable_fun_sum
    intro i hi
    have hp : Measurable (fun p : (Fin N → Ω) × Ω => (p.1 i,p.2)) :=
      ((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd
    exact hq.comp hp
  have hbS (X : Fin N → Ω) (y : Ω) : |S X y|≤(N : ℝ)*A := by
    calc
      _ ≤ ∑ i,|q (X i) y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin N,A := Finset.sum_le_sum (fun i _ => hb _ _)
      _ = _ := by simp
  have hSi : Integrable (fun p : (Fin N → Ω) × Ω => (S p.1 p.2)^2) (ν.prod μ) := by
    apply Integrable.of_bound hmS.aestronglyMeasurable (((N : ℝ)*A)^2)
    exact Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      nlinarith [abs_le.mp (hbS p.1 p.2)]
  have hqxm (y : Ω) : Measurable (fun x => q x y) := hq.comp (measurable_id.prodMk measurable_const)
  have hqPi (y : Ω) (i : Fin N) : Integrable (fun X : Fin N → Ω => q (X i) y) ν :=
    integrable_comp_eval (μ := fun _ : Fin N => μ) (i := i) (Integrable.of_bound (hqxm y).aestronglyMeasurable A
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x y))
  have hpairI (y : Ω) (i j : Fin N) : Integrable (fun X : Fin N → Ω => q (X i) y*q (X j) y) ν := by
    apply Integrable.of_bound (((hqxm y).comp (measurable_pi_apply i)).mul
      ((hqxm y).comp (measurable_pi_apply j))).aestronglyMeasurable (A^2)
    exact Filter.Eventually.of_forall fun X => by
      change ‖q (X i) y*q (X j) y‖≤A^2
      rw [Real.norm_eq_abs,abs_mul]
      simpa only [pow_two] using mul_le_mul (hb (X i) y) (hb (X j) y) (abs_nonneg _) hA
  have hpair (y : Ω) (i j : Fin N) :
      (∫ X : Fin N → Ω,q (X i) y*q (X j) y ∂ν) =
        if i=j then (∫ x,(q x y)^2 ∂μ) else 0 := by
    by_cases hij : i=j
    · subst j
      simp only [if_pos rfl,←pow_two]
      exact integral_comp_eval (μ := fun _ : Fin N => μ) (i := i) (((hqxm y).pow_const 2).aestronglyMeasurable)
    · rw [if_neg hij]
      have hi : iIndepFun (fun i : Fin N => fun X : Fin N → Ω => q (X i) y) ν :=
        iIndepFun_pi (fun _ => (hqxm y).aemeasurable)
      have hh := (hi.indepFun hij).integral_fun_mul_eq_mul_integral (hqPi y i).aestronglyMeasurable
        (hqPi y j).aestronglyMeasurable
      have hmean (k : Fin N) : (∫ X : Fin N → Ω,q (X k) y ∂ν)=0 :=
        (integral_comp_eval (μ := fun _ : Fin N => μ) (i := k) (hqxm y).aestronglyMeasurable).trans (hm y)
      rw [hmean i,hmean j] at hh
      simpa using hh
  have hvar (y : Ω) : (∫ X : Fin N → Ω,(S X y)^2 ∂ν)≤(N : ℝ)*B^2 := by
    have hs (X : Fin N → Ω) : (S X y)^2=∑ i,∑ j,q (X i) y*q (X j) y := by
      simp only [S,pow_two,Finset.sum_mul_sum]
    simp_rw [hs]
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hpairI y i j))]
    simp_rw [integral_finset_sum _ (fun j _ => hpairI y _ j),hpair]
    simpa using mul_le_mul_of_nonneg_left (hv y) (Nat.cast_nonneg N)
  calc
    _ = ∫ y,∫ X : Fin N → Ω,(S X y)^2 ∂ν ∂μ := by
      rw [←integral_prod _ hSi,integral_prod_symm _ hSi]
    _ ≤ ∫ _ : Ω,(N : ℝ)*B^2 ∂μ :=
      integral_mono_ae hSi.integral_prod_right (integrable_const _)
        (Filter.Eventually.of_forall hvar)
    _ = _ := by simp
