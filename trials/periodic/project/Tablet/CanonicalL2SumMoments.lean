import Tablet.CanonicalL2SumConcentration
import Tablet.CanonicalL2SumVariance
import Tablet.MomentFromExponential
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
open MeasureTheory
-- [TABLET NODE: CanonicalL2SumMoments]
theorem CanonicalL2SumMoments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ)
    (q : Ω → Ω → ℝ) (hq : Measurable (fun p : Ω × Ω => q p.1 p.2))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hb : ∀ x y,|q x y|≤A)
    (hm : ∀ y,(∫ x,q x y ∂μ)=0)
    (hv : ∀ x,(∫ y,(q x y)^2 ∂μ)≤B^2)
    (hv' : ∀ y,(∫ x,(q x y)^2 ∂μ)≤B^2)
    (ℓ : ℝ) (hℓ : 0<ℓ) (n : ℕ) :
    (∫ X : Fin N → Ω,(Real.sqrt (∫ y,(∑ i,q (X i) y)^2 ∂μ))^n
        ∂Measure.pi (fun _ : Fin N => μ)) ≤
      2^n*((Real.sqrt (N : ℝ)*B)^n+(n.factorial : ℝ)/ℓ^n *
        (2*Real.exp (2*(N : ℝ)*B^2*ℓ^2))) := by
-- BODY
  classical
  let ν := Measure.pi (fun _ : Fin N => μ)
  let S (X : Fin N → Ω) (y : Ω) := ∑ i,q (X i) y
  let F (X : Fin N → Ω) := Real.sqrt (∫ y,(S X y)^2 ∂μ)
  let m := ∫ X,F X ∂ν
  let C := (N : ℝ)*A
  have hC : 0≤C := mul_nonneg (Nat.cast_nonneg _) hA
  have hSb (X : Fin N → Ω) (y : Ω) : |S X y|≤C := by
    calc
      _ ≤ ∑ i,|q (X i) y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin N,A := Finset.sum_le_sum (fun i _ => hb _ _)
      _ = _ := by simp [C]
  have hSm : Measurable (fun p : (Fin N → Ω) × Ω => (S p.1 p.2)^2) := by
    apply Measurable.pow_const
    apply Finset.measurable_fun_sum
    intro i hi
    have hp : Measurable (fun p : (Fin N → Ω) × Ω => (p.1 i,p.2)) :=
      ((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd
    exact hq.comp hp
  have hFm : Measurable F := Real.continuous_sqrt.measurable.comp
    hSm.stronglyMeasurable.integral_prod_right'.measurable
  have hSqI (X : Fin N → Ω) : Integrable (fun y => (S X y)^2) μ := by
    apply Integrable.of_bound (hSm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable (C^2)
    exact Filter.Eventually.of_forall fun y => by
      change ‖(S X y)^2‖≤C^2
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      nlinarith [abs_le.mp (hSb X y)]
  have hFn (X : Fin N → Ω) : 0≤F X := Real.sqrt_nonneg _
  have hFb (X : Fin N → Ω) : |F X|≤C := by
    rw [abs_of_nonneg (hFn X)]
    apply Real.sqrt_le_iff.mpr
    refine ⟨hC,?_⟩
    calc
      _ ≤ ∫ _ : Ω,C^2 ∂μ := integral_mono_ae (hSqI X) (integrable_const _)
        (Filter.Eventually.of_forall fun y => by nlinarith [abs_le.mp (hSb X y)])
      _ = _ := by simp
  have hFL : MemLp F 2 ν := MemLp.of_bound hFm.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun X => by simpa only [Real.norm_eq_abs] using hFb X)
  have hFi : Integrable F ν := Integrable.of_bound hFm.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun X => by simpa only [Real.norm_eq_abs] using hFb X)
  have hFni : Integrable (fun X => (F X)^n) ν := Integrable.of_bound (hFm.pow_const n).aestronglyMeasurable (C^n)
    (Filter.Eventually.of_forall fun X => by
      change ‖(F X)^n‖≤C^n
      rw [Real.norm_eq_abs,abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hFb X) _)
  have hFv : (∫ X,(F X)^2 ∂ν)≤(N : ℝ)*B^2 := by
    have hh := CanonicalL2SumVariance μ N q hq A B hA hB hb hm hv'
    have he (X : Fin N → Ω) : (F X)^2=∫ y,(S X y)^2 ∂μ :=
      Real.sq_sqrt (integral_nonneg fun y => sq_nonneg _)
    simpa only [F,S,ν,Real.sq_sqrt (integral_nonneg fun y => sq_nonneg _)] using hh
  have hmn : 0≤m := integral_nonneg hFn
  have hmean : m≤Real.sqrt (N : ℝ)*B := by
    have hc : ConvexOn ℝ Set.univ (fun x : ℝ => x^2) := (by decide : Even (2 : ℕ)).convexOn_pow
    have hh := hc.map_integral_le (continuous_id.pow 2).continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hFi hFL.integrable_sq
    have hs : (Real.sqrt (N : ℝ)*B)^2=(N : ℝ)*B^2 := by
      rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg N)]
    have hpos : 0≤Real.sqrt (N : ℝ)*B := mul_nonneg (Real.sqrt_nonneg _) hB
    change m^2≤_ at hh
    nlinarith
  have hexpi (θ : ℝ) : Integrable (fun X => Real.exp (θ*(F X-m))) ν := by
    apply Integrable.of_bound ((hFm.sub_const m).const_mul θ).exp.aestronglyMeasurable
      (Real.exp (|θ| * (C+|m|)))
    exact Filter.Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      exact (le_abs_self _).trans (by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add_left (hFb X) _)) (abs_nonneg _))
  have hbound (θ : ℝ) : (∫ X,Real.exp (θ*(F X-m)) ∂ν)≤Real.exp (2*(N : ℝ)*B^2*θ^2) :=
    CanonicalL2SumConcentration μ N q hq A B hA hB hb hv θ
  have hmom := MomentFromExponential ν (fun X => F X-m) (hFm.sub_const m) ℓ hℓ n
    (hexpi ℓ) (by simpa only [neg_mul] using hexpi (-ℓ))
  have hGbound : (∫ X,|F X-m|^n ∂ν)≤(n.factorial : ℝ)/ℓ^n*(2*Real.exp (2*(N : ℝ)*B^2*ℓ^2)) := by
    calc
      _ ≤ _ := hmom.2
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by simpa only [neg_sq,two_mul] using add_le_add (hbound ℓ) (hbound (-ℓ)))
        (div_nonneg (Nat.cast_nonneg _) (le_of_lt (pow_pos hℓ n)))
  have hp (X : Fin N → Ω) : (F X)^n ≤ 2^n*((Real.sqrt (N : ℝ)*B)^n+|F X-m|^n) := by
    have hh : F X≤Real.sqrt (N : ℝ)*B+|F X-m| := by linarith [le_abs_self (F X-m)]
    calc
      _ ≤ (Real.sqrt (N : ℝ)*B+|F X-m|)^n := pow_le_pow_left₀ (hFn X) hh _
      _ ≤ 2^(n-1)*((Real.sqrt (N : ℝ)*B)^n+|F X-m|^n) :=
        add_pow_le (mul_nonneg (Real.sqrt_nonneg _) hB) (abs_nonneg _) n
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2) (Nat.sub_le n 1)) (by positivity)
  calc
    _ ≤ ∫ X,2^n*((Real.sqrt (N : ℝ)*B)^n+|F X-m|^n) ∂ν :=
      integral_mono_ae hFni (((integrable_const _).add hmom.1).const_mul _)
        (Filter.Eventually.of_forall hp)
    _ = 2^n*((Real.sqrt (N : ℝ)*B)^n+∫ X,|F X-m|^n ∂ν) := by
      rw [integral_const_mul,integral_add (integrable_const _) hmom.1];simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add_right hGbound _) (by positivity)
