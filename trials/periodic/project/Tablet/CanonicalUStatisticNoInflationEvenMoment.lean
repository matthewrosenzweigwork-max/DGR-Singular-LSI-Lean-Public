module

public import Tablet.CanonicalCrossNoInflationEvenMoment
public import Tablet.IndependentBernsteinMoments
public import Tablet.CanonicalConvexDecoupling
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section
open MeasureTheory
universe u
-- [TABLET NODE: CanonicalUStatisticNoInflationEvenMoment]
theorem CanonicalUStatisticNoInflationEvenMoment {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ) (hN : 0<N)
    (q : Ω → Ω → ℝ) (hq : Measurable (fun v : Ω × Ω => q v.1 v.2))
    (A B : ℝ) (hA : 0<A) (hB : 0<B) (hb : ∀x y,|q x y|≤A)
    (hc : ∀x,(∫y,q x y ∂μ)=0) (hc' : ∀y,(∫x,q x y ∂μ)=0)
    (hv : ∀x,(∫y,(q x y)^2 ∂μ)≤B^2) (hv' : ∀y,(∫x,(q x y)^2 ∂μ)≤B^2)
    (m : ℕ) (hm : 1≤m) :
    (∫X : Fin N → Ω,((∑i,∑j,if i=j then 0 else q (X i) (X j))/(N:ℝ))^(2*m)
      ∂Measure.pi (fun _ : Fin N => μ)) ≤
      (1000000000*((m:ℝ)^2*B^2+(m:ℝ)^3*B^2/(N:ℝ)+(m:ℝ)^4*A^2/(N:ℝ)^2))^m := by
-- BODY
  classical
  have bi {Λ : Type u} [MeasurableSpace Λ] (ξ : Measure Λ) [IsProbabilityMeasure ξ]
      (f : Λ → ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀x,|f x|≤C) : Integrable f ξ := by
    apply Integrable.of_bound hf.aestronglyMeasurable C
    exact Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x
  let ν := Measure.pi (fun _ : Fin N => μ)
  let ξ := ν.prod ν
  let L (v : (Fin N → Ω) × (Fin N → Ω)) := ∑i,∑j,q (v.1 i) (v.2 j)
  let D (v : (Fin N → Ω) × (Fin N → Ω)) := ∑i,q (v.1 i) (v.2 i)
  let O (v : (Fin N → Ω) × (Fin N → Ω)) := L v-D v
  let R := 6*(2*(m:ℝ)*A+Real.sqrt (2*(m:ℝ)*(N:ℝ)*B^2))
  let Z:=(m:ℝ)^2*(N:ℝ)^2*B^2+(m:ℝ)^3*(N:ℝ)*B^2+(m:ℝ)^4*A^2
  let C := 4*(139968*Real.exp 1+6144*(24*Real.exp 1+192))*Z
  let U (X : Fin N → Ω) := ∑i,∑j,if i=j then (0:ℝ) else q (X i) (X j)
  have hLm : Measurable L := by
    apply Finset.measurable_fun_sum; intro i hi
    apply Finset.measurable_fun_sum; intro j hj
    have hp : Measurable (fun v : (Fin N → Ω) × (Fin N → Ω) => (v.1 i,v.2 j)) :=
      ((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply j).comp measurable_snd)
    exact hq.comp hp
  have hDm : Measurable D := by
    apply Finset.measurable_fun_sum; intro i hi
    have hp : Measurable (fun v : (Fin N → Ω) × (Fin N → Ω) => (v.1 i,v.2 i)) :=
      ((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd)
    exact hq.comp hp
  have hLb (v : (Fin N → Ω) × (Fin N → Ω)) : |L v|≤(N:ℝ)^2*A := by
    calc
      _ ≤ ∑i,|∑j,q (v.1 i) (v.2 j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑_ : Fin N,(N:ℝ)*A := Finset.sum_le_sum fun i _ => by
        calc
          _ ≤ ∑j,|q (v.1 i) (v.2 j)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑_ : Fin N,A := Finset.sum_le_sum fun j _ => hb _ _
          _ = _ := by simp
      _ = _ := by simp; ring
  have hDb (v : (Fin N → Ω) × (Fin N → Ω)) : |D v|≤(N:ℝ)*A := by
    calc
      _ ≤ ∑i,|q (v.1 i) (v.2 i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑_ : Fin N,A := Finset.sum_le_sum fun i _ => hb _ _
      _ = _ := by simp
  have hLi : Integrable (fun v => (L v)^(2*m)) ξ := bi ξ _ (hLm.pow_const _) (((N:ℝ)^2*A)^(2*m))
    (fun v => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hLb v) _)
  have hDi : Integrable (fun v => (D v)^(2*m)) ξ := bi ξ _ (hDm.pow_const _) (((N:ℝ)*A)^(2*m))
    (fun v => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hDb v) _)
  have hOi : Integrable (fun v => (O v)^(2*m)) ξ :=
    bi ξ _ ((hLm.sub hDm).pow_const _) (((N:ℝ)^2*A+(N:ℝ)*A)^(2*m)) (fun v => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (add_le_add (hLb v) (hDb v))) _)
  have hqm : Measurable (fun v : Ω × Ω => q v.1 v.2) := hq
  have hqi : Integrable (fun v : Ω × Ω => q v.1 v.2) (μ.prod μ) := bi (μ.prod μ) _ hq A (fun v => hb _ _)
  have hq2i : Integrable (fun v : Ω × Ω => (q v.1 v.2)^2) (μ.prod μ) :=
    bi (μ.prod μ) _ (hq.pow_const 2) (A^2) (fun v => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hb _ _) _)
  have hqmean : (∫v : Ω × Ω,q v.1 v.2 ∂μ.prod μ)=0 := by
    rw [integral_prod _ hqi]; simp_rw [hc]; simp
  have hqvar : (∫v : Ω × Ω,(q v.1 v.2)^2 ∂μ.prod μ)≤B^2 := by
    rw [integral_prod _ hq2i]
    calc
      _ ≤ ∫_ : Ω,B^2 ∂μ := integral_mono hq2i.integral_prod_left (integrable_const _) hv
      _ = _ := by simp
  have hdiag : (∫v,(D v)^(2*m) ∂ξ)≤R^(2*m) := by
    let E := MeasurableEquiv.arrowProdEquivProdArrow Ω Ω (Fin N)
    have hmp := measurePreserving_arrowProdEquivProdArrow Ω Ω (Fin N)
      (fun _ : Fin N => μ) (fun _ : Fin N => μ)
    have hmap := hmp.integral_comp E.measurableEmbedding (fun v => (D v)^(2*m))
    have hpres : (∫v,(D v)^(2*m) ∂ξ)=
        ∫w : Fin N → Ω × Ω,(∑i,q (w i).1 (w i).2)^(2*m)
          ∂Measure.pi (fun _ : Fin N => μ.prod μ) := by
      have he (w : Fin N → Ω × Ω) : D (E w)=∑i,q (w i).1 (w i).2 := rfl
      change (∫w : Fin N → Ω × Ω,(D (E w))^(2*m) ∂Measure.pi (fun _ : Fin N => μ.prod μ))=(∫v,(D v)^(2*m) ∂ξ) at hmap
      simp_rw [he] at hmap
      exact hmap.symm
    rw [hpres]
    have hh := IndependentBernsteinMoments (μ.prod μ) N (fun _ : Fin N => fun v : Ω × Ω => q v.1 v.2)
      (fun _ => hq) A (B^2) hA (sq_nonneg _) (fun _ v => hb _ _) (fun _ => hqmean)
      (fun _ => hqvar) (2*m) (by omega)
    have hp (x : ℝ) : |x|^(2*m)=x^(2*m) := by rw [pow_mul,sq_abs,←pow_mul]
    simpa only [hp,Nat.cast_mul,Nat.cast_ofNat,R] using hh
  have hcross : (∫v,(L v)^(2*m) ∂ξ)≤C^m := CanonicalCrossNoInflationEvenMoment μ N hN q hq A B hA hB hb hc hc' hv hv' m hm
  have hev : Even (2*m) := even_two_mul m
  have hOpoint (v : (Fin N → Ω) × (Fin N → Ω)) :
      (O v)^(2*m)≤(4:ℝ)^m*((L v)^(2*m)+(D v)^(2*m)) := by
    have hh := hev.add_pow_le (a:=L v) (b:=-(D v))
    have hp : (2:ℝ)^(2*m-1)≤(2:ℝ)^(2*m) := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
    have h4 : (2:ℝ)^(2*m)=(4:ℝ)^m := by rw [pow_mul]; norm_num
    have hn := add_nonneg (hev.pow_nonneg (L v)) (hev.pow_nonneg (D v))
    have hs := hh.trans (mul_le_mul_of_nonneg_right hp (by simpa only [hev.neg_pow] using hn))
    simpa only [O,sub_eq_add_neg,hev.neg_pow,h4] using hs
  have hOff : (∫v,(O v)^(2*m) ∂ξ)≤(4*(C+R^2))^m := by
    calc
      _ ≤ ∫v,(4:ℝ)^m*((L v)^(2*m)+(D v)^(2*m)) ∂ξ :=
        integral_mono hOi ((hLi.add hDi).const_mul _) hOpoint
      _ = (4:ℝ)^m*((∫v,(L v)^(2*m) ∂ξ)+(∫v,(D v)^(2*m) ∂ξ)) := by
        rw [integral_const_mul,integral_add hLi hDi]
      _ ≤ (4:ℝ)^m*(C^m+R^(2*m)) := mul_le_mul_of_nonneg_left (add_le_add hcross hdiag) (by positivity)
      _ ≤ (4:ℝ)^m*(C+R^2)^m := by
        rw [pow_mul]
        exact mul_le_mul_of_nonneg_left (pow_add_pow_le (by dsimp [C]; positivity) (sq_nonneg _) (by omega)) (by positivity)
      _ = _ := (mul_pow _ _ _).symm
  have hoff (v : (Fin N → Ω) × (Fin N → Ω)) :
      (∑i,∑j,if i=j then (0:ℝ) else q (v.1 i) (v.2 j))=O v := by
    dsimp [O,L,D]
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hd : (∑j : Fin N,if i=j then q (v.1 i) (v.2 j) else 0)=q (v.1 i) (v.2 i) := by simp
    rw [←hd,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> ring
  have hdec := CanonicalConvexDecoupling μ N q hq A hA.le hb hc' hc 1
    (fun z : ℝ => z^(2*m)) hev.convexOn_pow (continuous_id.pow _)
  simp only [one_mul] at hdec
  simp_rw [hoff,mul_pow] at hdec
  rw [integral_const_mul] at hdec
  have h16 : (4:ℝ)^(2*m)=(16:ℝ)^m := by rw [pow_mul]; norm_num
  rw [h16] at hdec
  have hraw : (∫X,(U X)^(2*m) ∂ν)≤(64*(C+R^2))^m := by
    calc
      _ ≤ (16:ℝ)^m*(∫v,(O v)^(2*m) ∂ξ) := by simpa only [one_pow,mul_one] using hdec
      _ ≤ (16:ℝ)^m*(4*(C+R^2))^m := mul_le_mul_of_nonneg_left hOff (by positivity)
      _ = _ := by rw [←mul_pow]; congr 1; ring
  have hNR : 1≤(N:ℝ) := by exact_mod_cast (show 1≤N by omega)
  have hmR : 1≤(m:ℝ) := by exact_mod_cast hm
  have hNpos : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hmpos : 0<(m:ℝ) := by linarith
  have hRsq : R^2≤288*(m:ℝ)^2*A^2+144*(m:ℝ)*(N:ℝ)*B^2 := by
    have hs:=add_sq_le (a:=2*(m:ℝ)*A) (b:=Real.sqrt (2*(m:ℝ)*(N:ℝ)*B^2))
    rw[Real.sq_sqrt (by positivity)] at hs
    dsimp[R]
    nlinarith
  have hZn : 0≤Z := by dsimp[Z];positivity
  have hcoef : 4*(139968*Real.exp 1+6144*(24*Real.exp 1+192))≤10000000 := by
    nlinarith[Real.exp_one_lt_three]
  have hCbase : C≤10000000*Z := mul_le_mul_of_nonneg_right hcoef hZn
  have hm4 : (m:ℝ)^2≤(m:ℝ)^4 := pow_le_pow_right₀ hmR (by norm_num)
  have hmN : (m:ℝ)*(N:ℝ)≤(m:ℝ)^2*(N:ℝ)^2 := by
    have h1:=one_le_mul_of_one_le_of_one_le hmR hNR
    have h2 : (m:ℝ)*(N:ℝ)≤((m:ℝ)*(N:ℝ))^2 := by nlinarith
    simpa only[mul_pow] using h2
  have hdiagbase : R^2≤288*Z := by
    have hAineq:=mul_le_mul_of_nonneg_right hm4 (sq_nonneg A)
    have hBineq:=mul_le_mul_of_nonneg_right hmN (sq_nonneg B)
    have hmiddle : 0≤(m:ℝ)^3*(N:ℝ)*B^2 := by positivity
    have hfirst : 0≤(m:ℝ)^2*(N:ℝ)^2*B^2 := by positivity
    dsimp[Z]
    nlinarith only[hRsq,hAineq,hBineq,hmiddle,hfirst]
  have hbase : 64*(C+R^2)≤1000000000*Z := by nlinarith[hCbase,hdiagbase,hZn]
  have hdivide : 64*(C+R^2)/(N:ℝ)^2≤
      1000000000*((m:ℝ)^2*B^2+(m:ℝ)^3*B^2/(N:ℝ)+(m:ℝ)^4*A^2/(N:ℝ)^2) := by
    rw[div_le_iff₀ (sq_pos_of_pos hNpos)]
    have he : (1000000000*((m:ℝ)^2*B^2+(m:ℝ)^3*B^2/(N:ℝ)+(m:ℝ)^4*A^2/(N:ℝ)^2))*(N:ℝ)^2=
        1000000000*Z := by dsimp[Z];field_simp
    rw[he]
    exact hbase
  calc
    _=(∫X,(U X)^(2*m) ∂ν)/(N:ℝ)^(2*m) := by simp_rw[div_pow];rw[integral_div]
    _≤(64*(C+R^2))^m/(N:ℝ)^(2*m) := div_le_div_of_nonneg_right hraw (by positivity)
    _=(64*(C+R^2)/(N:ℝ)^2)^m := by rw[pow_mul,div_pow]
    _≤_ := pow_le_pow_left₀ (by dsimp[C,Z];positivity) hdivide _
