module

public import Tablet.Preamble
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section
open MeasureTheory ProbabilityTheory
universe u
-- [TABLET NODE: IndependentNonnegativeMomentBound]
theorem IndependentNonnegativeMomentBound {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ) (f : Fin N → Ω → ℝ)
    (hf : ∀ i, Measurable (f i)) (A : ℝ) (hA : 0≤A)
    (hn : ∀i x,0≤f i x) (hb : ∀i x,f i x≤A)
    (k : ℕ) (hk : 0<k) (L T : ℝ) (hL : 0≤L) (hT : 0≤T)
    (hroot : (∫X : Fin N → Ω,(∑i,f i (X i))^k ∂Measure.pi (fun _ : Fin N => μ))=L^k)
    (hmoment : (∑i,∫x,(f i x)^k ∂μ)≤T^k) :
    L≤2*Real.exp 1*(∑i,∫x,f i x ∂μ)+2*((k : ℝ)+1)*T := by
-- BODY
  classical
  have power_mean {Λ : Type u} [MeasurableSpace Λ] (ξ : Measure Λ) [IsProbabilityMeasure ξ]
      (g : Λ → ℝ) (hg : Measurable g) (C D : ℝ) (hC : 0≤C) (hD : 0≤D)
      (hgn : ∀x,0≤g x) (hgb : ∀x,g x≤C) (a b : ℕ) (ha : 0<a) (hba : b≤a)
      (hm : (∫x,(g x)^a ∂ξ)≤D^a) : (∫x,(g x)^b ∂ξ)≤D^b := by
    have hap : 0<(a : ℝ) := Nat.cast_pos.mpr ha
    let p : ℝ := (b : ℝ)/(a : ℝ)
    have hp : 0≤p := div_nonneg (Nat.cast_nonneg _) (le_of_lt hap)
    have hp1 : p≤1 := (div_le_one hap).mpr (by exact_mod_cast hba)
    have hid (x : ℝ) (hx : 0≤x) : (x^a)^p=x^b := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hx]
      change x^((a : ℝ)*((b : ℝ)/(a : ℝ)))=x^b
      rw [mul_div_cancel₀ _ (ne_of_gt hap),Real.rpow_natCast]
    have hai : Integrable (fun x => (g x)^a) ξ := by
      apply Integrable.of_bound (hg.pow_const a).aestronglyMeasurable (C^a)
      exact Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (hgn x) _)]
        exact pow_le_pow_left₀ (hgn x) (hgb x) _
    have hbai : Integrable (fun x => ((g x)^a)^p) ξ := by
      simp_rw [hid _ (hgn _)]
      apply Integrable.of_bound (hg.pow_const b).aestronglyMeasurable (C^b)
      exact Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (hgn x) _)]
        exact pow_le_pow_left₀ (hgn x) (hgb x) _
    have hj := (Real.concaveOn_rpow hp hp1).le_map_integral
      (Real.continuous_rpow_const hp).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall fun x => pow_nonneg (hgn x) a) hai hbai
    simp_rw [hid _ (hgn _)] at hj
    calc
      _ ≤ (∫x,(g x)^a ∂ξ)^p := hj
      _ ≤ (D^a)^p := Real.rpow_le_rpow (integral_nonneg fun x => pow_nonneg (hgn x) _) hm hp
      _ = _ := hid D hD
  let ν := Measure.pi (fun _ : Fin N => μ)
  let W (X : Fin N → Ω) := ∑i,f i (X i)
  let R (i : Fin N) (X : Fin N → Ω) := ∑j ∈ Finset.univ.erase i,f j (X j)
  let M := ∑i,∫x,f i x ∂μ
  let C := (N : ℝ)*A
  have hC : 0≤C := mul_nonneg (Nat.cast_nonneg _) hA
  have hWm : Measurable W := Finset.measurable_fun_sum _ (fun i _ => (hf i).comp (measurable_pi_apply i))
  have hRm (i : Fin N) : Measurable (R i) :=
    Finset.measurable_fun_sum _ (fun j _ => (hf j).comp (measurable_pi_apply j))
  have hWn (X : Fin N → Ω) : 0≤W X := Finset.sum_nonneg fun i _ => hn i _
  have hWb (X : Fin N → Ω) : W X≤C := by
    calc
      _ ≤ ∑_ : Fin N,A := Finset.sum_le_sum fun i _ => hb i _
      _ = _ := by simp [C]
  have hRn (i : Fin N) (X : Fin N → Ω) : 0≤R i X := Finset.sum_nonneg fun j _ => hn j _
  have hWR (i : Fin N) (X : Fin N → Ω) : f i (X i)+R i X=W X := by
    dsimp [R,W]
    exact Finset.add_sum_erase (Finset.univ : Finset (Fin N)) (fun j => f j (X j)) (Finset.mem_univ i)
  have hRb (i : Fin N) (X : Fin N → Ω) : R i X≤C := by
    linarith [hWR i X,hWb X,hn i (X i)]
  have hRW (i : Fin N) (X : Fin N → Ω) : R i X≤W X := by
    linarith [hWR i X,hn i (X i)]
  have power_integrable {Λ : Type u} [MeasurableSpace Λ] (ξ : Measure Λ) [IsProbabilityMeasure ξ]
      (g : Λ → ℝ) (hg : Measurable g) (D : ℝ) (hgn : ∀x,0≤g x) (hgb : ∀x,g x≤D) (a : ℕ) :
      Integrable (fun x => (g x)^a) ξ := by
    apply Integrable.of_bound (hg.pow_const a).aestronglyMeasurable (D^a)
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (hgn x) _)]
      exact pow_le_pow_left₀ (hgn x) (hgb x) _
  have hRi (i : Fin N) (a : ℕ) := power_integrable ν (R i) (hRm i) C (hRn i) (hRb i) a
  have hWi (a : ℕ) := power_integrable ν W hWm C hWn hWb a
  have hfPi (i : Fin N) (a : ℕ) := power_integrable ν (fun X => f i (X i))
    ((hf i).comp (measurable_pi_apply i)) A (fun X => hn i _) (fun X => hb i _) a
  have hfi (i : Fin N) (a : ℕ) := power_integrable μ (f i) (hf i) A (hn i) (hb i) a
  have hRmoment (i : Fin N) (a : ℕ) (ha : a≤k) : (∫X,(R i X)^a ∂ν)≤L^a := by
    calc
      _ ≤ ∫X,(W X)^a ∂ν := integral_mono_ae (hRi i a) (hWi a)
        (Filter.Eventually.of_forall fun X => pow_le_pow_left₀ (hRn i X) (hRW i X) a)
      _ ≤ _ := power_mean ν W hWm C L hC hL hWn hWb k a hk ha hroot.le
  have hi : iIndepFun (fun i : Fin N => fun X : Fin N → Ω => f i (X i)) ν :=
    iIndepFun_pi (fun i => (hf i).aemeasurable)
  have hfact (i : Fin N) (a b : ℕ) :
      (∫X,(f i (X i))^a*(R i X)^b ∂ν)=
        (∫x,(f i x)^a ∂μ)*(∫X,(R i X)^b ∂ν) := by
    have hind := (hi.indepFun_finsetSum_of_notMem
      (fun j => (hf j).comp (measurable_pi_apply j)) (by simp : i∉Finset.univ.erase i)).symm
    have heR : (∑j ∈ Finset.univ.erase i,fun X : Fin N → Ω => f j (X j))=R i := by
      funext X
      simp [R,Finset.sum_apply]
    rw [heR] at hind
    have hind' : IndepFun (fun X : Fin N → Ω => f i (X i)) (R i) ν := hind
    have hp : IndepFun (fun X : Fin N → Ω => (f i (X i))^a) (fun X => (R i X)^b) ν := by
      convert hind'.comp (measurable_id.pow_const a) (measurable_id.pow_const b) using 1 <;> funext X <;> rfl
    have hh := hp.integral_fun_mul_eq_mul_integral (hfPi i a).aestronglyMeasurable (hRi i b).aestronglyMeasurable
    rw [integral_comp_eval (μ := fun _ : Fin N => μ) (i := i) ((hf i).pow_const a).aestronglyMeasurable] at hh
    exact hh
  have hM : 0≤M := Finset.sum_nonneg fun i _ => integral_nonneg (hn i)
  by_cases hL0 : L=0
  · subst L
    positivity
  have hLp : 0<L := lt_of_le_of_ne hL (Ne.symm hL0)
  have hkp : 0<(k : ℝ) := Nat.cast_pos.mpr hk
  let d := k-1
  have hdk : d+1=k := Nat.sub_add_cancel hk
  let Q := L/(k : ℝ)
  have hQ : 0<Q := div_pos hLp hkp
  have hsplit (z : ℝ) (hz : 0≤z) (j : ℕ) (hj : j≤d) :
      z^(j+1)≤z*Q^j+z^k/Q^(d-j) := by
    by_cases hzQ : z≤Q
    · calc
        _ = z*z^j := by rw [pow_succ];ring
        _ ≤ z*Q^j := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz hzQ j) hz
        _ ≤ _ := le_add_of_nonneg_right (div_nonneg (pow_nonneg hz _) (le_of_lt (pow_pos hQ _)))
    · have hQz : Q≤z := le_of_not_ge hzQ
      have hpow := pow_le_pow_left₀ (le_of_lt hQ) hQz (d-j)
      have he : z^k=z^(j+1)*z^(d-j) := by rw [←pow_add];congr 1;omega
      have hh : z^(j+1)*Q^(d-j)≤z^k := by
        rw [he]
        exact mul_le_mul_of_nonneg_left hpow (pow_nonneg hz _)
      have hzterm := (le_div_iff₀ (pow_pos hQ (d-j))).mpr hh
      exact hzterm.trans (le_add_of_nonneg_left (mul_nonneg hz (pow_nonneg (le_of_lt hQ) _)))
  have hpI (i : Fin N) (a b : ℕ) : Integrable (fun X => (f i (X i))^a*(R i X)^b) ν := by
    apply Integrable.of_bound ((((hf i).comp (measurable_pi_apply i)).pow_const a).mul
      ((hRm i).pow_const b)).aestronglyMeasurable (A^a*C^b)
    exact Filter.Eventually.of_forall fun X => by
      change ‖(f i (X i))^a*(R i X)^b‖≤A^a*C^b
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (pow_nonneg (hn i _) _) (pow_nonneg (hRn i _) _))]
      exact mul_le_mul (pow_le_pow_left₀ (hn i _) (hb i _) _)
        (pow_le_pow_left₀ (hRn i _) (hRb i _) _) (pow_nonneg (hRn i _) _) (pow_nonneg hA _)
  have hfi1 (i : Fin N) : Integrable (f i) μ := by simpa only [pow_one] using hfi i 1
  have hfj (i : Fin N) (j : ℕ) (hj : j≤d) :
      (∫x,(f i x)^(j+1) ∂μ)≤(∫x,f i x ∂μ)*Q^j+(∫x,(f i x)^k ∂μ)/Q^(d-j) := by
    calc
      _ ≤ ∫x,f i x*Q^j+(f i x)^k/Q^(d-j) ∂μ :=
        integral_mono_ae (hfi i (j+1)) (((hfi1 i).mul_const _).add ((hfi i k).div_const _))
          (Filter.Eventually.of_forall fun x => hsplit _ (hn i x) j hj)
      _ = _ := by rw [integral_add ((hfi1 i).mul_const _) ((hfi i k).div_const _),integral_mul_const,integral_div]
  have hterm (i : Fin N) (j : ℕ) (hj : j≤d) :
      (∫X,(f i (X i))^(j+1)*(R i X)^(d-j) ∂ν)≤
      ((∫x,f i x ∂μ)*Q^j+(∫x,(f i x)^k ∂μ)/Q^(d-j))*L^(d-j) := by
    rw [hfact]
    exact mul_le_mul (hfj i j hj) (hRmoment i (d-j) (by omega))
      (integral_nonneg fun X => pow_nonneg (hRn i X) _)
      (add_nonneg (mul_nonneg (integral_nonneg (hn i)) (pow_nonneg (le_of_lt hQ) _))
        (div_nonneg (integral_nonneg fun x => pow_nonneg (hn i x) _) (le_of_lt (pow_pos hQ _))))
  have hpoint (X : Fin N → Ω) : (W X)^k=
      ∑i,∑j ∈ Finset.range (d+1),((d.choose j : ℝ)*((f i (X i))^(j+1)*(R i X)^(d-j))) := by
    rw [←hdk,pow_succ]
    conv_lhs => rhs;dsimp [W]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [←hWR i X,add_pow,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [pow_succ]
    ring
  have hrec : L^k≤M*(Q+L)^d+T^k*((k : ℝ)+1)^d := by
    calc
      _ = ∫X,(W X)^k ∂ν := hroot.symm
      _ = ∑i,∑j ∈ Finset.range (d+1),(d.choose j : ℝ)*
          (∫X,(f i (X i))^(j+1)*(R i X)^(d-j) ∂ν) := by
        simp_rw [hpoint]
        rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => (hpI i (j+1) (d-j)).const_mul _))]
        simp_rw [integral_finset_sum _ (fun j _ => (hpI _ (j+1) (d-j)).const_mul _)]
        simp_rw [integral_const_mul]
      _ ≤ ∑i,∑j ∈ Finset.range (d+1),(d.choose j : ℝ)*
          (((∫x,f i x ∂μ)*Q^j+(∫x,(f i x)^k ∂μ)/Q^(d-j))*L^(d-j)) :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj =>
          mul_le_mul_of_nonneg_left (hterm i j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))) (Nat.cast_nonneg _)
      _ = ∑j ∈ Finset.range (d+1),(d.choose j : ℝ)*
          ((M*Q^j+(∑i,∫x,(f i x)^k ∂μ)/Q^(d-j))*L^(d-j)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [mul_add,add_mul,Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum,Finset.sum_div,M]
      _ ≤ ∑j ∈ Finset.range (d+1),(d.choose j : ℝ)*
          ((M*Q^j+T^k/Q^(d-j))*L^(d-j)) := by
        apply Finset.sum_le_sum
        intro j hj
        apply mul_le_mul_of_nonneg_left
        apply mul_le_mul_of_nonneg_right
        · exact add_le_add_right (div_le_div_of_nonneg_right hmoment (le_of_lt (pow_pos hQ _))) _
        · positivity
        · positivity
      _ = _ := by
        have hratio : L/Q=(k : ℝ) := by dsimp [Q];field_simp
        have hquot (j : ℕ) : T^k/Q^(d-j)*L^(d-j)=T^k*(k : ℝ)^(d-j) := by
          calc
            _ = T^k*(L^(d-j)/Q^(d-j)) := by ring
            _ = _ := by rw [←div_pow,hratio]
        have hterm' (j : ℕ) : (d.choose j : ℝ)*((M*Q^j+T^k/Q^(d-j))*L^(d-j)) =
            M*(Q^j*L^(d-j)*(d.choose j : ℝ))+T^k*((1 : ℝ)^j*(k : ℝ)^(d-j)*(d.choose j : ℝ)) := by
          calc
            _ = M*(Q^j*L^(d-j)*(d.choose j : ℝ))+(d.choose j : ℝ)*(T^k/Q^(d-j)*L^(d-j)) := by ring
            _ = _ := by rw [hquot];ring
        simp_rw [hterm',Finset.sum_add_distrib,←Finset.mul_sum,←add_pow]
        rw [add_comm (1 : ℝ)]
  have he : (1+1/(k : ℝ))^d≤Real.exp 1 := by
    calc
      _ ≤ (Real.exp (1/(k : ℝ)))^d := pow_le_pow_left₀ (by positivity) (by simpa only [add_comm] using Real.add_one_le_exp (1/(k : ℝ))) _
      _ = Real.exp ((d : ℝ)/(k : ℝ)) := by rw [←Real.exp_nat_mul];congr 1;ring
      _ ≤ _ := Real.exp_le_exp.mpr ((div_le_one hkp).mpr (by exact_mod_cast Nat.sub_le k 1))
  have hrec' : L^k≤Real.exp 1*M*L^d+((k : ℝ)+1)^d*T^k := by
    have heq : Q+L=L*(1+1/(k : ℝ)) := by dsimp [Q];ring
    rw [heq,mul_pow] at hrec
    calc
      _ ≤ _ := hrec
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left he (mul_nonneg hM (pow_nonneg hL d))
        calc
          _ = (M*L^d)*(1+1/(k : ℝ))^d+T^k*((k : ℝ)+1)^d := by ring
          _ ≤ (M*L^d)*Real.exp 1+T^k*((k : ℝ)+1)^d := add_le_add hh (le_refl _)
          _ = _ := by ring
  by_cases hsmall : L≤2*Real.exp 1*M
  · exact hsmall.trans (le_add_of_nonneg_right (by positivity))
  have hbig : 2*Real.exp 1*M<L := lt_of_not_ge hsmall
  have hhalf : Real.exp 1*M*L^d≤L^k/2 := by
    have hh := mul_le_mul_of_nonneg_right (le_of_lt hbig) (pow_nonneg hL d)
    rw [←hdk,pow_succ]
    nlinarith
  have hpower : L^k≤(2*((k : ℝ)+1)*T)^k := by
    have hh : L^k≤2*((k : ℝ)+1)^d*T^k := by linarith [hrec']
    calc
      _ ≤ _ := hh
      _ ≤ _ := by
        rw [mul_pow,mul_pow]
        have h2 : (2 : ℝ)≤2^k := by
          have hh := pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2) (show 1≤k from hk)
          simpa using hh
        have hkk : ((k : ℝ)+1)^d≤((k : ℝ)+1)^k :=
          pow_le_pow_right₀ (show (1 : ℝ)≤(k : ℝ)+1 from le_add_of_nonneg_left (Nat.cast_nonneg k)) (Nat.sub_le k 1)
        exact mul_le_mul_of_nonneg_right (mul_le_mul h2 hkk (by positivity) (by positivity)) (by positivity)
  have hlinear : L≤2*((k : ℝ)+1)*T := by
    by_contra hh
    have hlt := pow_lt_pow_left₀ (lt_of_not_ge hh) (by positivity : 0≤2*((k : ℝ)+1)*T) (Nat.ne_of_gt hk)
    linarith
  exact hlinear.trans (le_add_of_nonneg_left (by positivity))
