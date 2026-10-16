module

public import Tablet.IndependentRosenthalEvenMoment
public import Tablet.GLZSecondConditionalRosenthal
public import Tablet.CanonicalL2SumMoments
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.Nat.Factorial.Basic

@[expose] public section
open MeasureTheory
universe u
-- [TABLET NODE: CanonicalCrossNoInflationEvenMoment]
theorem CanonicalCrossNoInflationEvenMoment {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ) (hN : 0<N)
    (q : Ω → Ω → ℝ) (hq : Measurable (fun v : Ω × Ω => q v.1 v.2))
    (A B : ℝ) (hA : 0<A) (hB : 0<B) (hb : ∀x y,|q x y|≤A)
    (hc : ∀x,(∫y,q x y ∂μ)=0) (hc' : ∀y,(∫x,q x y ∂μ)=0)
    (hv : ∀x,(∫y,(q x y)^2 ∂μ)≤B^2) (hv' : ∀y,(∫x,(q x y)^2 ∂μ)≤B^2)
    (m : ℕ) (hm : 1≤m) :
    (∫v : (Fin N → Ω) × (Fin N → Ω),(∑i,∑j,q (v.1 i) (v.2 j))^(2*m)
      ∂(Measure.pi (fun _ : Fin N => μ)).prod (Measure.pi (fun _ : Fin N => μ))) ≤
      (4*(139968*Real.exp 1+6144*(24*Real.exp 1+192))*
        ((m:ℝ)^2*(N:ℝ)^2*B^2+(m:ℝ)^3*(N:ℝ)*B^2+(m:ℝ)^4*A^2))^m := by
-- BODY
  have optimized_l2_moment
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ) (hN : 0<N)
    (q : Ω → Ω → ℝ) (hq : Measurable (fun p : Ω × Ω => q p.1 p.2))
    (A B : ℝ) (hA : 0≤A) (hB : 0<B) (hb : ∀x y,|q x y|≤A)
    (hm : ∀y,(∫x,q x y ∂μ)=0)
    (hv : ∀x,(∫y,(q x y)^2 ∂μ)≤B^2)
    (hv' : ∀y,(∫x,(q x y)^2 ∂μ)≤B^2) (n : ℕ) (hn : 1≤n) :
    (∫X : Fin N → Ω,(Real.sqrt (∫y,(∑i,q (X i) y)^2 ∂μ))^n
      ∂Measure.pi (fun _ : Fin N => μ)) ≤
      (54*Real.sqrt (n:ℝ)*Real.sqrt (N:ℝ)*B)^n := by
    let b := Real.sqrt (N:ℝ)*B
    let p := Real.sqrt (n:ℝ)
    let ℓ := p/b
    have hNR : 0<(N:ℝ) := Nat.cast_pos.mpr hN
    have hnR : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
    have hbp : 0<b := mul_pos (Real.sqrt_pos.mpr hNR) hB
    have hpp : 0<p := Real.sqrt_pos.mpr hnR
    have hℓp : 0<ℓ := div_pos hpp hbp
    have hbsq : b^2=(N:ℝ)*B^2 := by dsimp [b]; rw [mul_pow,Real.sq_sqrt hNR.le]
    have hpsq : p^2=(n:ℝ) := Real.sq_sqrt hnR.le
    have hℓvar : 2*(N:ℝ)*B^2*ℓ^2=2*(n:ℝ) := by
      change 2*(N:ℝ)*B^2*(p/b)^2=2*(n:ℝ)
      calc
        _=2*b^2*(p^2/b^2) := by rw [div_pow,hbsq]; ring
        _=2*(n:ℝ) := by rw [hpsq]; field_simp
    have hratio : (n:ℝ)/ℓ=p*b := by
      dsimp [ℓ]; rw [div_div_eq_mul_div,←hpsq]
      field_simp
    have hp1 : 1≤p := by
      dsimp [p]; exact Real.one_le_sqrt.mpr (by exact_mod_cast hn)
    have hmain := CanonicalL2SumMoments μ N q hq A B hA hB.le hb hm hv hv' ℓ hℓp n
    have hfac : (n.factorial:ℝ)≤(n:ℝ)^n := by exact_mod_cast Nat.factorial_le_pow n
    have hfact : (n.factorial:ℝ)/ℓ^n≤(p*b)^n := by
      calc
        _ ≤ (n:ℝ)^n/ℓ^n := div_le_div_of_nonneg_right hfac (by positivity)
        _ = _ := by rw [←div_pow,hratio]
    have hexp : Real.exp (2*(n:ℝ))≤(9:ℝ)^n := by
      calc
        _ = (Real.exp 2)^n := by rw [mul_comm]; exact Real.exp_nat_mul 2 n
        _ ≤ (9:ℝ)^n := by
          apply pow_le_pow_left₀ (Real.exp_pos _).le
          calc
            _ = (Real.exp 1)^2 := by rw [←Real.exp_nat_mul]; norm_num
            _ ≤ (3:ℝ)^2 := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le 2
            _ = _ := by norm_num
    have hbpow : b^n≤(p*b)^n := pow_le_pow_left₀ hbp.le (by nlinarith) _
    have h9 : (1:ℝ)≤(9:ℝ)^n := one_le_pow₀ (by norm_num)
    have h3 : (3:ℝ)≤(3:ℝ)^n := by simpa using pow_le_pow_right₀ (a:=(3:ℝ)) (by norm_num) hn
    calc
      _ ≤ 2^n*(b^n+(n.factorial:ℝ)/ℓ^n*(2*Real.exp (2*(n:ℝ)))) := by simpa only [hℓvar] using hmain
      _ ≤ 2^n*((p*b)^n+(p*b)^n*(2*(9:ℝ)^n)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply add_le_add hbpow
        exact mul_le_mul hfact (mul_le_mul_of_nonneg_left hexp (by norm_num)) (by positivity) (by positivity)
      _ ≤ 2^n*(3*(9:ℝ)^n*(p*b)^n) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [mul_le_mul_of_nonneg_right h9 (pow_nonneg (mul_nonneg hpp.le hbp.le) n)]
      _ ≤ 2^n*((3:ℝ)^n*(9:ℝ)^n*(p*b)^n) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 (by positivity)) (by positivity)
      _ = _ := by
        rw [←mul_pow,←mul_pow,←mul_pow]
        congr 1
        dsimp [p,b]; ring

  classical
  have bi {Λ : Type u} [MeasurableSpace Λ] (ξ : Measure Λ) [IsProbabilityMeasure ξ]
      (f : Λ → ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀x,|f x|≤C) : Integrable f ξ := by
    apply Integrable.of_bound hf.aestronglyMeasurable C
    exact Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x
  let ν := Measure.pi (fun _ : Fin N => μ)
  let S (X : Fin N → Ω) (y : Ω) := ∑i,q (X i) y
  let Q (X : Fin N → Ω) := ∫y,(S X y)^2 ∂μ
  let C := (N:ℝ)*A
  let H (X : Fin N → Ω) := ∫y,(S X y)^(2*m) ∂μ
  let a := 24*Real.exp 1*(m:ℝ)*(N:ℝ)
  let b := 192*(m:ℝ)^2
  have hCn : 0≤C := mul_nonneg (Nat.cast_nonneg _) hA.le
  have hSn (X : Fin N → Ω) (y : Ω) : |S X y|≤C := by
    calc
      _ ≤ ∑i,|q (X i) y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑_ : Fin N,A := Finset.sum_le_sum fun i _ => hb _ _
      _ = _ := by simp [C]
  have hSm (X : Fin N → Ω) : Measurable (S X) := by
    apply Finset.measurable_fun_sum
    intro i hi
    exact hq.comp (measurable_const.prodMk measurable_id)
  have hSsq (X : Fin N → Ω) : Integrable (fun y => (S X y)^2) μ :=
    bi μ _ ((hSm X).pow_const 2) (C^2) (fun y => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hSn X y) 2)
  have hSQm : Measurable (fun v : (Fin N → Ω) × Ω => (S v.1 v.2)^2) := by
    apply Measurable.pow_const
    apply Finset.measurable_fun_sum
    intro i hi
    have hp : Measurable (fun v : (Fin N → Ω) × Ω => (v.1 i,v.2)) :=
      ((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd
    exact hq.comp hp
  have hQm : Measurable Q := hSQm.stronglyMeasurable.integral_prod_right'.measurable
  have hQn (X : Fin N → Ω) : 0≤Q X := integral_nonneg fun y => sq_nonneg _
  have hQb (X : Fin N → Ω) : Q X≤C^2 := by
    calc
      _ ≤ ∫_ : Ω,C^2 ∂μ := integral_mono (hSsq X) (integrable_const _) fun y => by
        exact (by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hSn X y) 2)
      _ = _ := by simp
  have hmean (X : Fin N → Ω) : (∫y,S X y ∂μ)=0 := by
    change (∫y,∑i,q (X i) y ∂μ)=0
    have hqi (i : Fin N) : Integrable (fun y => q (X i) y) μ :=
      bi μ _ (hq.comp (measurable_const.prodMk measurable_id)) A (hb (X i))
    rw [integral_finset_sum _ (fun i _ => hqi i)]
    simp_rw [hc]; simp
  have hHPm : Measurable (fun v : (Fin N → Ω) × Ω => (S v.1 v.2)^(2*m)) := by
    have hSm0 : Measurable (fun v : (Fin N → Ω) × Ω => S v.1 v.2) := by
      apply Finset.measurable_fun_sum
      intro i hi
      have hp : Measurable (fun v : (Fin N → Ω) × Ω => (v.1 i,v.2)) :=
        ((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd
      exact hq.comp hp
    exact hSm0.pow_const _
  have hHni (X : Fin N → Ω) : 0≤H X := integral_nonneg fun y => (even_two_mul m).pow_nonneg _
  have hHi (X : Fin N → Ω) : Integrable (fun y => (S X y)^(2*m)) μ :=
    bi μ _ ((hSm X).pow_const _) (C^(2*m)) (fun y => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hSn X y) _)
  have hHPi : Integrable (fun v : (Fin N → Ω) × Ω => (S v.1 v.2)^(2*m)) (ν.prod μ) :=
    bi (ν.prod μ) _ hHPm (C^(2*m)) (fun v => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hSn v.1 v.2) _)
  have ha : 0≤a := by dsimp [a]; positivity
  have hbn : 0≤b := by dsimp [b]; positivity
  have hrow (X : Fin N → Ω) :
      (∫Y : Fin N → Ω,(∑j,S X (Y j))^(2*m) ∂ν) ≤
      (2:ℝ)^m*(a^m*(Q X)^m+b^m*(N:ℝ)*H X) := by
    let TX := ((N:ℝ)*H X)^(((2*m:ℕ):ℝ)⁻¹)
    have hTXn : 0≤TX := Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _) (hHni X)) _
    have hTXpow : TX^(2*m)=(N:ℝ)*H X :=
      Real.rpow_inv_natCast_pow (mul_nonneg (Nat.cast_nonneg _) (hHni X)) (by omega)
    have hs := IndependentRosenthalEvenMoment μ N (fun _ : Fin N => S X)
      (fun _ => hSm X) C hCn (fun _ => hSn X) (fun _ => hmean X)
      m hm ((N:ℝ)*Q X) TX (by positivity) hTXn
      (by simp [Q]) (by simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hTXpow.symm.le)
    have ht : (2:ℝ)^(m-1)≤(2:ℝ)^m := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
    calc
      _ ≤ (a*Q X+b*TX^2)^m := by simpa only [a,b,mul_assoc] using hs
      _ ≤ (2:ℝ)^m*((a*Q X)^m+(b*TX^2)^m) :=
        (add_pow_le (mul_nonneg ha (hQn X)) (mul_nonneg hbn (sq_nonneg TX)) m).trans
          (mul_le_mul_of_nonneg_right ht (by positivity))
      _ = _ := by rw [mul_pow a (Q X) m,mul_pow b (TX^2) m,←pow_mul,hTXpow]; ring
  let G (v : (Fin N → Ω) × (Fin N → Ω)) := (∑j,S v.1 (v.2 j))^(2*m)
  have hGm : Measurable G := by
    apply Measurable.pow_const
    apply Finset.measurable_fun_sum
    intro j hj
    apply Finset.measurable_fun_sum
    intro i hi
    have hp : Measurable (fun v : (Fin N → Ω) × (Fin N → Ω) => (v.1 i,v.2 j)) :=
      ((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply j).comp measurable_snd)
    exact hq.comp hp
  have hGb (v : (Fin N → Ω) × (Fin N → Ω)) : |G v|≤((N:ℝ)*C)^(2*m) := by
    dsimp [G]
    rw [abs_pow]
    apply pow_le_pow_left₀ (abs_nonneg _)
    calc
      _ ≤ ∑j,|S v.1 (v.2 j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑_ : Fin N,C := Finset.sum_le_sum fun j _ => hSn _ _
      _ = _ := by simp
  have hGi : Integrable G (ν.prod ν) := bi (ν.prod ν) G hGm _ hGb
  have hQmi : Integrable (fun X => (Q X)^m) ν := bi ν _ (hQm.pow_const _) ((C^2)^m)
    (fun X => by rw [abs_pow,abs_of_nonneg (hQn X)]; exact pow_le_pow_left₀ (hQn X) (hQb X) _)
  have hQmoment : (∫X,(Q X)^m ∂ν)≤(5832*(m:ℝ)*(N:ℝ)*B^2)^m := by
    have hh := optimized_l2_moment μ N hN q hq A B hA.le hB hb hc' hv hv' (2*m) (by omega)
    have hid (X : Fin N → Ω) : (Real.sqrt (Q X))^(2*m)=(Q X)^m := by
      rw [pow_mul,Real.sq_sqrt (hQn X)]
    have hr : (54*Real.sqrt ((2*m:ℕ):ℝ)*Real.sqrt (N:ℝ)*B)^(2*m)=
        (5832*(m:ℝ)*(N:ℝ)*B^2)^m := by
      rw [pow_mul]
      congr 1
      rw [mul_pow,mul_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg _),Real.sq_sqrt (Nat.cast_nonneg _)]
      push_cast; ring
    simpa only [S,Q,hid,hr] using hh
  have hright : Integrable (fun X => (2:ℝ)^m*(a^m*(Q X)^m+b^m*(N:ℝ)*H X)) ν :=
    ((hQmi.const_mul (a^m)).add (hHPi.integral_prod_left.const_mul (b^m*(N:ℝ)))).const_mul _
  have hq2i : Integrable (fun v:Ω×Ω=>(q v.1 v.2)^2) (μ.prod μ) :=
    bi _ _ (hq.pow_const _) (A^2) (fun v=>by rw[abs_pow];exact pow_le_pow_left₀ (abs_nonneg _) (hb _ _) _)
  have hHS : (∫v:Ω×Ω,(q v.1 v.2)^2 ∂μ.prod μ)≤B^2 := by
    rw[integral_prod _ hq2i]
    have hh:=integral_mono hq2i.integral_prod_left (integrable_const (B^2)) hv
    simpa using hh
  have hsecond:=GLZSecondConditionalRosenthal μ N hN q hq A B B hA hB hB hb hc' hv' hHS m hm
  have hswap : (∫X,H X ∂ν)=(∫y,∫X:Fin N→Ω,(S X y)^(2*m) ∂ν ∂μ) :=
    integral_integral_swap (f:=fun X y=>(S X y)^(2*m)) hHPi
  change (m:ℝ)^(2*m)*(N:ℝ)*(∫y,∫X:Fin N→Ω,(S X y)^(2*m) ∂ν ∂μ)≤_ at hsecond
  rw[←hswap] at hsecond
  let K:=139968*Real.exp 1+6144*(24*Real.exp 1+192)
  let Z:=(m:ℝ)^2*(N:ℝ)^2*B^2+(m:ℝ)^3*(N:ℝ)*B^2+(m:ℝ)^4*A^2
  have hKn : 0≤K := by dsimp[K];positivity
  have hZn : 0≤Z := by dsimp[Z];positivity
  have hK1 : 139968*Real.exp 1≤K := by dsimp[K];linarith[Real.exp_pos 1]
  have hK2 : 192*(32*(24*Real.exp 1+192))≤K := by dsimp[K];linarith[Real.exp_pos 1]
  have hm1 : 1≤(m:ℝ) := by exact_mod_cast hm
  have hXZ : (m:ℝ)^2*(N:ℝ)^2*B^2≤Z := by
    dsimp[Z]
    have hy:0≤(m:ℝ)^3*(N:ℝ)*B^2 := by positivity
    have hz:0≤(m:ℝ)^4*A^2 := by positivity
    linarith
  have hfirst : a^m*(∫X,(Q X)^m ∂ν)≤K^m*Z^m := by
    calc
      _≤a^m*(5832*(m:ℝ)*(N:ℝ)*B^2)^m := mul_le_mul_of_nonneg_left hQmoment (pow_nonneg ha _)
      _=(139968*Real.exp 1*((m:ℝ)^2*(N:ℝ)^2*B^2))^m := by rw[←mul_pow];congr 1;dsimp[a];ring
      _≤(K*Z)^m := pow_le_pow_left₀ (by positivity) (mul_le_mul hK1 hXZ (by positivity) hKn) _
      _=_ := mul_pow _ _ _
  have hsmallHS : (m:ℝ)*(N:ℝ)^2*B^2≤(m:ℝ)^2*(N:ℝ)^2*B^2 := by
    have hh : (m:ℝ)≤(m:ℝ)^2 := by nlinarith
    simpa only[mul_assoc] using mul_le_mul_of_nonneg_right hh (by positivity : 0≤(N:ℝ)^2*B^2)
  have hsum : ((m:ℝ)*(N:ℝ)^2*B^2)^m+((m:ℝ)^3*(N:ℝ)*B^2)^m+((m:ℝ)^4*A^2)^m≤Z^m := by
    have hx:=pow_le_pow_left₀ (by positivity) hsmallHS m
    have hy:=pow_add_pow_le (by positivity : 0≤(m:ℝ)^2*(N:ℝ)^2*B^2) (by positivity : 0≤(m:ℝ)^3*(N:ℝ)*B^2) (by omega : m≠0)
    have hz:=pow_add_pow_le (by positivity : 0≤(m:ℝ)^2*(N:ℝ)^2*B^2+(m:ℝ)^3*(N:ℝ)*B^2) (by positivity : 0≤(m:ℝ)^4*A^2) (by omega : m≠0)
    exact (add_le_add (add_le_add hx le_rfl) le_rfl).trans ((add_le_add hy le_rfl).trans hz)
  have hrest : b^m*(N:ℝ)*(∫X,H X ∂ν)≤K^m*Z^m := by
    calc
      _=(192:ℝ)^m*((m:ℝ)^(2*m)*(N:ℝ)*(∫X,H X ∂ν)) := by dsimp[b];rw[mul_pow,←pow_mul];ring
      _≤(192:ℝ)^m*((32*(24*Real.exp 1+192))^m*
        (((m:ℝ)*(N:ℝ)^2*B^2)^m+((m:ℝ)^3*(N:ℝ)*B^2)^m+((m:ℝ)^4*A^2)^m)) := mul_le_mul_of_nonneg_left hsecond (by positivity)
      _=(192*(32*(24*Real.exp 1+192)))^m*
        (((m:ℝ)*(N:ℝ)^2*B^2)^m+((m:ℝ)^3*(N:ℝ)*B^2)^m+((m:ℝ)^4*A^2)^m) := by rw[←mul_assoc,←mul_pow]
      _≤K^m*Z^m := mul_le_mul (pow_le_pow_left₀ (by positivity) hK2 _) hsum (by positivity) (pow_nonneg hKn _)
  have hmain : (∫v,G v ∂ν.prod ν)≤(2:ℝ)^m*(a^m*(∫X,(Q X)^m ∂ν)+b^m*(N:ℝ)*(∫X,H X ∂ν)) := by
    calc
      _=∫X,∫Y,(∑j,S X (Y j))^(2*m) ∂ν ∂ν := integral_prod G hGi
      _≤∫X,(2:ℝ)^m*(a^m*(Q X)^m+b^m*(N:ℝ)*H X) ∂ν := integral_mono hGi.integral_prod_left hright hrow
      _=_ := by rw[integral_const_mul,integral_add (hQmi.const_mul _) (hHPi.integral_prod_left.const_mul _),integral_const_mul,integral_const_mul]
  have hbound : (∫v,G v ∂ν.prod ν)≤(4*K*Z)^m := by
    have h2 : (2:ℝ)≤(2:ℝ)^m := by simpa using pow_le_pow_right₀ (a:=(2:ℝ)) (by norm_num) hm
    calc
      _≤(2:ℝ)^m*(K^m*Z^m+K^m*Z^m) := hmain.trans (mul_le_mul_of_nonneg_left (add_le_add hfirst hrest) (by positivity))
      _=(2:ℝ)^m*2*(K^m*Z^m) := by ring
      _≤(2:ℝ)^m*(2:ℝ)^m*(K^m*Z^m) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by positivity)) (by positivity)
      _=_ := by rw[←mul_pow,←mul_pow,←mul_pow];congr 1;ring
  have hsumG (v:(Fin N→Ω)×(Fin N→Ω)) : (∑i,∑j,q (v.1 i) (v.2 j))^(2*m)=G v := by dsimp[G,S];rw[Finset.sum_comm]
  simp_rw[hsumG]
  exact hbound
