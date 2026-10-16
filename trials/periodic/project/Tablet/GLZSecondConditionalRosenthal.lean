module

public import Tablet.IndependentRosenthalEvenMoment
public import Tablet.GLZBoundedMomentCorrection

@[expose] public section
open MeasureTheory
universe u
-- [TABLET NODE: GLZSecondConditionalRosenthal]
theorem GLZSecondConditionalRosenthal {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ) (hN : 0<N)
    (q : Ω → Ω → ℝ) (hq : Measurable (fun v:Ω×Ω=>q v.1 v.2))
    (A F H : ℝ) (hA : 0<A) (hF : 0<F) (hH : 0<H)
    (hb : ∀x y,|q x y|≤A) (hc : ∀y,(∫x,q x y ∂μ)=0)
    (hFbound : ∀y,(∫x,(q x y)^2 ∂μ)≤F^2)
    (hHS : (∫v:Ω×Ω,(q v.1 v.2)^2 ∂μ.prod μ)≤H^2)
    (m : ℕ) (hm : 1≤m) :
    (m:ℝ)^(2*m)*(N:ℝ)*(∫y,∫X:Fin N→Ω,(∑i,q (X i) y)^(2*m)
      ∂Measure.pi (fun _:Fin N=>μ) ∂μ)≤
      (32*(24*Real.exp 1+192))^m*
        ((((m:ℝ)*(N:ℝ)^2*H^2))^m+
        (((m:ℝ)^3*(N:ℝ)*F^2))^m+(((m:ℝ)^4*A^2))^m) := by
-- BODY
  classical
  have bi {Λ:Type u} [MeasurableSpace Λ] (ξ:Measure Λ) [IsProbabilityMeasure ξ]
      (f:Λ→ℝ) (hf:Measurable f) (C:ℝ) (hb:∀x,|f x|≤C) : Integrable f ξ :=
    Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun x=>by
      simpa only[Real.norm_eq_abs] using hb x)
  let ν:=Measure.pi (fun _:Fin N=>μ)
  let V (y:Ω):=(N:ℝ)*(∫x,(q x y)^2 ∂μ)
  let W (y:Ω):=(N:ℝ)*(∫x,(q x y)^(2*m) ∂μ)
  let R:=24*Real.exp 1+192
  have hRn : 0≤R := by dsimp[R];positivity
  have hR1 : 24*Real.exp 1≤R := by dsimp[R];linarith
  have hR2 : 192≤R := by dsimp[R];linarith[Real.exp_pos 1]
  have hqpow (n:ℕ) : Integrable (fun v:Ω×Ω=>(q v.1 v.2)^n) (μ.prod μ) :=
    bi _ _ (hq.pow_const n) (A^n) (fun v=>by rw[abs_pow];exact pow_le_pow_left₀ (abs_nonneg _) (hb _ _) _)
  have hVm : Measurable V :=
    ((hq.pow_const 2).stronglyMeasurable.integral_prod_left'.measurable).const_mul _
  have hWm : Measurable W :=
    ((hq.pow_const (2*m)).stronglyMeasurable.integral_prod_left'.measurable).const_mul _
  have hVn (y:Ω):0≤V y := by dsimp[V];positivity
  have hWn (y:Ω):0≤W y := by dsimp[W];exact mul_nonneg (Nat.cast_nonneg _) (integral_nonneg fun x=>(even_two_mul m).pow_nonneg _)
  have hVb (y:Ω):V y≤(N:ℝ)*F^2 := mul_le_mul_of_nonneg_left (hFbound y) (Nat.cast_nonneg _)
  have hWb (y:Ω):W y≤(N:ℝ)*A^(2*m) := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have hqi : Integrable (fun x=>(q x y)^(2*m)) μ :=
      bi μ _ ((hq.comp (measurable_id.prodMk measurable_const)).pow_const _) _
        (fun x=>by rw[abs_pow];exact pow_le_pow_left₀ (abs_nonneg _) (hb _ _) _)
    calc
      _≤∫_:Ω,A^(2*m) ∂μ := integral_mono hqi (integrable_const _) fun x=>by
        have hh:=pow_le_pow_left₀ (abs_nonneg (q x y)) (hb x y) (2*m)
        rwa[(even_two_mul m).pow_abs] at hh
      _=_ := by simp
  have hVi : Integrable V μ := bi μ V hVm _ (fun y=>by rw[abs_of_nonneg (hVn y)];exact hVb y)
  have hWi : Integrable W μ := bi μ W hWm _ (fun y=>by rw[abs_of_nonneg (hWn y)];exact hWb y)
  have hVmean : (∑_:Fin N,∫y,V y ∂μ)≤(N:ℝ)^2*H^2 := by
    simp only[Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    change (N:ℝ)*(∫y,(N:ℝ)*(∫x,(q x y)^2 ∂μ) ∂μ)≤_
    have hs:=integral_integral_swap (f:=fun x y=>(q x y)^2) (hqpow 2)
    rw[integral_const_mul,←hs,←integral_prod _ (hqpow 2)]
    have hh:=mul_le_mul_of_nonneg_left hHS (sq_nonneg (N:ℝ))
    simpa only[pow_two,mul_assoc] using hh
  have hVC:=GLZBoundedMomentCorrection μ (fun _:Fin N=>V) ((N:ℝ)*F^2) ((N:ℝ)^2*H^2)
    (by positivity) (by positivity) (fun _=>hVi) (fun _=>Filter.Eventually.of_forall hVn)
    (fun _=>Filter.Eventually.of_forall hVb) hVmean m hm 2
  have hVmi : Integrable (fun y=>(V y)^m) μ := hVC.1 ⟨0,hN⟩
  have hVcorr : (m:ℝ)^(3*m)*(N:ℝ)*(∫y,(V y)^m ∂μ)≤
      (4:ℝ)^m*((((m:ℝ)*(N:ℝ)^2*H^2))^m+(((m:ℝ)^3*(N:ℝ)*F^2))^m) := by
    simpa only[Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      show 2+1=3 by rfl,show (2^2:ℝ)=4 by norm_num,mul_assoc] using hVC.2
  have hQmean : (∑_:Fin N×Fin N,∫v:Ω×Ω,(q v.1 v.2)^2 ∂μ.prod μ)≤(N:ℝ)^2*H^2 := by
    simp only[Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul]
    simpa only[pow_two] using mul_le_mul_of_nonneg_left hHS (by positivity : 0≤(N:ℝ)*(N:ℝ))
  have hAC:=GLZBoundedMomentCorrection (μ.prod μ) (fun _:Fin N×Fin N=>fun v:Ω×Ω=>(q v.1 v.2)^2)
    (A^2) ((N:ℝ)^2*H^2) (by positivity) (by positivity) (fun _=>hqpow 2)
    (fun _=>Filter.Eventually.of_forall fun v=>sq_nonneg _)
    (fun _=>Filter.Eventually.of_forall fun v=>by simpa only[sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hb v.1 v.2) 2)
    hQmean m hm 3
  have hAcorr : (m:ℝ)^(4*m)*(N:ℝ)*(∫y,W y ∂μ)≤
      (8:ℝ)^m*((((m:ℝ)*(N:ℝ)^2*H^2))^m+(((m:ℝ)^4*A^2))^m) := by
    have hh:=hAC.2
    simp only[Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,
      Nat.cast_mul,show 3+1=4 by rfl,show (2^3:ℝ)=8 by norm_num,←pow_mul] at hh
    change (m:ℝ)^(4*m)*(N:ℝ)*(∫y,(N:ℝ)*(∫x,(q x y)^(2*m) ∂μ) ∂μ)≤_
    have hs:=integral_integral_swap (f:=fun x y=>(q x y)^(2*m)) (hqpow (2*m))
    rw[integral_const_mul,←hs,←integral_prod _ (hqpow (2*m))]
    convert hh using 1 <;> ring
  have hrow (y:Ω) : (∫X:Fin N→Ω,(∑i,q (X i) y)^(2*m) ∂ν)≤
      (2*R)^m*((m:ℝ)^m*(V y)^m+(m:ℝ)^(2*m)*W y) := by
    let T:=(W y)^(((2*m:ℕ):ℝ)⁻¹)
    have hTn : 0≤T := Real.rpow_nonneg (hWn y) _
    have hTpow : T^(2*m)=W y := Real.rpow_inv_natCast_pow (hWn y) (by omega : 2*m≠0)
    have hr:=IndependentRosenthalEvenMoment μ N (fun _:Fin N=>fun x=>q x y)
      (fun _=>hq.comp (measurable_id.prodMk measurable_const)) A hA.le (fun _ x=>hb x y)
      (fun _=>hc y) m hm (V y) T (hVn y) hTn (by simp[V]) (by simp[W,hTpow])
    have hterms : 24*Real.exp 1*(m:ℝ)*V y+192*(m:ℝ)^2*T^2≤
        R*((m:ℝ)*V y+(m:ℝ)^2*T^2) := by
      have h1:=mul_le_mul_of_nonneg_right hR1 (by positivity : 0≤(m:ℝ)*V y)
      have h2:=mul_le_mul_of_nonneg_right hR2 (by positivity : 0≤(m:ℝ)^2*T^2)
      nlinarith only[h1,h2]
    have hpow:=pow_le_pow_left₀ (by positivity : 0≤24*Real.exp 1*(m:ℝ)*V y+192*(m:ℝ)^2*T^2) hterms m
    have hsplit:=add_pow_le (by positivity : 0≤(m:ℝ)*V y) (by positivity : 0≤(m:ℝ)^2*T^2) m
    have htwo : (2:ℝ)^(m-1)≤(2:ℝ)^m := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
    calc
      _≤_ := hr.trans hpow
      _=R^m*((m:ℝ)*V y+(m:ℝ)^2*T^2)^m := mul_pow _ _ _
      _≤R^m*((2:ℝ)^m*(((m:ℝ)*V y)^m+((m:ℝ)^2*T^2)^m)) :=
        mul_le_mul_of_nonneg_left (hsplit.trans (mul_le_mul_of_nonneg_right htwo (by positivity))) (pow_nonneg hRn _)
      _=_ := by
        have he : ((m:ℝ)^2*T^2)^m=(m:ℝ)^(2*m)*W y := by
          rw[mul_pow,←pow_mul,←pow_mul,hTpow]
        rw[he,mul_pow,mul_pow]
        ring
  have hjointm : Measurable (fun v:(Fin N→Ω)×Ω=>(∑i,q (v.1 i) v.2)^(2*m)) := by
    apply Measurable.pow_const
    apply Finset.measurable_fun_sum
    intro i hi
    have hp : Measurable (fun v:(Fin N→Ω)×Ω=>(v.1 i,v.2)) :=
      ((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd
    exact hq.comp hp
  have hji : Integrable (fun v:(Fin N→Ω)×Ω=>(∑i,q (v.1 i) v.2)^(2*m)) (ν.prod μ) :=
    bi _ _ hjointm (((N:ℝ)*A)^(2*m)) (fun v=>by
      rw[abs_pow]
      apply pow_le_pow_left₀ (abs_nonneg _) _
      calc
        _≤∑i,|q (v.1 i) v.2| := Finset.abs_sum_le_sum_abs _ _
        _≤∑_:Fin N,A := Finset.sum_le_sum fun i _=>hb _ _
        _=_ := by simp)
  have hh:=integral_mono hji.integral_prod_right
    (((hVmi.const_mul ((m:ℝ)^m)).add (hWi.const_mul ((m:ℝ)^(2*m)))).const_mul ((2*R)^m)) hrow
  rw[integral_const_mul] at hh
  change (∫y,∫X:Fin N→Ω,(∑i,q (X i) y)^(2*m) ∂ν ∂μ)≤
    (2*R)^m*(∫y,(m:ℝ)^m*(V y)^m+(m:ℝ)^(2*m)*W y ∂μ) at hh
  have he:=integral_add (hVmi.const_mul ((m:ℝ)^m)) (hWi.const_mul ((m:ℝ)^(2*m)))
  change (∫y,(m:ℝ)^m*(V y)^m+(m:ℝ)^(2*m)*W y ∂μ)=_ at he
  rw[he,integral_const_mul,integral_const_mul] at hh
  have hcombine : (4:ℝ)^m*((((m:ℝ)*(N:ℝ)^2*H^2))^m+(((m:ℝ)^3*(N:ℝ)*F^2))^m)+
      (8:ℝ)^m*((((m:ℝ)*(N:ℝ)^2*H^2))^m+(((m:ℝ)^4*A^2))^m)≤
      (16:ℝ)^m*((((m:ℝ)*(N:ℝ)^2*H^2))^m+(((m:ℝ)^3*(N:ℝ)*F^2))^m+(((m:ℝ)^4*A^2))^m) := by
    have h48 : (4:ℝ)^m≤(8:ℝ)^m := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    have h2 : (2:ℝ)≤(2:ℝ)^m := by simpa using pow_le_pow_right₀ (a:=(2:ℝ)) (by norm_num) hm
    have h16 : (16:ℝ)^m=(2:ℝ)^m*(8:ℝ)^m := by rw[←mul_pow];norm_num
    let x:=(((m:ℝ)*(N:ℝ)^2*H^2))^m
    let y:=(((m:ℝ)^3*(N:ℝ)*F^2))^m
    let z:=(((m:ℝ)^4*A^2))^m
    have hx:0≤x := by dsimp[x];positivity
    have hy:0≤y := by dsimp[y];positivity
    have hz:0≤z := by dsimp[z];positivity
    change (4:ℝ)^m*(x+y)+(8:ℝ)^m*(x+z)≤(16:ℝ)^m*(x+y+z)
    calc
      _≤(8:ℝ)^m*(x+y)+(8:ℝ)^m*(x+z) :=
        add_le_add (mul_le_mul_of_nonneg_right h48 (add_nonneg hx hy)) le_rfl
      _=(8:ℝ)^m*(2*x+y+z) := by ring
      _≤(8:ℝ)^m*(2*(x+y+z)) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _=2*((8:ℝ)^m*(x+y+z)) := by ring
      _≤(2:ℝ)^m*((8:ℝ)^m*(x+y+z)) := mul_le_mul_of_nonneg_right h2 (by positivity)
      _=_ := by rw[h16];ring
  calc
    _≤(m:ℝ)^(2*m)*(N:ℝ)*((2*R)^m*((m:ℝ)^m*(∫y,(V y)^m ∂μ)+(m:ℝ)^(2*m)*(∫y,W y ∂μ))) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _=(2*R)^m*((m:ℝ)^(3*m)*(N:ℝ)*(∫y,(V y)^m ∂μ)+(m:ℝ)^(4*m)*(N:ℝ)*(∫y,W y ∂μ)) := by
      have h3 : (m:ℝ)^(3*m)=(m:ℝ)^(2*m)*(m:ℝ)^m := by rw[←pow_add];congr 1;omega
      have h4 : (m:ℝ)^(4*m)=(m:ℝ)^(2*m)*(m:ℝ)^(2*m) := by rw[←pow_add];congr 1;omega
      rw[h3,h4];ring
    _≤(2*R)^m*((4:ℝ)^m*((((m:ℝ)*(N:ℝ)^2*H^2))^m+(((m:ℝ)^3*(N:ℝ)*F^2))^m)+
      (8:ℝ)^m*((((m:ℝ)*(N:ℝ)^2*H^2))^m+(((m:ℝ)^4*A^2))^m)) :=
      mul_le_mul_of_nonneg_left (add_le_add hVcorr hAcorr) (by positivity)
    _≤(2*R)^m*((16:ℝ)^m*((((m:ℝ)*(N:ℝ)^2*H^2))^m+(((m:ℝ)^3*(N:ℝ)*F^2))^m+(((m:ℝ)^4*A^2))^m)) :=
      mul_le_mul_of_nonneg_left hcombine (by positivity)
    _=_ := by rw[←mul_assoc,←mul_pow];dsimp[R];congr 2;ring
