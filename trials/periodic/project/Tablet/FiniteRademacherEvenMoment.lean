import Tablet.Preamble
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
open scoped BigOperators
-- [TABLET NODE: FiniteRademacherEvenMoment]
theorem FiniteRademacherEvenMoment (N:ℕ)(a:Fin N→ℝ)(m:ℕ)(hm:1≤m) :
    (Fintype.card (Fin N→Bool):ℝ)⁻¹ *
      (∑σ:Fin N→Bool,(∑i:Fin N,(if σ i then 1 else -1)*a i)^(2*m))≤
    (6*(m:ℝ))^m*(∑i:Fin N,a i^2)^m := by
-- BODY
  have finite_rademacher_mgf (N:ℕ)(a:Fin N→ℝ)(t:ℝ) :
      (Fintype.card (Fin N→Bool):ℝ)⁻¹ *
        (∑σ:Fin N→Bool,Real.exp (t*∑i:Fin N,(if σ i then 1 else -1)*a i))≤
      Real.exp (t^2/2*∑i:Fin N,a i^2) := by
    classical
    have he (σ:Fin N→Bool):Real.exp (t*∑i:Fin N,(if σ i then 1 else -1)*a i)=
        ∏i:Fin N,Real.exp (t*((if σ i then 1 else -1)*a i)):=by
      rw[Finset.mul_sum,Real.exp_sum]
    simp_rw[he]
    rw[←Fintype.prod_sum (fun (i:Fin N)(b:Bool)=>Real.exp (t*((if b then 1 else -1)*a i)))]
    have hs(i:Fin N):(∑b:Bool,Real.exp (t*((if b then 1 else -1)*a i)))=2*Real.cosh (t*a i):=by
      rw[Fintype.sum_bool,Real.cosh_eq]
      simp
      ring
    simp_rw[hs]
    rw[Finset.prod_mul_distrib]
    have hcard:(Fintype.card (Fin N→Bool):ℝ)=∏i:Fin N,(2:ℝ):=by simp[Fintype.card_fun]
    rw[hcard,←mul_assoc,inv_mul_cancel₀ (by positivity),one_mul]
    calc
      (∏i:Fin N,Real.cosh (t*a i))≤∏i:Fin N,Real.exp ((t*a i)^2/2):=
        Finset.prod_le_prod (fun i _=>(Real.cosh_pos _).le) (fun i _=>Real.cosh_le_exp_half_sq _)
      _=Real.exp (t^2/2*∑i:Fin N,a i^2):=by
        rw[←Real.exp_sum,Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have even_power_le_cosh (x:ℝ)(m:ℕ):x^(2*m)≤((2*m).factorial:ℝ)*Real.cosh x:=by
    have h: x^(2*m)/((2*m).factorial:ℝ)≤Real.cosh x:=by
      rw[Real.cosh_eq_tsum]
      exact (Real.hasSum_cosh x).summable.le_tsum m fun j _=>
        div_nonneg (by simpa only [pow_mul] using pow_nonneg (sq_nonneg x) j) (Nat.cast_nonneg _)
    have hp:0<((2*m).factorial:ℝ):=by exact_mod_cast Nat.factorial_pos (2*m)
    simpa only [mul_comm] using (div_le_iff₀ hp).mp h
  classical
  let S:=∑i:Fin N,a i^2
  let C:ℝ:=Fintype.card (Fin N→Bool)
  have hSn:0≤S:=Finset.sum_nonneg fun i _=>sq_nonneg _
  have hCn:0≤C⁻¹:=inv_nonneg.mpr (Nat.cast_nonneg _)
  by_cases hS:S=0
  · have haz:∀i:Fin N,a i=0:=by
      intro i
      have hle:a i^2≤S:=Finset.single_le_sum (fun j _=>sq_nonneg _) (Finset.mem_univ i)
      rw[hS] at hle
      nlinarith [sq_nonneg (a i)]
    have hm2:2*m≠0:=by omega
    simp[haz,hm2,(show m≠0 by omega)]
  have hSp:0<S:=lt_of_le_of_ne hSn (Ne.symm hS)
  have hmp:0<(m:ℝ):=by exact_mod_cast (show 0<m by omega)
  let t:=Real.sqrt (2*(m:ℝ)/S)
  have htp:0<t:=Real.sqrt_pos.2 (div_pos (by positivity) hSp)
  have ht:t^2=2*(m:ℝ)/S:=Real.sq_sqrt (div_nonneg (by positivity) hSn)
  let F:=fun σ:Fin N→Bool=>∑i:Fin N,(if σ i then 1 else -1)*a i
  let M:=C⁻¹*∑σ:Fin N→Bool,(F σ)^(2*m)
  have hp: t^(2*m)*M≤((2*m).factorial:ℝ)*(C⁻¹*∑σ:Fin N→Bool,Real.cosh (t*F σ)):=by
    have hh:=mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s:=Finset.univ)
      (fun σ _=>even_power_le_cosh (t*F σ) m)) hCn
    simp_rw[mul_pow,←Finset.mul_sum] at hh
    dsimp [M]
    simpa only [mul_assoc,mul_left_comm,mul_comm] using hh
  have hmgf:=finite_rademacher_mgf N a t
  have hmgfn:=finite_rademacher_mgf N a (-t)
  change C⁻¹*(∑σ:Fin N→Bool,Real.exp (t*F σ))≤Real.exp (t^2/2*S) at hmgf
  change C⁻¹*(∑σ:Fin N→Bool,Real.exp ((-t)*F σ))≤Real.exp ((-t)^2/2*S) at hmgfn
  rw[neg_sq] at hmgfn
  have hc:C⁻¹*(∑σ:Fin N→Bool,Real.cosh (t*F σ))≤Real.exp (t^2/2*S):=by
    have he:C⁻¹*(∑σ:Fin N→Bool,Real.cosh (t*F σ))=
        (C⁻¹*(∑σ:Fin N→Bool,Real.exp (t*F σ))+C⁻¹*(∑σ:Fin N→Bool,Real.exp ((-t)*F σ)))/2:=by
      simp_rw[Real.cosh_eq,neg_mul]
      rw[←Finset.sum_div,Finset.sum_add_distrib]
      ring
    rw[he]
    linarith
  have he:t^2/2*S=(m:ℝ):=by rw[ht];field_simp[hS]
  rw[he] at hc
  have hh:=hp.trans (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg ((2*m).factorial)))
  have hfact:((2*m).factorial:ℝ)≤(2*(m:ℝ))^(2*m):=by exact_mod_cast Nat.factorial_le_pow (2*m)
  have hexp:Real.exp (m:ℝ)≤(3:ℝ)^m:=by
    have he:Real.exp (m:ℝ)=Real.exp (1:ℝ)^m:=by simpa using Real.exp_nat_mul 1 m
    rw[he]
    exact pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_one_lt_three.le) m
  have hbound:((2*m).factorial:ℝ)*Real.exp (m:ℝ)≤(2*(m:ℝ))^(2*m)*(3:ℝ)^m:=
    mul_le_mul hfact hexp (Real.exp_pos _).le (by positivity)
  have htm:t^(2*m)=(2*(m:ℝ)/S)^m:=by rw[pow_mul,ht]
  rw[htm] at hh
  have hden:0<(2*(m:ℝ)/S)^m:=pow_pos (div_pos (by positivity) hSp) _
  have hdiv:M≤((2*(m:ℝ))^(2*m)*(3:ℝ)^m)/((2*(m:ℝ)/S)^m):=
    (le_div_iff₀ hden).mpr (by simpa only[mul_comm] using hh.trans hbound)
  have hnum:(2*(m:ℝ))^(2*m)*(3:ℝ)^m=((2*(m:ℝ))^m)^2*(3:ℝ)^m:=by
    rw[show 2*m=m+m by omega,pow_add]
    ring
  have hrhs:(6*(m:ℝ))^m*S^m=(3:ℝ)^m*(2*(m:ℝ))^m*S^m:=by
    rw[show 6*(m:ℝ)=3*(2*(m:ℝ)) by ring]
    rw[mul_pow]
  have hratio:((2*(m:ℝ))^(2*m)*(3:ℝ)^m)/((2*(m:ℝ)/S)^m)=
      (6*(m:ℝ))^m*S^m:=by
    rw[hnum,div_pow,hrhs,div_div_eq_mul_div]
    apply (div_eq_iff (pow_ne_zero m (show 2*(m:ℝ)≠0 by positivity))).mpr
    ring
  rwa[hratio] at hdiv
