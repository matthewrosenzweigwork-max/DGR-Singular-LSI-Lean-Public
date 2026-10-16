import Tablet.RieszMellinCoefficientBounds
import Tablet.RieszMellinLong
import Tablet.HeatKernelFacts
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open MeasureTheory Set Filter UnitAddTorus
open scoped Topology
-- [TABLET NODE: RieszMellinFourier]
theorem RieszMellinFourier (d:ℕ) (s a:ℝ) (hsd:s<(d:ℝ)) (ha:0<a)
    (δ ε:ℝ) (hδ:0<δ) (hε:0≤ε):
    let c:=RieszMellinCoefficient d s a δ ε
    Summable c ∧
    (∀x:UnitAddTorus (Fin d),RieszMellinLong d s a δ ε x=
      ∑'k:Fin d→ℤ,c k*(UnitAddTorus.mFourier k x).re) ∧
    (∑'k:Fin d→ℤ,c k)=RieszMellinLong d s a δ ε 0 ∧
    Continuous (RieszMellinLong d s a δ ε) := by
-- BODY
  classical
  have character_exp (d : ℕ) (k : Fin d → ℤ) (x : UnitAddTorus (Fin d)) :
      UnitAddTorus.mFourier k x = Complex.exp
        ((2 * Real.pi * ∑ j, (k j : ℝ) *
          (AddCircle.equivIco (1 : ℝ) 0 (x j) : ℝ) : ℝ) * Complex.I) := by
    classical
    have hx : x = fun j =>
        ((AddCircle.equivIco (1 : ℝ) 0 (x j) : ℝ) : AddCircle (1 : ℝ)) := by
      ext j
      exact AddCircle.coe_equivIco.symm
    conv_lhs => rw [hx]
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_coe_apply,
      div_one]
    rw [← Complex.exp_sum]
    congr 1
    simp only [Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  
  have cos_eq_character_re (d : ℕ) (k : Fin d → ℤ) (x : UnitAddTorus (Fin d)) :
      Real.cos (2 * Real.pi * ∑ j, (k j : ℝ) *
        (AddCircle.equivIco (1 : ℝ) 0 (x j) : ℝ)) =
          (UnitAddTorus.mFourier k x).re := by
    rw [character_exp, Complex.exp_re]
    simp
  

  have gaussian_int_summable (c : ℝ) (hc : 0 < c) :
      Summable (fun n : ℤ => Real.exp (-c * (n : ℝ)^2)) := by
    have hn : Summable (fun n : ℕ => Real.exp (-c * (n : ℝ)^2)) := by
      apply Real.summable_exp_nat_mul_of_ge (neg_lt_zero.mpr hc)
      intro n
      exact_mod_cast (show n ≤ n^2 by nlinarith)
    apply summable_int_iff_summable_nat_and_neg.mpr
    constructor
    · simpa using hn
    · simpa using hn
  
  have gaussian_lattice_summable (d : ℕ) (c : ℝ) (hc : 0 < c) :
      Summable (fun k : Fin d → ℤ => Real.exp (-c * ∑ j, (k j : ℝ)^2)) := by
    induction d with
    | zero => exact (hasSum_fintype _).summable
    | succ d ih =>
      have hs := (gaussian_int_summable c hc).mul_of_nonneg ih
        (fun _ => Real.exp_nonneg _) (fun _ => Real.exp_nonneg _)
      apply (Fin.consEquiv (fun _ : Fin (d+1) => ℤ)).summable_iff.mp
      convert hs using 1
      ext k
      simp only [Function.comp_apply, Fin.consEquiv_apply, Fin.sum_univ_succ,
        Fin.cons_zero, Fin.cons_succ]
      rw [mul_add, Real.exp_add]
  
  have nonzero_norm_sq {d : ℕ} (k : Fin d → ℤ) (hk : k≠0) :
      (1:ℝ)≤∑ j,(k j:ℝ)^2 := by
    have hex : ∃j,k j≠0 := by
      by_contra h
      push_neg at h
      apply hk
      funext j
      exact h j
    obtain ⟨j,hj⟩ := hex
    have hsq : (1:ℝ)≤(k j:ℝ)^2 := by
      have h : (1:ℤ)≤(k j)^2 := by
        have hp : 1≤k j ∨ k j≤-1 := by omega
        rcases hp with hp | hp <;> nlinarith
      exact_mod_cast h
    exact hsq.trans (Finset.single_le_sum (fun l _=>sq_nonneg (k l:ℝ)) (Finset.mem_univ j))
  

  have frequency_ge_two (d:ℕ) (k:Fin d→ℤ) (hk:k≠0):
      2≤4*Real.pi^2*∑j,(k j:ℝ)^2:=by
    have hn:=nonzero_norm_sq k hk
    have hpi:=Real.pi_gt_three
    nlinarith [mul_nonneg (show 0≤4*Real.pi^2-2 by nlinarith) (show 0≤∑j,(k j:ℝ)^2 by positivity)]

  have coefficient_summable (d:ℕ) (s a:ℝ) (hsd:s<(d:ℝ)) (ha:0<a)
      (δ ε:ℝ) (hδ:0<δ) (hε:0≤ε):Summable (RieszMellinCoefficient d s a δ ε):=
    (RieszMellinCoefficientBounds d s a hsd ha δ ε hδ hε).1

  have character_norm (d:ℕ) (k:Fin d→ℤ) (x:UnitAddTorus (Fin d)):‖mFourier k x‖=1:=by
    simp only [mFourier,ContinuousMap.coe_mk,fourier_apply,norm_prod,Circle.norm_coe,Finset.prod_const_one]
  have heat_nonzero_rep (d:ℕ) (u:ℝ) (hu:0<u) (x:UnitAddTorus (Fin d)):
      HeatKernel d u x-1=∑'k:Fin d→ℤ,if k=0 then 0 else
        Real.exp (-4*Real.pi^2*u*∑j,(k j:ℝ)^2)*(mFourier k x).re:=by
    classical
    let f:=fun k:Fin d→ℤ=>Real.exp (-4*Real.pi^2*u*∑j,(k j:ℝ)^2)*(mFourier k x).re
    have hg:Summable (fun k:Fin d→ℤ=>Real.exp (-4*Real.pi^2*u*∑j,(k j:ℝ)^2)):=by
      convert gaussian_lattice_summable d (4*Real.pi^2*u) (by positivity) using 1 <;>ring_nf
    have hb:∀k,‖f k‖≤Real.exp (-4*Real.pi^2*u*∑j,(k j:ℝ)^2):=by
      intro k
      rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
      apply mul_le_of_le_one_right (Real.exp_nonneg _)
      exact (Complex.abs_re_le_norm _).trans_eq (character_norm d k x)
    have hs:Summable f:=summable_norm_iff.mp (Summable.of_nonneg_of_le (fun _=>norm_nonneg _) hb hg)
    have h0:f 0=1:=by simp [f,mFourier_zero]
    have he:HeatKernel d u x=∑'k,f k:=by
      unfold HeatKernel
      simp_rw [cos_eq_character_re]
      rfl
    rw [he,hs.tsum_eq_add_tsum_ite 0,h0]
    dsimp [f]
    ring
  have scalar_mode_integrable (d:ℕ) (α:ℝ) (hα:0<α) (ε:ℝ) (hε:0≤ε)
      (k:Fin d→ℤ) (hk:k≠0):
      IntegrableOn (fun t:ℝ=>t^(α-1)*Real.exp (-4*Real.pi^2*(t+ε)*∑j,(k j:ℝ)^2)) (Ioi 0) volume:=by
    have hg:IntegrableOn (fun t:ℝ=>t^(α-1)*Real.exp (-t)) (Ioi 0) volume:=by
      simpa only [mul_comm] using Real.GammaIntegral_convergent hα
    have hν:=frequency_ge_two d k hk
    apply hg.mono' ((measurable_id.pow_const _).mul
      ((((measurable_const.mul measurable_const).mul (measurable_id.add_const ε)).mul measurable_const).exp)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0:0<t:=ht
    change ‖t^(α-1)*Real.exp (-4*Real.pi^2*(t+ε)*∑j,(k j:ℝ)^2)‖≤t^(α-1)*Real.exp (-t)
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have hq:0≤∑j,(k j:ℝ)^2:=by positivity
    nlinarith [mul_nonneg (show 0≤4*Real.pi^2 by positivity) (mul_nonneg hε hq),mul_nonneg (show 0≤4*Real.pi^2*(∑j,(k j:ℝ)^2)-1 by linarith) ht0.le]
  have long_pointwise_series (d:ℕ) (s a:ℝ) (hsd:s<(d:ℝ)) (ha:0<a)
      (δ ε:ℝ) (hδ:0<δ) (hε:0≤ε) (x:UnitAddTorus (Fin d)):
      RieszMellinLong d s a δ ε x=∑'k:Fin d→ℤ,RieszMellinCoefficient d s a δ ε k*(mFourier k x).re:=by
    classical
    let α:=((d:ℝ)-s)/2
    let P:=a/Real.Gamma α
    have hα:0<α:=by dsimp [α];linarith
    have hP:0<P:=div_pos ha (Real.Gamma_pos_of_pos hα)
    let F:=fun(k:Fin d→ℤ)(t:ℝ)=>if k=0 then (0:ℝ) else
      t^(α-1)*Real.exp (-4*Real.pi^2*(t+ε)*∑j,(k j:ℝ)^2)*(mFourier k x).re
    have hFi:∀k,IntegrableOn (F k) (Ioi δ) volume:=by
      intro k
      by_cases hk:k=0
      · simp [F,hk]
      · change Integrable (F k) (volume.restrict (Ioi δ))
        simp only [F,if_neg hk]
        exact ((scalar_mode_integrable d α hα ε hε k hk).mono_set
          (Ioi_subset_Ioi hδ.le)).mul_const (mFourier k x).re
    have hFb:∀k,(∫t in Ioi δ,‖F k t‖)≤P⁻¹*RieszMellinCoefficient d s a δ ε k:=by
      intro k
      by_cases hk:k=0
      · simp [F,hk,RieszMellinCoefficient]
      have hi:= (scalar_mode_integrable d α hα ε hε k hk).mono_set (Ioi_subset_Ioi hδ.le)
      have hb:(∫t in Ioi δ,‖F k t‖)≤∫t in Ioi δ,t^(α-1)*Real.exp (-4*Real.pi^2*(t+ε)*∑j,(k j:ℝ)^2):=by
        apply integral_mono_ae (hFi k).norm hi
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0:0<t:=hδ.trans ht
        simp only [F,if_neg hk,Real.norm_eq_abs,abs_mul,
          abs_of_nonneg (Real.rpow_nonneg ht0.le _),abs_of_pos (Real.exp_pos _)]
        apply mul_le_of_le_one_right (by positivity)
        exact (Complex.abs_re_le_norm _).trans_eq (character_norm d k x)
      refine hb.trans_eq ?_
      simp only [RieszMellinCoefficient,if_neg hk]
      change _=P⁻¹*(P*_)
      rw [←mul_assoc,inv_mul_cancel₀ (ne_of_gt hP),one_mul]
    have hFs:Summable (fun k=>∫t in Ioi δ,‖F k t‖):=
      Summable.of_nonneg_of_le (fun _=>integral_nonneg (fun _=>norm_nonneg _)) hFb
        ((coefficient_summable d s a hsd ha δ ε hδ hε).mul_left P⁻¹)
    have hsum:=integral_tsum_of_summable_integral_norm hFi hFs
    have hsumfun:(fun t:ℝ=>∑'k,F k t)=ᵐ[volume.restrict (Ioi δ)]
        (fun t=>t^(α-1)*(HeatKernel d (t+ε) x-1)):=by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [heat_nonzero_rep d (t+ε) (add_pos_of_pos_of_nonneg (hδ.trans ht) hε) x,←tsum_mul_left]
      apply tsum_congr
      intro k
      dsimp [F]
      split_ifs <;>ring
    have hcoef:∀k,P*(∫t in Ioi δ,F k t)=RieszMellinCoefficient d s a δ ε k*(mFourier k x).re:=by
      intro k
      by_cases hk:k=0
      · simp [F,hk,RieszMellinCoefficient]
      simp only [F,if_neg hk,integral_mul_const,RieszMellinCoefficient]
      change P*(_*_)=P*_*_
      ring
    change P*(∫t in Ioi δ,t^(α-1)*(HeatKernel d (t+ε) x-1))=_
    rw [←integral_congr_ae hsumfun,←hsum,←tsum_mul_left]
    exact tsum_congr hcoef
  have hs:=coefficient_summable d s a hsd ha δ ε hδ hε
  have hp:=long_pointwise_series d s a hsd ha δ ε hδ hε
  refine ⟨hs,hp,?_,?_⟩
  · rw [hp 0]
    apply tsum_congr
    intro k
    simp [UnitAddTorus.mFourier,fourier_apply]
  · have heq:RieszMellinLong d s a δ ε=(fun x=>∑'k:Fin d→ℤ,
        RieszMellinCoefficient d s a δ ε k*(UnitAddTorus.mFourier k x).re):=funext hp
    rw [heq]
    apply continuous_tsum (fun k=>continuous_const.mul
      (Complex.continuous_re.comp (UnitAddTorus.mFourier k).continuous)) hs
    intro k x
    change ‖RieszMellinCoefficient d s a δ ε k*(UnitAddTorus.mFourier k x).re‖≤RieszMellinCoefficient d s a δ ε k
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg ((RieszMellinCoefficientBounds d s a hsd ha δ ε hδ hε).2.2 k).1]
    apply mul_le_of_le_one_right ((RieszMellinCoefficientBounds d s a hsd ha δ ε hδ hε).2.2 k).1
    exact (Complex.abs_re_le_norm _).trans_eq (character_norm d k x)
