import Tablet.RieszMellinCoefficient
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open MeasureTheory Set Filter
open scoped Topology
-- [TABLET NODE: RieszMellinCoefficientBounds]
theorem RieszMellinCoefficientBounds (d:ℕ) (s a:ℝ) (hsd:s<(d:ℝ)) (ha:0<a)
    (δ ε:ℝ) (hδ:0<δ) (hε:0≤ε):
    Summable (RieszMellinCoefficient d s a δ ε) ∧
    (∀k:Fin d→ℤ,RieszMellinCoefficient d s a δ ε (-k)=RieszMellinCoefficient d s a δ ε k) ∧
    ∀k:Fin d→ℤ,0≤RieszMellinCoefficient d s a δ ε k ∧
      RieszMellinCoefficient d s a δ ε k≤
        (if k=0 then 0 else a*(4*Real.pi^2*∑j,(k j:ℝ)^2)^(-((d:ℝ)-s)/2)) ∧
      RieszMellinCoefficient d s a δ ε k≤a*Real.exp (-(2*Real.pi^2*δ)*∑j,(k j:ℝ)^2):=by
-- BODY
  classical
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
  

  have coefficient_even (d:ℕ) (s a δ ε:ℝ) (k:Fin d→ℤ):
      RieszMellinCoefficient d s a δ ε (-k)=RieszMellinCoefficient d s a δ ε k:=by
    simp only [RieszMellinCoefficient,neg_eq_zero,Pi.neg_apply,Int.cast_neg,neg_sq]
  have coefficient_bounds (d:ℕ) (s a:ℝ) (hsd:s<(d:ℝ)) (ha:0<a)
      (δ ε:ℝ) (hδ:0≤δ) (hε:0≤ε) (k:Fin d→ℤ):
      0≤RieszMellinCoefficient d s a δ ε k ∧
      RieszMellinCoefficient d s a δ ε k≤
        if k=0 then 0 else a*(4*Real.pi^2*∑j,(k j:ℝ)^2)^(-((d:ℝ)-s)/2):=by
    classical
    by_cases hk:k=0
    · simp [RieszMellinCoefficient,hk]
    let α:=((d:ℝ)-s)/2
    let ν:=4*Real.pi^2*∑j,(k j:ℝ)^2
    let P:=a/Real.Gamma α
    have hα:0<α:=by dsimp [α];linarith
    have hP:0<P:=div_pos ha (Real.Gamma_pos_of_pos hα)
    have hν1:1≤ν:=by
      have hn:=nonzero_norm_sq k hk
      have hpi:=Real.pi_gt_three
      dsimp [ν]
      nlinarith [mul_nonneg (show 0≤4*Real.pi^2-1 by nlinarith) (show 0≤∑j,(k j:ℝ)^2 by positivity)]
    have hν:0<ν:=lt_of_lt_of_le zero_lt_one hν1
    have hbase:IntegrableOn (fun t:ℝ=>t^(α-1)*Real.exp (-(ν*t))) (Ioi 0) volume:=by
      have hg:IntegrableOn (fun t:ℝ=>t^(α-1)*Real.exp (-t)) (Ioi 0) volume:=by
        simpa only [mul_comm] using Real.GammaIntegral_convergent hα
      apply hg.mono' (((measurable_id.pow_const _).mul ((measurable_const.mul measurable_id).neg.exp)).aestronglyMeasurable)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0:0<t:=ht
      change ‖t^(α-1)*Real.exp (-(ν*t))‖≤t^(α-1)*Real.exp (-t)
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      nlinarith
    have hδi:=hbase.mono_set (Ioi_subset_Ioi hδ)
    have hbound:(∫t in Ioi δ,t^(α-1)*Real.exp (-(ν*(t+ε))))≤
        ∫t in Ioi 0,t^(α-1)*Real.exp (-(ν*t)):=by
      have hshift:IntegrableOn (fun t:ℝ=>t^(α-1)*Real.exp (-(ν*(t+ε)))) (Ioi δ) volume:=by
        apply hδi.mono' (((measurable_id.pow_const _).mul ((measurable_const.mul (measurable_id.add_const ε)).neg.exp)).aestronglyMeasurable)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0:0<t:=lt_of_le_of_lt hδ ht
        change ‖t^(α-1)*Real.exp (-(ν*(t+ε)))‖≤t^(α-1)*Real.exp (-(ν*t))
        rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hν.le hε])
      have hi:(∫t in Ioi δ,t^(α-1)*Real.exp (-(ν*(t+ε))))≤
          ∫t in Ioi δ,t^(α-1)*Real.exp (-(ν*t)):=by
        apply integral_mono_ae hshift hδi
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (hδ.trans ht.le) _)
        exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hν.le hε])
      refine hi.trans (setIntegral_mono_set hbase ?_ (Eventually.of_forall (Ioi_subset_Ioi hδ)))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le
    have heval:P*(∫t in Ioi 0,t^(α-1)*Real.exp (-(ν*t)))=a*ν^(-α):=by
      rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hα hν]
      have hp:(1/ν)^α=ν^(-α):=by rw [one_div,Real.inv_rpow,Real.rpow_neg] <;> exact hν.le
      rw [hp]
      dsimp [P]
      field_simp [ne_of_gt (Real.Gamma_pos_of_pos hα)]
    simp only [RieszMellinCoefficient,if_neg hk]
    have hex:(fun t:ℝ=>t^(((d:ℝ)-s)/2-1)*Real.exp (-4*Real.pi^2*(t+ε)*∑j,(k j:ℝ)^2))=
        (fun t=>t^(α-1)*Real.exp (-(ν*(t+ε)))):=by
      funext t
      dsimp [α,ν]
      congr 2
      ring
    rw [hex]
    rw [show -((d:ℝ)-s)/2=-α by dsimp [α];ring]
    change 0≤P*(∫t in Ioi δ,t^(α-1)*Real.exp (-(ν*(t+ε)))) ∧
      P*(∫t in Ioi δ,t^(α-1)*Real.exp (-(ν*(t+ε))))≤a*ν^(-α)
    constructor
    · apply mul_nonneg hP.le
      apply setIntegral_nonneg measurableSet_Ioi
      intro t ht
      exact mul_nonneg (Real.rpow_nonneg (hδ.trans ht.le) _) (Real.exp_pos _).le
    · exact (mul_le_mul_of_nonneg_left hbound hP.le).trans_eq heval

  have frequency_ge_two (d:ℕ) (k:Fin d→ℤ) (hk:k≠0):
      2≤4*Real.pi^2*∑j,(k j:ℝ)^2:=by
    have hn:=nonzero_norm_sq k hk
    have hpi:=Real.pi_gt_three
    nlinarith [mul_nonneg (show 0≤4*Real.pi^2-2 by nlinarith) (show 0≤∑j,(k j:ℝ)^2 by positivity)]
  have coefficient_gaussian_bound (d:ℕ) (s a:ℝ) (hsd:s<(d:ℝ)) (ha:0<a)
      (δ ε:ℝ) (hδ:0<δ) (hε:0≤ε) (k:Fin d→ℤ):
      RieszMellinCoefficient d s a δ ε k≤a*Real.exp (-(2*Real.pi^2*δ)*∑j,(k j:ℝ)^2):=by
    classical
    by_cases hk:k=0
    · simp [RieszMellinCoefficient,hk,ha.le]
    let α:=((d:ℝ)-s)/2
    let ν:=4*Real.pi^2*∑j,(k j:ℝ)^2
    let E:=Real.exp (-(ν*δ/2))
    have hα:0<α:=by dsimp [α];linarith
    have hν:2≤ν:=frequency_ge_two d k hk
    have hg:IntegrableOn (fun t:ℝ=>t^(α-1)*Real.exp (-t)) (Ioi 0) volume:=by
      simpa only [mul_comm] using Real.GammaIntegral_convergent hα
    have hgd:IntegrableOn (fun t:ℝ=>E*(t^(α-1)*Real.exp (-t))) (Ioi δ) volume:=
      (hg.mono_set (Ioi_subset_Ioi hδ.le)).const_mul E
    have hpt:∀t:ℝ,δ<t→t^(α-1)*Real.exp (-4*Real.pi^2*(t+ε)*∑j,(k j:ℝ)^2)≤
        E*(t^(α-1)*Real.exp (-t)):=by
      intro t ht
      have ht0:0<t:=hδ.trans ht
      have hex:Real.exp (-4*Real.pi^2*(t+ε)*∑j,(k j:ℝ)^2)≤E*Real.exp (-t):=by
        rw [←Real.exp_add]
        apply Real.exp_le_exp.mpr
        change -4*Real.pi^2*(t+ε)*∑j,(k j:ℝ)^2≤-(ν*δ/2)+(-t)
        have he: -4*Real.pi^2*(t+ε)*∑j,(k j:ℝ)^2=-(ν*(t+ε)):=by dsimp [ν];ring
        rw [he]
        nlinarith [mul_nonneg (show 0≤ν-2 by linarith) ht0.le,mul_nonneg (show 0≤ν by linarith) (show 0≤t-δ by linarith),mul_nonneg (show 0≤ν by linarith) hε]
      calc
        _ ≤ t^(α-1)*(E*Real.exp (-t)):=mul_le_mul_of_nonneg_left hex (Real.rpow_nonneg ht0.le _)
        _ = E*(t^(α-1)*Real.exp (-t)):=by ring
    have hi:IntegrableOn (fun t:ℝ=>t^(α-1)*Real.exp (-4*Real.pi^2*(t+ε)*∑j,(k j:ℝ)^2)) (Ioi δ) volume:=by
      apply hgd.mono' ((measurable_id.pow_const _).mul
        ((((measurable_const.mul measurable_const).mul (measurable_id.add_const ε)).mul measurable_const).exp)).aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      change ‖t^(α-1)*Real.exp (-4*Real.pi^2*(t+ε)*∑j,(k j:ℝ)^2)‖≤_
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (hδ.trans ht).le _) (Real.exp_pos _).le)]
      exact hpt t ht
    have hb:(∫t in Ioi δ,t^(α-1)*Real.exp (-4*Real.pi^2*(t+ε)*∑j,(k j:ℝ)^2))≤
        E*(∫t in Ioi 0,t^(α-1)*Real.exp (-t)):=by
      refine (integral_mono_ae hi hgd (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht;exact hpt t ht)).trans ?_
      rw [integral_const_mul]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply setIntegral_mono_set hg
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le
      · exact Eventually.of_forall (Ioi_subset_Ioi hδ.le)
    have hΓ: (∫t in Ioi 0,t^(α-1)*Real.exp (-t))=Real.Gamma α:=by
      simpa using Real.integral_rpow_mul_exp_neg_mul_Ioi hα (by norm_num : (0:ℝ)<1)
    simp only [RieszMellinCoefficient,if_neg hk]
    have hP:0≤a/Real.Gamma α:=by positivity
    refine (mul_le_mul_of_nonneg_left hb hP).trans_eq ?_
    rw [hΓ]
    dsimp [E,ν]
    have he:-(4*Real.pi^2*(∑j,(k j:ℝ)^2)*δ/2)=-(2*Real.pi^2*δ)*∑j,(k j:ℝ)^2:=by ring
    rw [he]
    field_simp [ne_of_gt (Real.Gamma_pos_of_pos hα)]
  have coefficient_summable (d:ℕ) (s a:ℝ) (hsd:s<(d:ℝ)) (ha:0<a)
      (δ ε:ℝ) (hδ:0<δ) (hε:0≤ε):Summable (RieszMellinCoefficient d s a δ ε):=by
    exact Summable.of_nonneg_of_le (fun k=>(coefficient_bounds d s a hsd ha δ ε hδ.le hε k).1)
      (fun k=>coefficient_gaussian_bound d s a hsd ha δ ε hδ hε k)
      ((gaussian_lattice_summable d (2*Real.pi^2*δ) (by positivity)).mul_left a)
  refine ⟨coefficient_summable d s a hsd ha δ ε hδ hε,
    coefficient_even d s a δ ε,?_⟩
  intro k
  exact ⟨(coefficient_bounds d s a hsd ha δ ε hδ.le hε k).1,
    (coefficient_bounds d s a hsd ha δ ε hδ.le hε k).2,
    coefficient_gaussian_bound d s a hsd ha δ ε hδ hε k⟩
