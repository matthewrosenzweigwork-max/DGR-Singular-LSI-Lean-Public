module

public import Tablet.RieszMellinLong
public import Tablet.HeatKernelFacts
public import Tablet.RieszGaussianImageRemainder
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

@[expose] public section
open MeasureTheory Set Filter
open scoped Topology
-- [TABLET NODE: RieszMellinLongBound]
theorem RieszMellinLongBound (d:ℕ) (hd:2≤d) (s a:ℝ) (hs:0≤s)
    (hsd:s<(d:ℝ)) (ha:0<a) :
    ∃A:ℝ,0<A ∧ ∀δ ε:ℝ,0<δ→δ≤1→0≤ε→
      (∀x:UnitAddTorus (Fin d),IntegrableOn
        (fun t:ℝ=>t^(((d:ℝ)-s)/2-1)*(HeatKernel d (t+ε) x-1)) (Ioi δ) volume) ∧
      ∀x:UnitAddTorus (Fin d),|RieszMellinLong d s a δ ε x|≤
        A*(if s=0 then 1+|Real.log δ| else δ^(-s/2)) := by
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
  
  have heat_joint_measurable (d:ℕ) :
      Measurable (fun p:ℝ×UnitAddTorus (Fin d)=>HeatKernel d p.1 p.2) := by
    unfold HeatKernel
    simp_rw [cos_eq_character_re]
    apply Measurable.tsum
    intro k
    exact ((measurable_const.mul measurable_fst).mul measurable_const).exp.mul
      ((Complex.continuous_re.comp (UnitAddTorus.mFourier k).continuous).measurable.comp measurable_snd)
  
  have power_mass (α δ:ℝ) (hα:0<α) (hδ:0<δ) :
      (∫t in Ioc (0:ℝ) δ,t^(α-1))=δ^α/α := by
    rw [←intervalIntegral.integral_of_le hδ.le,integral_rpow (Or.inl (by linarith))]
    simp only [sub_add_cancel,Real.zero_rpow (ne_of_gt hα),sub_zero]
  have power_integrable (α δ:ℝ) (hα:0<α) (hδ:0<δ) :
      IntegrableOn (fun t:ℝ=>t^(α-1)) (Ioc 0 δ) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hδ.le).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))

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
  
  have heat_decay (d : ℕ) : ∃C:ℝ,0≤C ∧ ∀(t ε:ℝ),1≤t → 0≤ε →
      ∀x:UnitAddTorus (Fin d),|HeatKernel d (t+ε) x-1|≤C*Real.exp (-t) := by
    classical
    let C := ∑' k:Fin d→ℤ,Real.exp (-(∑j,(k j:ℝ)^2))
    have hg := gaussian_lattice_summable d 1 zero_lt_one
    have hg' : Summable (fun k:Fin d→ℤ=>Real.exp (-(∑j,(k j:ℝ)^2))) := by simpa using hg
    refine ⟨C,tsum_nonneg (fun _=>Real.exp_nonneg _),?_⟩
    intro t ε ht hε x
    let f := fun k:Fin d→ℤ=>Real.exp (-4*Real.pi^2*(t+ε)*∑j,(k j:ℝ)^2)*
      Real.cos (2*Real.pi*∑j,(k j:ℝ)*(AddCircle.equivIco (1:ℝ) 0 (x j):ℝ))
    have ht0 : 0<t+ε := by linarith
    have hgTime := gaussian_lattice_summable d (4*Real.pi^2*(t+ε)) (by positivity)
    have hfg (k) : ‖f k‖≤Real.exp (-4*Real.pi^2*(t+ε)*∑j,(k j:ℝ)^2) := by
      simp only [f,Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (Real.exp_nonneg _) (Real.abs_cos_le_one _)
    have hgTime' : Summable (fun k:Fin d→ℤ=>Real.exp (-4*Real.pi^2*(t+ε)*∑j,(k j:ℝ)^2)) := by
      convert hgTime using 1 <;> ring_nf
    have hf : Summable f := summable_norm_iff.mp (Summable.of_nonneg_of_le (fun _=>norm_nonneg _) hfg hgTime')
    have hnonzero (k:Fin d→ℤ) : ‖if k=0 then (0:ℝ) else f k‖ ≤
        Real.exp (-t)*Real.exp (-(∑j,(k j:ℝ)^2)) := by
      by_cases hk:k=0
      · simp [hk,Real.exp_nonneg]
      · simp only [hk,↓reduceIte]
        apply (hfg k).trans
        rw [←Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hq := nonzero_norm_sq k hk
        have hqpos : 0≤∑j,(k j:ℝ)^2 := Finset.sum_nonneg (fun _ _=>sq_nonneg _)
        have hπ : 2≤4*Real.pi^2 := by nlinarith [Real.pi_gt_three]
        have hprod := mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hq)
        have htq := mul_le_mul_of_nonneg_right ht hqpos
        have heq := mul_nonneg hε hqpos
        nlinarith [mul_le_mul_of_nonneg_right hπ (mul_nonneg (by linarith : 0≤t+ε) hqpos)]
    have hs := Summable.of_nonneg_of_le (fun k=>norm_nonneg _) hnonzero (hg'.mul_left (Real.exp (-t)))
    have he : HeatKernel d (t+ε) x-1=∑'k:Fin d→ℤ,if k=0 then 0 else f k := by
      have ht := hf.tsum_eq_add_tsum_ite 0
      have h0 : f 0=1 := by simp [f]
      change (∑'k,f k)-1=_
      rw [ht,h0]
      ring
    rw [he,←Real.norm_eq_abs]
    calc
      _ ≤ ∑'k:Fin d→ℤ,‖if k=0 then (0:ℝ) else f k‖ := norm_tsum_le_tsum_norm hs
      _ ≤ ∑'k:Fin d→ℤ,Real.exp (-t)*Real.exp (-(∑j,(k j:ℝ)^2)) :=
        Summable.tsum_le_tsum hnonzero hs (hg'.mul_left (Real.exp (-t)))
      _ = C*Real.exp (-t) := by rw [tsum_mul_left];exact mul_comm _ _
  
  have heat_origin_sum (d:ℕ)(t:ℝ) : HeatKernel d t 0 =
      ∑'k:Fin d→ℤ,Real.exp (-4*Real.pi^2*t*∑j,(k j:ℝ)^2) := by
    have h0 : ((AddCircle.equivIco (1:ℝ) 0) 0 : ℝ) = 0 := by
      simpa using (AddCircle.equivIco_coe_of_mem (p:=(1:ℝ)) (a:=0) (y:=0) (by norm_num))
    simp [HeatKernel,h0]
  have heat_shift_abs_origin (d:ℕ)(t ε:ℝ)(ht:0<t)(hε:0≤ε)(x:UnitAddTorus (Fin d)) :
      |HeatKernel d (t+ε) x|≤HeatKernel d t 0 := by
    let f:=fun k:Fin d→ℤ=>Real.exp (-4*Real.pi^2*(t+ε)*∑j,(k j:ℝ)^2)*
      Real.cos (2*Real.pi*∑j,(k j:ℝ)*(AddCircle.equivIco (1:ℝ) 0 (x j):ℝ))
    have hs:Summable (fun k:Fin d→ℤ=>Real.exp (-4*Real.pi^2*t*∑j,(k j:ℝ)^2)):=by
      convert gaussian_lattice_summable d (4*Real.pi^2*t) (by positivity) using 1 <;>ring_nf
    have hb(k):‖f k‖≤Real.exp (-4*Real.pi^2*t*∑j,(k j:ℝ)^2):=by
      simp only [f,Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
      apply (mul_le_of_le_one_right (Real.exp_nonneg _) (Real.abs_cos_le_one _)).trans
      apply Real.exp_le_exp.mpr
      have hn:0≤∑j,(k j:ℝ)^2:=Finset.sum_nonneg fun _ _=>sq_nonneg _
      nlinarith [mul_nonneg (show 0≤4*Real.pi^2 by positivity) (mul_nonneg hε hn)]
    have hn:Summable (fun k=>‖f k‖):=Summable.of_nonneg_of_le (fun _=>norm_nonneg _) hb hs
    rw [heat_origin_sum]
    change |∑'k,f k|≤_
    rw [←Real.norm_eq_abs]
    exact (norm_tsum_le_tsum_norm hn).trans (Summable.tsum_le_tsum hb hn hs)
  
  
  have heat_origin_small_bound (d:ℕ) : ∃C:ℝ,0≤C ∧ ∀t:ℝ,0<t→t≤1→
      HeatKernel d t 0≤C*t^(-(d:ℝ)/2) := by
    let S:=∑'n:Fin d→ℤ,Real.exp (-(∑j,(n j:ℝ)^2)/4)
    have hs:Summable (fun n:Fin d→ℤ=>Real.exp (-(∑j,(n j:ℝ)^2)/4)):=by
      convert gaussian_lattice_summable d (1/4) (by norm_num) using 1
      funext n;congr 1;ring
    let C:=(4*Real.pi)^(-(d:ℝ)/2)*S
    refine ⟨C,mul_nonneg (Real.rpow_nonneg (by positivity) _) (tsum_nonneg fun _=>Real.exp_nonneg _),?_⟩
    intro t ht ht1
    have hb(n:Fin d→ℤ):Real.exp (-(∑j,(n j:ℝ)^2)/(4*t))≤Real.exp (-(∑j,(n j:ℝ)^2)/4):=by
      apply Real.exp_le_exp.mpr
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have hn:0≤∑j,(n j:ℝ)^2:=Finset.sum_nonneg fun _ _=>sq_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left ht1 hn]
    have hs':Summable (fun n:Fin d→ℤ=>Real.exp (-(∑j,(n j:ℝ)^2)/(4*t))):=
      Summable.of_nonneg_of_le (fun _=>Real.exp_nonneg _) hb hs
    have hK:=(RieszGaussianImageRemainder d).1 t ht (0:EuclideanSpace ℝ (Fin d))
    have hz:TorusLift d (0:EuclideanSpace ℝ (Fin d))=0:=by funext j;rfl
    rw [hz] at hK
    simp only [PiLp.zero_apply,zero_add] at hK
    rw [hK]
    calc
      _ ≤ (4*Real.pi*t)^(-(d:ℝ)/2)*S:=
        mul_le_mul_of_nonneg_left (hs'.tsum_le_tsum hb hs) (Real.rpow_nonneg (by positivity) _)
      _ = C*t^(-(d:ℝ)/2):=by
        rw [Real.mul_rpow (by positivity) ht.le]
        dsimp[C]
        ring

  have power_away_integrable (p δ:ℝ) (hδ:0<δ) :
      IntegrableOn (fun t:ℝ=>t^p) (Ioc δ 1) volume := by
    have hc:ContinuousOn (fun t:ℝ=>t^p) (Icc δ 1):=fun t ht=>
      (Real.continuousAt_rpow_const t p (Or.inl (ne_of_gt (hδ.trans_le ht.1)))).continuousWithinAt
    exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have long_integrable (d:ℕ) (α:ℝ) (hα:0<α) (δ ε:ℝ) (hδ:0<δ) (hδ1:δ≤1)
      (hε:0≤ε) (x:UnitAddTorus (Fin d)) :
      IntegrableOn (fun t:ℝ=>t^(α-1)*(HeatKernel d (t+ε) x-1)) (Ioi δ) volume := by
    obtain ⟨C,hC,hsmall⟩:=heat_origin_small_bound d
    obtain ⟨L,hL,hlarge⟩:=heat_decay d
    have hm:Measurable (fun t:ℝ=>t^(α-1)*(HeatKernel d (t+ε) x-1)):=
      (measurable_id.pow_const _).mul (((heat_joint_measurable d).comp
        ((measurable_id.add_const ε).prodMk measurable_const)).sub_const 1)
    have hnear:IntegrableOn (fun t:ℝ=>t^(α-1)*(HeatKernel d (t+ε) x-1)) (Ioc δ 1) volume:=by
      apply (((power_away_integrable (α-1-(d:ℝ)/2) δ hδ).const_mul C).add
        (power_away_integrable (α-1) δ hδ)).mono' hm.aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0:0<t:=hδ.trans ht.1
      have hp:|HeatKernel d (t+ε) x-1|≤C*t^(-(d:ℝ)/2)+1:=by
        have he:|HeatKernel d (t+ε) x-1|≤|HeatKernel d (t+ε) x|+1:=by simpa using abs_sub _ (1:ℝ)
        exact he.trans (by simpa only [add_comm] using add_le_add_left ((heat_shift_abs_origin d t ε ht0 hε x).trans (hsmall t ht0 ht.2)) 1)
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
      calc
        _ ≤ t^(α-1)*(C*t^(-(d:ℝ)/2)+1):=mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg ht0.le _)
        _ = C*t^(α-1-(d:ℝ)/2)+t^(α-1):=by
          rw [mul_add,mul_one,←mul_assoc,mul_comm (t^(α-1)) C,mul_assoc,←Real.rpow_add ht0]
          congr 1
          congr 1
          ring
    have hfar:IntegrableOn (fun t:ℝ=>t^(α-1)*(HeatKernel d (t+ε) x-1)) (Ioi 1) volume:=by
      have hg0:IntegrableOn (fun t:ℝ=>t^(α-1)*Real.exp (-t)) (Ioi 0) volume:=by
        simpa only [mul_comm] using Real.GammaIntegral_convergent hα
      have hg:=hg0.mono_set (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤1))
      apply (hg.const_mul L).mono' hm.aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0:0<t:=lt_trans zero_lt_one ht
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
      calc
        _ ≤ t^(α-1)*(L*Real.exp (-t)):=mul_le_mul_of_nonneg_left (hlarge t ε ht.le hε x) (Real.rpow_nonneg ht0.le _)
        _ = L*(t^(α-1)*Real.exp (-t)):=by ring
    rw [←Ioc_union_Ioi_eq_Ioi hδ1,integrableOn_union]
    exact ⟨hnear,hfar⟩
  have long_norm_envelope (d:ℕ) (α:ℝ) (hα:0<α) :
      ∃C:ℝ,0≤C ∧ ∃L:ℝ,0≤L ∧ ∀δ ε:ℝ,0<δ→δ≤1→0≤ε→∀x:UnitAddTorus (Fin d),
        |∫t in Ioi δ,t^(α-1)*(HeatKernel d (t+ε) x-1)| ≤
        C*(∫t in Ioc δ 1,t^(α-1-(d:ℝ)/2))+(∫t in Ioc δ 1,t^(α-1))+
          L*(∫t in Ioi 1,t^(α-1)*Real.exp (-t)) := by
    obtain ⟨C,hC,hsmall⟩:=heat_origin_small_bound d
    obtain ⟨L,hL,hlarge⟩:=heat_decay d
    refine ⟨C,hC,L,hL,?_⟩
    intro δ ε hδ hδ1 hε x
    have hi:=long_integrable d α hα δ ε hδ hδ1 hε x
    have hin:=hi.mono_set (show Ioc δ 1 ⊆ Ioi δ from fun _ ht=>ht.1)
    have hif:=hi.mono_set (Ioi_subset_Ioi hδ1)
    have hbn:IntegrableOn (fun t:ℝ=>C*t^(α-1-(d:ℝ)/2)+t^(α-1)) (Ioc δ 1) volume:=
      ((power_away_integrable _ δ hδ).const_mul C).add (power_away_integrable _ δ hδ)
    have hn:|∫t in Ioc δ 1,t^(α-1)*(HeatKernel d (t+ε) x-1)|≤
        C*(∫t in Ioc δ 1,t^(α-1-(d:ℝ)/2))+(∫t in Ioc δ 1,t^(α-1)):=by
      have hb:=norm_integral_le_of_norm_le hbn (show ∀ᵐt∂volume.restrict (Ioc δ 1),
        ‖t^(α-1)*(HeatKernel d (t+ε) x-1)‖≤C*t^(α-1-(d:ℝ)/2)+t^(α-1) from by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        have ht0:0<t:=hδ.trans ht.1
        have hp:|HeatKernel d (t+ε) x-1|≤C*t^(-(d:ℝ)/2)+1:=by
          have he:|HeatKernel d (t+ε) x-1|≤|HeatKernel d (t+ε) x|+1:=by simpa using abs_sub _ (1:ℝ)
          exact he.trans (by simpa only [add_comm] using add_le_add_left ((heat_shift_abs_origin d t ε ht0 hε x).trans (hsmall t ht0 ht.2)) 1)
        rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
        calc
          _ ≤ t^(α-1)*(C*t^(-(d:ℝ)/2)+1):=mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg ht0.le _)
          _ = C*t^(α-1-(d:ℝ)/2)+t^(α-1):=by
            rw [mul_add,mul_one,←mul_assoc,mul_comm (t^(α-1)) C,mul_assoc,←Real.rpow_add ht0]
            congr 1
            congr 1
            ring)
      simpa only [Real.norm_eq_abs,integral_add ((power_away_integrable _ δ hδ).const_mul C)
        (power_away_integrable _ δ hδ),integral_const_mul] using hb
    have hg0:IntegrableOn (fun t:ℝ=>t^(α-1)*Real.exp (-t)) (Ioi 0) volume:=by
      simpa only [mul_comm] using Real.GammaIntegral_convergent hα
    have hg:=hg0.mono_set (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤1))
    have hf:|∫t in Ioi 1,t^(α-1)*(HeatKernel d (t+ε) x-1)|≤
        L*(∫t in Ioi 1,t^(α-1)*Real.exp (-t)):=by
      have hb:=norm_integral_le_of_norm_le (hg.const_mul L) (show ∀ᵐt∂volume.restrict (Ioi 1),
        ‖t^(α-1)*(HeatKernel d (t+ε) x-1)‖≤L*(t^(α-1)*Real.exp (-t)) from by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0:0<t:=lt_trans zero_lt_one ht
        rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
        calc
          _ ≤ t^(α-1)*(L*Real.exp (-t)):=mul_le_mul_of_nonneg_left (hlarge t ε ht.le hε x) (Real.rpow_nonneg ht0.le _)
          _ = L*(t^(α-1)*Real.exp (-t)):=by ring)
      simpa only [Real.norm_eq_abs,integral_const_mul] using hb
    rw [←Ioc_union_Ioi_eq_Ioi hδ1,setIntegral_union (by
      apply disjoint_left.mpr
      intro t ht hn
      exact (not_lt_of_ge ht.2) hn) measurableSet_Ioi hin hif]
    exact (abs_add_le _ _).trans (add_le_add hn hf)

  have power_critical_integral (s δ:ℝ) (hs:0<s) (hδ:0<δ) (hδ1:δ≤1):
      (∫t in Ioc δ 1,t^(-s/2-1))≤(2/s)*δ^(-s/2):=by
    have hz:0∉uIcc δ 1:=by
      rw [uIcc_of_le hδ1]
      intro h
      exact (not_le_of_gt hδ) h.1
    rw [←intervalIntegral.integral_of_le hδ1,
      integral_rpow (Or.inr ⟨by linarith,hz⟩)]
    have hex:-s/2-1+1=-s/2:=by ring
    rw [hex,Real.one_rpow]
    have hs0:s≠0:=ne_of_gt hs
    have heq:(1-δ^(-s/2))/(-s/2)=(2/s)*(δ^(-s/2)-1):=by field_simp;ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left (sub_le_self _ zero_le_one) (by positivity)
  have power_log_integral (δ:ℝ) (hδ:0<δ) (hδ1:δ≤1):
      (∫t in Ioc δ 1,t^(-(1:ℝ)))=-Real.log δ:=by
    have hz:0∉uIcc δ 1:=by
      rw [uIcc_of_le hδ1]
      intro h
      exact (not_le_of_gt hδ) h.1
    rw [←intervalIntegral.integral_of_le hδ1]
    simp_rw [Real.rpow_neg_one]
    rw [integral_inv hz,one_div,Real.log_inv]
  have power_short_mass_bound (α δ:ℝ) (hα:0<α) (hδ:0<δ) (hδ1:δ≤1):
      (∫t in Ioc δ 1,t^(α-1))≤1/α:=by
    have hi:=power_integrable α 1 hα zero_lt_one
    have hb:(∫t in Ioc δ 1,t^(α-1))≤∫t in Ioc 0 1,t^(α-1):=by
      apply setIntegral_mono_set hi
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact Real.rpow_nonneg ht.1.le _
      · exact Filter.Eventually.of_forall (fun t ht=>⟨hδ.trans ht.1,ht.2⟩)
    exact hb.trans_eq (by simpa using power_mass α 1 hα zero_lt_one)

  have long_power_bound (d:ℕ) (s a:ℝ) (hs:0<s) (hsd:s<(d:ℝ)) (ha:0<a):
      ∃A:ℝ,0<A ∧ ∀δ ε:ℝ,0<δ→δ≤1→0≤ε→∀x:UnitAddTorus (Fin d),
        |RieszMellinLong d s a δ ε x|≤A*δ^(-s/2):=by
    let α:=((d:ℝ)-s)/2
    have hα:0<α:=by dsimp [α];linarith
    let P:=a/Real.Gamma α
    have hP:0<P:=div_pos ha (Real.Gamma_pos_of_pos hα)
    obtain ⟨C,hC,L,hL,hbound⟩:=long_norm_envelope d α hα
    let H:=∫t in Ioi 1,t^(α-1)*Real.exp (-t)
    have hH:0≤H:=setIntegral_nonneg measurableSet_Ioi (fun t ht=>mul_nonneg
      (Real.rpow_nonneg (le_trans zero_le_one ht.le) _) (Real.exp_pos _).le)
    let D:=C*(2/s)+1/α+L*H
    have hD:0<D:=by dsimp [D];positivity
    refine ⟨P*D,mul_pos hP hD,?_⟩
    intro δ ε hδ hδ1 hε x
    have hp:1≤δ^(-s/2):=Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
    have he:α-1-(d:ℝ)/2=-s/2-1:=by dsimp [α];ring
    have hb:=hbound δ ε hδ hδ1 hε x
    rw [he] at hb
    have hraw:|∫t in Ioi δ,t^(α-1)*(HeatKernel d (t+ε) x-1)|≤D*δ^(-s/2):=by
      calc
        _ ≤ C*((2/s)*δ^(-s/2))+1/α+L*H:=hb.trans (add_le_add
          (add_le_add (mul_le_mul_of_nonneg_left (power_critical_integral s δ hs hδ hδ1) hC)
            (power_short_mass_bound α δ hα hδ hδ1)) le_rfl)
        _ ≤ C*((2/s)*δ^(-s/2))+(1/α+L*H)*δ^(-s/2):=by
          have hm:=mul_le_mul_of_nonneg_left hp (show 0≤1/α+L*H by positivity)
          nlinarith
        _ = D*δ^(-s/2):=by dsimp [D];ring
    change |P*(∫t in Ioi δ,t^(α-1)*(HeatKernel d (t+ε) x-1))|≤_
    rw [abs_mul,abs_of_pos hP]
    exact (mul_le_mul_of_nonneg_left hraw hP.le).trans_eq (by ring)
  have long_log_bound (d:ℕ) (a:ℝ) (hd:0<d) (ha:0<a):
      ∃A:ℝ,0<A ∧ ∀δ ε:ℝ,0<δ→δ≤1→0≤ε→∀x:UnitAddTorus (Fin d),
        |RieszMellinLong d 0 a δ ε x|≤A*(1+|Real.log δ|):=by
    let α:ℝ:=(d:ℝ)/2
    have hα:0<α:=by dsimp [α];exact div_pos (Nat.cast_pos.mpr hd) (by norm_num)
    let P:=a/Real.Gamma α
    have hP:0<P:=div_pos ha (Real.Gamma_pos_of_pos hα)
    obtain ⟨C,hC,L,hL,hbound⟩:=long_norm_envelope d α hα
    let H:=∫t in Ioi 1,t^(α-1)*Real.exp (-t)
    have hH:0≤H:=setIntegral_nonneg measurableSet_Ioi (fun t ht=>mul_nonneg
      (Real.rpow_nonneg (le_trans zero_le_one ht.le) _) (Real.exp_pos _).le)
    let D:=C+1/α+L*H
    have hD:0<D:=by dsimp [D];positivity
    refine ⟨P*D,mul_pos hP hD,?_⟩
    intro δ ε hδ hδ1 hε x
    have he:α-1-(d:ℝ)/2=-(1:ℝ):=by dsimp [α];ring
    have hb:=hbound δ ε hδ hδ1 hε x
    rw [he,power_log_integral δ hδ hδ1] at hb
    have hraw:|∫t in Ioi δ,t^(α-1)*(HeatKernel d (t+ε) x-1)|≤D*(1+|Real.log δ|):=by
      calc
        _ ≤ C*|Real.log δ|+1/α+L*H:=hb.trans (add_le_add
          (add_le_add (mul_le_mul_of_nonneg_left (neg_le_abs _) hC)
            (power_short_mass_bound α δ hα hδ hδ1)) le_rfl)
        _ ≤ D*(1+|Real.log δ|):=by
          have hz:0≤1/α+L*H:=by positivity
          have hm:=mul_nonneg hz (abs_nonneg (Real.log δ))
          dsimp [D]
          nlinarith
    unfold RieszMellinLong
    simp only [sub_zero]
    change |P*(∫t in Ioi δ,t^(α-1)*(HeatKernel d (t+ε) x-1))|≤_
    rw [abs_mul,abs_of_pos hP]
    exact (mul_le_mul_of_nonneg_left hraw hP.le).trans_eq (by ring)
  have hα:0<((d:ℝ)-s)/2:=by linarith
  by_cases hs0:s=0
  · subst s
    obtain ⟨A,hA,hbound⟩:=long_log_bound d a (by omega) ha
    refine ⟨A,hA,?_⟩
    intro δ ε hδ hδ1 hε
    refine ⟨fun x=>long_integrable d (((d:ℝ)-0)/2) hα δ ε hδ hδ1 hε x,?_⟩
    intro x
    simpa using hbound δ ε hδ hδ1 hε x
  · obtain ⟨A,hA,hbound⟩:=long_power_bound d s a (lt_of_le_of_ne hs (Ne.symm hs0)) hsd ha
    refine ⟨A,hA,?_⟩
    intro δ ε hδ hδ1 hε
    refine ⟨fun x=>long_integrable d (((d:ℝ)-s)/2) hα δ ε hδ hδ1 hε x,?_⟩
    intro x
    simpa only [if_neg hs0] using hbound δ ε hδ hδ1 hε x
