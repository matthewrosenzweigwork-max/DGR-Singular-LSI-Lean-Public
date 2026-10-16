import Tablet.RieszMellinNearCap
import Tablet.RieszMellinLongBound
import Tablet.RieszL1Foundation
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
open MeasureTheory Set Filter
open scoped Topology
-- [TABLET NODE: RieszMellinDecomposition]
theorem RieszMellinDecomposition (d:ℕ) (hd:2≤d) (s a:ℝ) (hs:0≤s)
    (hsd:s<(d:ℝ)) (ha:0<a) (δ ε:ℝ) (hδ:0<δ) (hδ1:δ≤1) (hε:0≤ε) :
    let α:=((d:ℝ)-s)/2
    let m:=(a/Real.Gamma α)*δ^α/α
    let L:=RieszMellinLong d s a δ ε
    Measurable L ∧ Integrable L volume ∧ (∫x:UnitAddTorus (Fin d),L x)=0 ∧
      RieszKernel d s a ε =ᵐ[volume]
        (fun x=>RieszMellinNear d s a δ ε x+L x-m) := by
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
  

  have joint_mellin_integrable (d:ℕ) (α:ℝ) (hα:0<α) (ε:ℝ) (hε:0≤ε) :
      Integrable (fun p:ℝ×UnitAddTorus (Fin d)=>p.1^(α-1)*(HeatKernel d (p.1+ε) p.2-1))
        ((volume.restrict (Ioi 0)).prod (volume:Measure (UnitAddTorus (Fin d)))) := by
    have heat_continuous (d:ℕ) (u:ℝ) (hu:0<u):Continuous (HeatKernel d u):=(HeatKernelFacts d u hu).1
    have heat_mass (d:ℕ) (u:ℝ) (hu:0<u):(∫x:UnitAddTorus (Fin d),HeatKernel d u x)=1:=
      (HeatKernelFacts d u hu).2.2.2.1
    letI circle_probability : IsProbabilityMeasure (volume : Measure (AddCircle (1:ℝ))) := by
      rw [AddCircle.volume_eq_smul_haarAddCircle]
      simp
      infer_instance
    
    let integrand (d : ℕ) (α ε : ℝ) (p : ℝ × UnitAddTorus (Fin d)) : ℝ :=
      p.1^(α-1)*(HeatKernel d (p.1+ε) p.2-1)
    let majorant (α C t : ℝ) : ℝ :=
      (Set.Ioc (0:ℝ) 1).indicator (fun u:ℝ=>2*u^(α-1)) t + C*(t^(α-1)*Real.exp (-t))
    
    have integrand_measurable (d : ℕ) (α ε : ℝ) : Measurable (integrand d α ε) := by
      exact (measurable_fst.pow_const _).mul
        (((heat_joint_measurable d).comp
          ((measurable_fst.add_const ε).prodMk measurable_snd)).sub measurable_const)
    
    have majorant_integrable {α C : ℝ} (hα : 0<α) :
        Integrable (majorant α C) (volume.restrict (Set.Ioi 0)) := by
      have hr : IntegrableOn (fun t:ℝ=>t^(α-1)) (Set.Ioc 0 1) volume :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
          (intervalIntegral.intervalIntegrable_rpow' (by linarith))
      have hn : Integrable ((Set.Ioc (0:ℝ) 1).indicator (fun t:ℝ=>2*t^(α-1))) volume :=
        (integrable_indicator_iff measurableSet_Ioc).mpr (hr.const_mul 2)
      have he : Integrable (fun t:ℝ=>t^(α-1)*Real.exp (-t)) (volume.restrict (Set.Ioi 0)) := by
        change IntegrableOn _ (Set.Ioi 0) volume
        simpa only [mul_comm] using Real.GammaIntegral_convergent hα
      exact (hn.mono_measure Measure.restrict_le_self).add (he.const_mul C)
    
    have majorant_nonneg {α C t : ℝ} (hC : 0≤C) (ht : 0<t) : 0≤majorant α C t := by
      unfold majorant
      apply add_nonneg
      · apply Set.indicator_nonneg
        intro u hu
        exact mul_nonneg (by norm_num) (Real.rpow_nonneg hu.1.le _)
      · exact mul_nonneg hC (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_nonneg _))
    
    have heat_integrable (d : ℕ) (u : ℝ) (hu : 0<u) :
        Integrable (HeatKernel d u) (volume:Measure (UnitAddTorus (Fin d))) :=
      (heat_continuous d u hu).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    
    have heat_abs_diff_integral (d : ℕ) (u : ℝ) (hu : 0<u) :
        (∫x:UnitAddTorus (Fin d),|HeatKernel d u x-1|)≤2 := by
      have hi := heat_integrable d u hu
      have hp := (HeatKernelFacts d u hu).2.1
      have hm := heat_mass d u hu
      calc
        _ ≤ ∫x:UnitAddTorus (Fin d),HeatKernel d u x+1 := by
          apply integral_mono (hi.sub (integrable_const 1)).abs (hi.add (integrable_const 1))
          intro x
          calc
            |HeatKernel d u x-1| ≤ |HeatKernel d u x|+|1| := abs_sub _ _
            _ = HeatKernel d u x+1 := by rw [abs_of_nonneg (hp x),abs_one]
        _ = 2 := by rw [integral_add hi (integrable_const 1),hm];norm_num
    
    have joint_integrable (d : ℕ) (α : ℝ) (hα : 0<α) (ε : ℝ) (hε : 0≤ε) :
        Integrable (integrand d α ε)
          ((volume.restrict (Set.Ioi 0)).prod (volume:Measure (UnitAddTorus (Fin d)))) := by
      obtain ⟨C,hC,hdec⟩ := heat_decay d
      have hm := integrand_measurable d α ε
      apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
      constructor
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        convert ((heat_integrable d (t+ε) (by exact add_pos_of_pos_of_nonneg ht hε)).sub
          (integrable_const 1)).const_mul (t^(α-1)) using 1 <;> rfl
      · apply (majorant_integrable (C:=C) hα).mono'
          (hm.stronglyMeasurable.norm.integral_prod_right').aestronglyMeasurable
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have hu : 0<t+ε := add_pos_of_pos_of_nonneg ht hε
        have hi := (heat_integrable d (t+ε) hu).sub (integrable_const 1)
        have hr : 0≤t^(α-1) := Real.rpow_nonneg ht.le _
        have hn : 0≤∫x:UnitAddTorus (Fin d),‖integrand d α ε (t,x)‖ :=
          integral_nonneg (fun _=>norm_nonneg _)
        rw [Real.norm_eq_abs,abs_of_nonneg hn]
        have heq : (∫x:UnitAddTorus (Fin d),‖integrand d α ε (t,x)‖) =
            t^(α-1)*(∫x:UnitAddTorus (Fin d),|HeatKernel d (t+ε) x-1|) := by
          simp only [integrand,Real.norm_eq_abs,abs_mul,abs_of_nonneg hr,integral_const_mul]
        rw [heq]
        by_cases ht1:t≤1
        · have hnear : (Set.Ioc (0:ℝ) 1).indicator (fun u:ℝ=>2*u^(α-1)) t=2*t^(α-1) :=
            Set.indicator_of_mem (show t∈Set.Ioc (0:ℝ) 1 from ⟨ht,ht1⟩) _
          unfold majorant
          rw [hnear]
          have htail : 0≤C*(t^(α-1)*Real.exp (-t)) := by positivity
          nlinarith [mul_le_mul_of_nonneg_left (heat_abs_diff_integral d (t+ε) hu) hr]
        · have hfar : (Set.Ioc (0:ℝ) 1).indicator (fun u:ℝ=>2*u^(α-1)) t=0 :=
            Set.indicator_of_notMem (fun h=>ht1 h.2) _
          unfold majorant
          rw [hfar,zero_add]
          have hab : (∫x:UnitAddTorus (Fin d),|HeatKernel d (t+ε) x-1|)≤C*Real.exp (-t) := by
            calc
              _ ≤ ∫x:UnitAddTorus (Fin d),C*Real.exp (-t) :=
                integral_mono hi.abs (integrable_const _) (hdec t ε (le_of_not_ge ht1) hε)
              _ = _ := by simp
          nlinarith [mul_le_mul_of_nonneg_left hab hr]
  
    exact joint_integrable d α hα ε hε
  have riesz_mellin_split (d:ℕ) (hd:2≤d) (s a:ℝ) (hsd:s<(d:ℝ))
      (δ ε:ℝ) (hδ:0<δ) (hδ1:δ≤1) (hε:0≤ε):
      RieszKernel d s a ε =ᵐ[volume]
        (fun x=>RieszMellinNear d s a δ ε x+RieszMellinLong d s a δ ε x-
          (a/Real.Gamma (((d:ℝ)-s)/2))*δ^(((d:ℝ)-s)/2)/(((d:ℝ)-s)/2)):=by
    let α:=((d:ℝ)-s)/2
    have hα:0<α:=by dsimp [α];linarith
    letI:Nonempty (Fin d):=Fin.pos_iff_nonempty.mp (by omega)
    letI:NullSingletonClass (volume:Measure (AddCircle (1:ℝ))):=by
      constructor
      intro x
      simpa using (AddCircle.volume_closedBall (T:=1) (x:=x) 0)
    have hj:=joint_mellin_integrable d α hα ε hε
    filter_upwards [hj.prod_left_ae,(volume:Measure (UnitAddTorus (Fin d))).ae_ne 0] with x hx hx0
    change IntegrableOn (fun t:ℝ=>t^(α-1)*(HeatKernel d (t+ε) x-1)) (Ioi 0) volume at hx
    have hin:=hx.mono_set (show Ioc 0 δ ⊆ Ioi 0 from fun _ ht=>ht.1)
    have hif:=hx.mono_set (Ioi_subset_Ioi hδ.le)
    have hp:=power_integrable α δ hα hδ
    have hpos:IntegrableOn (fun t:ℝ=>t^(α-1)*HeatKernel d (t+ε) x) (Ioc 0 δ) volume:=by
      apply (hin.add hp).congr
      exact Eventually.of_forall fun t=>by dsimp;ring
    have he:(∫t in Ioi 0,t^(α-1)*(HeatKernel d (t+ε) x-1))=
        (∫t in Ioc 0 δ,t^(α-1)*HeatKernel d (t+ε) x)-δ^α/α+
        (∫t in Ioi δ,t^(α-1)*(HeatKernel d (t+ε) x-1)):=by
      rw [←Ioc_union_Ioi_eq_Ioi hδ.le,setIntegral_union (by
        apply disjoint_left.mpr
        intro t ht hn
        exact (not_lt_of_ge ht.2) hn) measurableSet_Ioi hin hif]
      have hex:(fun t:ℝ=>t^(α-1)*(HeatKernel d (t+ε) x-1))=
          (fun t=>t^(α-1)*HeatKernel d (t+ε) x-t^(α-1)):=by funext t;ring
      rw [hex,integral_sub hpos hp,power_mass α δ hα hδ]
    simp only [RieszKernel,hx0,and_false,ite_false,RieszMellinNear,RieszMellinLong]
    change (a/Real.Gamma α)*(∫t in Ioi 0,t^(α-1)*(HeatKernel d (t+ε) x-1))=_
    rw [he]
    ring
  have riesz_long_properties (d:ℕ) (hd:2≤d) (s a:ℝ) (hs:0≤s) (hsd:s<(d:ℝ)) (ha:0<a)
      (δ ε:ℝ) (hδ:0<δ) (hδ1:δ≤1) (hε:0≤ε):
      Measurable (RieszMellinLong d s a δ ε) ∧
      Integrable (RieszMellinLong d s a δ ε) volume ∧
      (∫x:UnitAddTorus (Fin d),RieszMellinLong d s a δ ε x)=0 := by
    letI:IsProbabilityMeasure (volume:Measure (AddCircle (1:ℝ))):=by
      rw [AddCircle.volume_eq_smul_haarAddCircle];simp;infer_instance
    let α:=((d:ℝ)-s)/2
    let P:=a/Real.Gamma α
    let m:=P*δ^α/α
    have hm:Measurable (fun p:ℝ×UnitAddTorus (Fin d)=>p.1^(α-1)*(HeatKernel d (p.1+ε) p.2-1)):=
      (measurable_fst.pow_const _).mul (((heat_joint_measurable d).comp
        ((measurable_fst.add_const ε).prodMk measurable_snd)).sub_const 1)
    have hLm:Measurable (RieszMellinLong d s a δ ε):=by
      change Measurable (fun x=>P*(∫t in Ioi δ,t^(α-1)*(HeatKernel d (t+ε) x-1)))
      exact hm.stronglyMeasurable.integral_prod_left'.measurable.const_mul P
    obtain ⟨A,hA,hbound⟩:=RieszMellinLongBound d hd s a hs hsd ha
    have hLi:Integrable (RieszMellinLong d s a δ ε) volume:=
      Integrable.of_bound hLm.aestronglyMeasurable _ (Eventually.of_forall (fun x=>by
        simpa only [Real.norm_eq_abs] using (hbound δ ε hδ hδ1 hε).2 x))
    refine ⟨hLm,hLi,?_⟩
    have hnear:=RieszMellinNearCap d s a hsd ha δ ε hδ hε 1 le_rfl
      (fun _=>1) measurable_const (Eventually.of_forall (fun _=>by norm_num)) (by simp)
    obtain ⟨c,hc,hkernel⟩:=RieszL1Foundation d hd s a hs hsd ha
    have hki:Integrable (RieszKernel d s a ε) volume:=(hkernel ε hε).2.1
    have hkm:(∫x:UnitAddTorus (Fin d),RieszKernel d s a ε x)=0:=(hkernel ε hε).2.2.1
    have he:=integral_congr_ae (riesz_mellin_split d hd s a hsd δ ε hδ hδ1 hε)
    change (∫x:UnitAddTorus (Fin d),RieszKernel d s a ε x)=
      ∫x,RieszMellinNear d s a δ ε x+RieszMellinLong d s a δ ε x-m at he
    have hsum:Integrable (fun x=>RieszMellinNear d s a δ ε x+RieszMellinLong d s a δ ε x) volume:=hnear.2.1.add hLi
    have hadd:(∫x:UnitAddTorus (Fin d),RieszMellinNear d s a δ ε x+RieszMellinLong d s a δ ε x)=
      (∫x,RieszMellinNear d s a δ ε x)+(∫x,RieszMellinLong d s a δ ε x):=integral_add hnear.2.1 hLi
    rw [integral_sub hsum (integrable_const m),hadd,hnear.2.2.2.1,hkm] at he
    have hmconst:(∫x:UnitAddTorus (Fin d),m)=m:=by simp
    rw [hmconst] at he
    change 0=m+(∫x:UnitAddTorus (Fin d),RieszMellinLong d s a δ ε x)-m at he
    linarith
  exact ⟨(riesz_long_properties d hd s a hs hsd ha δ ε hδ hδ1 hε).1,
    (riesz_long_properties d hd s a hs hsd ha δ ε hδ hδ1 hε).2.1,
    (riesz_long_properties d hd s a hs hsd ha δ ε hδ hδ1 hε).2.2,
    riesz_mellin_split d hd s a hsd δ ε hδ hδ1 hε⟩
