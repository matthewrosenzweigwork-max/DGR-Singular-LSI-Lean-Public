module

public import Tablet.RieszL1Foundation
public import Tablet.HeatFourierCoefficients
public import Tablet.HeatOperatorBounds
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

@[expose] public section
open MeasureTheory Filter Set UnitAddTorus
open scoped Topology ComplexConjugate
set_option maxHeartbeats 1500000
-- [TABLET NODE: RieszFourierCoefficients]
theorem RieszFourierCoefficients (d : ℕ) (hd : 2 ≤ d) (s a ε : ℝ)
    (hs : 0 ≤ s) (hsd : s < (d : ℝ)) (ha : 0 < a) (hε : 0 ≤ ε)
    (k : Fin d → ℤ) (hk : k ≠ 0) :
    (∫ x, RieszKernel d s a ε x * (UnitAddTorus.mFourier k x).re ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d)))) =
      a * Real.rpow (4 * Real.pi ^ 2 * ∑ j, (k j : ℝ) ^ 2)
        (-((d : ℝ) - s) / 2) *
        Real.exp (-4 * Real.pi ^ 2 * ε * ∑ j, (k j : ℝ) ^ 2) := by
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
  
  have heat_continuous (d : ℕ) (t : ℝ) (ht : 0 < t) :
      Continuous (HeatKernel d t) := by
    have hc : 0 < 4 * Real.pi^2 * t := by positivity
    have hs := gaussian_lattice_summable d (4 * Real.pi^2 * t) hc
    have he : HeatKernel d t = fun x => ∑' k : Fin d → ℤ,
        Real.exp (-4 * Real.pi^2 * t * ∑ j, (k j : ℝ)^2) *
          (UnitAddTorus.mFourier k x).re := by
      ext x
      simp only [HeatKernel, cos_eq_character_re]
    rw [he]
    apply continuous_tsum (u := fun k : Fin d → ℤ =>
      Real.exp (-4 * Real.pi^2 * t * ∑ j, (k j : ℝ)^2))
    · intro k
      exact continuous_const.mul (Complex.continuous_re.comp (UnitAddTorus.mFourier k).continuous)
    · convert hs using 1 <;> ring_nf
    · intro k x
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      apply mul_le_of_le_one_right (Real.exp_nonneg _)
      exact (Complex.abs_re_le_norm _).trans
        (by simpa only [UnitAddTorus.mFourier_norm] using
          (UnitAddTorus.mFourier k).norm_coe_le_norm x)
  
  have heat_even (d : ℕ) (t : ℝ) (x : UnitAddTorus (Fin d)) :
      HeatKernel d t (-x) = HeatKernel d t x := by
    classical
    have hneg (k : Fin d → ℤ) :
        UnitAddTorus.mFourier k (-x) = star (UnitAddTorus.mFourier k x) := by
      change (∏ j, fourier (k j) (-x j)) =
        star (∏ j, fourier (k j) (x j))
      rw [star_prod]
      apply Finset.prod_congr rfl
      intro j _
      rw [fourier_apply, smul_neg, fourier_neg']
      rfl
    unfold HeatKernel
    apply tsum_congr
    intro k
    rw [cos_eq_character_re, cos_eq_character_re, hneg]
    rfl
  
  have heat_mass (d : ℕ) (t : ℝ) (ht : 0<t) :
      (∫x:UnitAddTorus (Fin d),HeatKernel d t x)=1 :=
    (HeatKernelFacts d t ht).2.2.2.1

  have heat_joint_measurable (d : ℕ) :
      Measurable (fun p : ℝ × UnitAddTorus (Fin d) => HeatKernel d p.1 p.2) := by
    unfold HeatKernel
    simp_rw [cos_eq_character_re]
    apply Measurable.tsum
    intro k
    exact ((measurable_const.mul measurable_fst).mul measurable_const).exp.mul
      ((Complex.continuous_re.comp (UnitAddTorus.mFourier k).continuous).measurable.comp measurable_snd)
  
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

  letI circle_null : NullSingletonClass (volume : Measure (AddCircle (1:ℝ))) := by
    constructor
    intro x
    simpa using (AddCircle.volume_closedBall (T:=1) (x:=x) 0)
  let raw (d:ℕ) (α ε:ℝ) (x:UnitAddTorus (Fin d)) : ℝ :=
    ∫t in Set.Ioi (0:ℝ),integrand d α ε (t,x)
  
  have raw_measurable (d:ℕ) (α ε:ℝ) : Measurable (raw d α ε) :=
    (integrand_measurable d α ε).stronglyMeasurable.integral_prod_left'.measurable
  
  have raw_integrable (d:ℕ) (α:ℝ) (hα:0<α) (ε:ℝ) (hε:0≤ε) :
      Integrable (raw d α ε) (volume:Measure (UnitAddTorus (Fin d))) :=
    (joint_integrable d α hα ε hε).integral_prod_right
  
  have raw_mean (d:ℕ) (α:ℝ) (hα:0<α) (ε:ℝ) (hε:0≤ε) :
      (∫x:UnitAddTorus (Fin d),raw d α ε x)=0 := by
    change (∫x:UnitAddTorus (Fin d),∫t in Set.Ioi (0:ℝ),integrand d α ε (t,x))=0
    have hi : Integrable (Function.uncurry (fun (x:UnitAddTorus (Fin d)) (t:ℝ)=>integrand d α ε (t,x)))
        (volume.prod (volume.restrict (Set.Ioi 0))) := by
      convert (joint_integrable d α hα ε hε).swap using 1 <;> rfl
    rw [integral_integral_swap hi]
    have hzero : (fun t:ℝ=>∫x:UnitAddTorus (Fin d),integrand d α ε (t,x)) =ᵐ[volume.restrict (Set.Ioi 0)] 0 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hu : 0<t+ε := add_pos_of_pos_of_nonneg ht hε
      simp only [integrand,integral_const_mul]
      rw [integral_sub (heat_integrable d (t+ε) hu) (integrable_const 1),
        heat_mass d (t+ε) hu]
      simp
    rw [integral_congr_ae hzero]
    simp only [Pi.zero_apply,integral_zero]
  
  have raw_even (d:ℕ) (α ε:ℝ) (x:UnitAddTorus (Fin d)) :
      raw d α ε (-x)=raw d α ε x := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t=>by simp only [integrand,heat_even]
  
  have riesz_ae_raw (d:ℕ) [Nonempty (Fin d)] (s a ε:ℝ) :
      RieszKernel d s a ε =ᵐ[volume]
        (fun x=>a/Real.Gamma (((d:ℝ)-s)/2)*raw d (((d:ℝ)-s)/2) ε x) := by
    filter_upwards [(volume:Measure (UnitAddTorus (Fin d))).ae_ne 0] with x hx
    simp only [RieszKernel,hx,and_false,ite_false,raw,integrand]
    rfl
  
  have volume_eq_haar (d : ℕ) :
      (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d))) =
        MeasureTheory.Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle (T := (1 : ℝ))) := by
    change MeasureTheory.Measure.pi (fun _ : Fin d =>
      (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ)))) = _
    congr 1
    funext j
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp

  have character_mean (d : ℕ) (k : Fin d → ℤ) :
      (∫ x, UnitAddTorus.mFourier k x
        ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d)))) =
          if k = 0 then (1 : ℂ) else 0 := by
    classical
    have h := (orthonormal_iff_ite.mp (UnitAddTorus.orthonormal_mFourier (d := Fin d))) (-k) 0
    simp only [ContinuousMap.inner_toLp, ← UnitAddTorus.mFourier_neg,
      ← UnitAddTorus.mFourier_add, neg_neg, zero_add, neg_eq_zero] at h
    rw [volume_eq_haar]
    exact h

  have re_mean (d : ℕ) (k : Fin d→ℤ) : (∫x,(mFourier k x).re) = if k=0 then 1 else 0 := by
    have hi : Integrable (mFourier k) (volume : Measure (UnitAddTorus (Fin d))) :=
      (mFourier k).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hh := integral_re hi
    rw [character_mean] at hh
    split_ifs at hh ⊢ <;>simpa using hh
  classical
  letI : Nonempty (Fin d) := ⟨⟨0,by omega⟩⟩
  let α : ℝ := ((d:ℝ)-s)/2
  let A : ℝ := a/Real.Gamma α
  let r : ℝ := 4*Real.pi^2*∑j,(k j:ℝ)^2
  have hα : 0<α := by dsimp [α];linarith
  have hr : 0<r := by
    have hh := nonzero_norm_sq k hk
    dsimp [r]
    positivity
  have hΓ : Real.Gamma α≠0 := ne_of_gt (Real.Gamma_pos_of_pos hα)
  have hchar x : ‖(mFourier k x).re‖≤1 := by
    rw [Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (by simpa only [mFourier_norm] using (mFourier k).norm_coe_le_norm x)
  have hjoint : Integrable (fun p:ℝ×UnitAddTorus (Fin d)=>
      integrand d α ε p*(mFourier k p.2).re)
      ((volume.restrict (Ioi 0)).prod volume) :=
    (joint_integrable d α hα ε hε).mul_bdd
      ((Complex.measurable_re.comp (mFourier k).continuous.measurable).comp measurable_snd).aestronglyMeasurable
      (Eventually.of_forall fun p=>hchar p.2)
  have hswap : Integrable (Function.uncurry (fun (x:UnitAddTorus (Fin d)) (t:ℝ)=>
      integrand d α ε (t,x)*(mFourier k x).re))
      (volume.prod (volume.restrict (Ioi 0))) := hjoint.swap
  have hrep := (riesz_ae_raw d s a ε).mono (fun x hx=>congrArg (fun z:ℝ=>z*(mFourier k x).re) hx)
  rw [integral_congr_ae hrep]
  change (∫x,A*(∫t in Ioi 0,integrand d α ε (t,x))*(mFourier k x).re)=_
  have hconvert : (∫x,A*(∫t in Ioi 0,integrand d α ε (t,x))*(mFourier k x).re)=
      A*(∫x,∫t in Ioi 0,integrand d α ε (t,x)*(mFourier k x).re) := by
    simp_rw [integral_mul_const]
    rw [←integral_const_mul]
    congr 1;funext x;ring
  rw [hconvert,integral_integral_swap hswap]
  have htime : (fun t:ℝ=>∫x,integrand d α ε (t,x)*(mFourier k x).re) =ᵐ[volume.restrict (Ioi 0)]
      fun t=>t^(α-1)*Real.exp (-(r*(t+ε))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htp : 0<t+ε := add_pos_of_pos_of_nonneg ht hε
    have hi1 : Integrable (fun x=>HeatKernel d (t+ε) x*(mFourier k x).re) volume :=
      ((heat_continuous d (t+ε) htp).mul
        (Complex.continuous_re.comp (mFourier k).continuous)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hi2 : Integrable (fun x=>(mFourier k x).re) volume :=
      (Complex.continuous_re.comp (mFourier k).continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    dsimp only [integrand]
    simp_rw [mul_assoc,sub_mul,one_mul]
    rw [integral_const_mul,integral_sub hi1 hi2,(HeatFourierCoefficients d (t+ε) htp k).1,
      re_mean,if_neg hk,sub_zero]
    congr 2
    dsimp [r]
    ring
  rw [integral_congr_ae htime]
  have hsplit : (fun t:ℝ=>t^(α-1)*Real.exp (-(r*(t+ε))))=
      fun t=>Real.exp (-r*ε)*(t^(α-1)*Real.exp (-(r*t))) := by
    funext t
    rw [show -(r*(t+ε)) = -r*ε + -(r*t) by ring,Real.exp_add]
    ring
  rw [hsplit,integral_const_mul,Real.integral_rpow_mul_exp_neg_mul_Ioi hα hr]
  have hpower : (1/r)^α=r^(-α) := by
    rw [one_div,Real.inv_rpow,Real.rpow_neg] <;> exact hr.le
  rw [hpower]
  rw [show -((d:ℝ)-s)/2 = -α by dsimp [α];ring,
    show -4*Real.pi^2*ε*(∑j,(k j:ℝ)^2) = -r*ε by dsimp [r];ring]
  change (a/Real.Gamma α)*(Real.exp (-r*ε)*(r^(-α)*Real.Gamma α)) = a*r^(-α)*Real.exp (-r*ε)
  field_simp [hΓ]
  <;> ring

