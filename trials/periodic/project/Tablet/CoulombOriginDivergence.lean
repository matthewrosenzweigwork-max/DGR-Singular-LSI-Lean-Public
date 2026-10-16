import Tablet.RieszKernel
import Tablet.RieszGaussianImageRemainder
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open MeasureTheory Set Filter
open scoped Topology
-- [TABLET NODE: CoulombOriginDivergence]
theorem CoulombOriginDivergence (d:ℕ)(hd:2≤d) :
    Tendsto (fun ε:ℝ=>RieszKernel d ((d:ℝ)-2) 1 ε 0) (𝓝[>]0) atTop := by
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

  have kernel_time_measurable (d : ℕ) (x : UnitAddTorus (Fin d)) :
      Measurable (fun t : ℝ => HeatKernel d t x) := by
    unfold HeatKernel
    apply Measurable.tsum
    intro k
    fun_prop

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
  have heat_decay_half (d : ℕ) : ∃C:ℝ,0≤C ∧ ∀(t ε:ℝ),1/2≤t → 0≤ε →
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
    have htpos : 0≤t := by linarith
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
        have hπ : 3≤4*Real.pi^2 := by nlinarith [Real.pi_gt_three]
        have h1 := mul_le_mul_of_nonneg_left hq htpos
        have h2 := mul_le_mul_of_nonneg_right ht hqpos
        have heq := mul_nonneg hε hqpos
        have h3 := mul_le_mul_of_nonneg_right hπ (mul_nonneg (by linarith : 0≤t+ε) hqpos)
        nlinarith
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
      ∑' k:Fin d→ℤ,Real.exp (-4*Real.pi^2*t*∑j,(k j:ℝ)^2) := by
    have h0 : ((AddCircle.equivIco (1:ℝ) 0) 0 : ℝ) = 0 := by
      simpa using (AddCircle.equivIco_coe_of_mem (p:=(1:ℝ)) (a:=0) (y:=0) (by norm_num))
    simp [HeatKernel,h0]
  have heat_origin_ge_one (d:ℕ)(t:ℝ)(ht:0<t) : 1≤HeatKernel d t 0 := by
    rw [heat_origin_sum]
    have hs := gaussian_lattice_summable d (4*Real.pi^2*t) (by positivity)
    have hs' : Summable (fun k:Fin d→ℤ=>Real.exp (-4*Real.pi^2*t*∑j,(k j:ℝ)^2)) := by
      convert hs using 1 <;>ring_nf
    simpa using hs'.le_tsum 0 (fun _ _ => Real.exp_nonneg _)
  have heat_origin_uniform_above (d:ℕ)(ε:ℝ)(hε:0<ε) :
      ∃A:ℝ,0≤A ∧ ∀t:ℝ,ε≤t→|HeatKernel d t 0|≤A := by
    let A := ∑' k:Fin d→ℤ,Real.exp (-(4*Real.pi^2*ε)*∑j,(k j:ℝ)^2)
    have hs := gaussian_lattice_summable d (4*Real.pi^2*ε) (by positivity)
    refine ⟨A,tsum_nonneg (fun _=>Real.exp_nonneg _),?_⟩
    intro t ht
    rw [heat_origin_sum,abs_of_nonneg (tsum_nonneg fun _=>Real.exp_nonneg _)]
    have hb (k:Fin d→ℤ) : Real.exp (-4*Real.pi^2*t*∑j,(k j:ℝ)^2) ≤
        Real.exp (-(4*Real.pi^2*ε)*∑j,(k j:ℝ)^2) := by
      apply Real.exp_le_exp.mpr
      have hq : 0≤∑j,(k j:ℝ)^2 := Finset.sum_nonneg (fun _ _=>sq_nonneg _)
      have hm := mul_le_mul_of_nonneg_right ht hq
      nlinarith [mul_le_mul_of_nonneg_left hm (show 0≤4*Real.pi^2 by positivity)]
    exact (Summable.of_nonneg_of_le (fun _=>Real.exp_nonneg _) hb hs).tsum_le_tsum hb hs
  have heat_origin_integrable_shift (d:ℕ)(ε:ℝ)(hε:0<ε) :
      IntegrableOn (fun t:ℝ=>HeatKernel d (t+ε) 0-1) (Ioi 0) volume := by
    obtain ⟨A,hA,hAb⟩ := heat_origin_uniform_above d ε hε
    obtain ⟨L,hL,hLb⟩ := heat_decay_half d
    have hm : AEStronglyMeasurable (fun t:ℝ=>HeatKernel d (t+ε) 0-1) volume :=
      (((kernel_time_measurable d 0).comp (measurable_id.add_const ε)).sub_const 1).aestronglyMeasurable
    have hn : IntegrableOn (fun t:ℝ=>HeatKernel d (t+ε) 0-1) (Ioc 0 1) volume := by
      apply (integrableOn_const (s:=Ioc (0:ℝ) 1) (μ:=volume) (C:=A+1) (by simp)).mono' hm.restrict
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Real.norm_eq_abs]
      have hh := abs_sub (HeatKernel d (t+ε) 0) 1
      simp only [abs_one] at hh
      linarith [hAb (t+ε) (by linarith [ht.1])]
    have hl : IntegrableOn (fun t:ℝ=>HeatKernel d (t+ε) 0-1) (Ioi 1) volume := by
      have hg : IntegrableOn (fun t:ℝ=>Real.exp (-t)) (Ioi 0) volume := by
        simpa using Real.GammaIntegral_convergent (show 0<(1:ℝ) by norm_num)
      apply ((hg.mono_set (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤1))).const_mul L).mono' hm.restrict
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simpa only [Real.norm_eq_abs] using hLb t ε (by linarith [show (1:ℝ)<t from ht]) hε.le 0
    rw [←Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ)≤1),integrableOn_union]
    exact ⟨hn,hl⟩
  have heat_origin_gaussian_lower (d:ℕ)(t:ℝ)(ht:0<t) :
      (4*Real.pi*t)^(-(d:ℝ)/2) ≤ HeatKernel d t 0 := by
    have hs := gaussian_lattice_summable d (1/(4*t)) (by positivity)
    have hs' : Summable (fun n:Fin d→ℤ=>Real.exp (-(∑j,(n j:ℝ)^2)/(4*t))) := by
      convert hs using 1
      funext n
      congr 1
      ring
    have hb : 1≤∑'n:Fin d→ℤ,Real.exp (-(∑j,(n j:ℝ)^2)/(4*t)) := by
      simpa using hs'.le_tsum 0 (fun _ _=>Real.exp_nonneg _)
    have hK := (RieszGaussianImageRemainder d).1 t ht 0
    have hz : TorusLift d (0 : EuclideanSpace ℝ (Fin d)) = 0 := by funext j; rfl
    rw [hz] at hK
    simp only [PiLp.zero_apply,zero_add] at hK
    rw [hK]
    simpa using mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg (show 0≤4*Real.pi*t by positivity) (-(d:ℝ)/2))

  have origin_coulomb_lower (d:ℕ)(hd:2≤d)(r c ε:ℝ)(hr:0<r)
      (hc:0<c)(hrc:r≤c)(hcsmall:8*Real.pi*c≤1)(hε:0<ε)(hεr:ε≤r) :
      (1/(8*Real.pi))*Real.log (c/r)-(c-r) ≤ RieszKernel d ((d:ℝ)-2) 1 ε 0 := by
    have hpow : ((d:ℝ)-((d:ℝ)-2))/2 = 1 := by ring
    have hg := heat_origin_integrable_shift d ε hε
    have hn : ∀ᵐt:ℝ∂volume.restrict (Ioi 0),0≤HeatKernel d (t+ε) 0-1 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hh := heat_origin_ge_one d (t+ε) (by linarith [show 0<t from ht])
      linarith
    have hsub : Ioc r c ⊆ Ioi (0:ℝ) := fun t ht => lt_trans hr ht.1
    have hset := setIntegral_mono_set hg hn (Eventually.of_forall fun _ h=>hsub h)
    have hi : IntervalIntegrable (fun t:ℝ=>t⁻¹) volume r c := by
      apply intervalIntegral.intervalIntegrable_inv _ continuousOn_id
      intro t ht
      rw [uIcc_of_le hrc] at ht
      exact ne_of_gt (hr.trans_le ht.1)
    have hlowi : IntegrableOn (fun t:ℝ=>(1/(8*Real.pi))*t⁻¹-1) (Ioc r c) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hrc).mp
        ((hi.const_mul (1/(8*Real.pi))).sub (intervalIntegrable_const))
    have hpt : ∀t∈Ioc r c,(1/(8*Real.pi))*t⁻¹-1 ≤ HeatKernel d (t+ε) 0-1 := by
      intro t ht
      have ht0:0<t:=hr.trans ht.1
      have hτ:0<t+ε:=by linarith
      have hp:0<4*Real.pi*(t+ε):=by positivity
      have hp1:4*Real.pi*(t+ε)≤1 := by
        have he:ε≤t:=hεr.trans ht.1.le
        nlinarith [Real.pi_pos,mul_le_mul_of_nonneg_left ht.2 (show 0≤8*Real.pi by positivity)]
      have hpd : -(d:ℝ)/2 ≤ -1 := by
        have hdreal : (2:ℝ)≤(d:ℝ) := by exact_mod_cast hd
        linarith
      have hb := Real.rpow_le_rpow_of_exponent_ge hp hp1 hpd
      rw [Real.rpow_neg_one] at hb
      have hden : 4*Real.pi*(t+ε)≤8*Real.pi*t := by
        nlinarith [mul_le_mul_of_nonneg_left (hεr.trans ht.1.le) (show 0≤4*Real.pi by positivity)]
      have hinv := one_div_le_one_div_of_le hp hden
      have hgauss := heat_origin_gaussian_lower d (t+ε) hτ
      have heq : (1/(8*Real.pi))*t⁻¹=1/(8*Real.pi*t) := by field_simp
      rw [heq]
      simp only [one_div] at hinv ⊢
      exact sub_le_sub_right (hinv.trans (hb.trans hgauss)) 1
    have hlo := setIntegral_mono_on hlowi (hg.mono_set hsub) measurableSet_Ioc hpt
    have hv : (∫t in Ioc r c,(1/(8*Real.pi))*t⁻¹-1) =
        (1/(8*Real.pi))*Real.log (c/r)-(c-r) := by
      rw [←intervalIntegral.integral_of_le hrc,intervalIntegral.integral_sub
        (hi.const_mul _) intervalIntegrable_const,intervalIntegral.integral_const_mul,
        integral_inv_of_pos hr hc,intervalIntegral.integral_const]
      simp
    have hkernel : RieszKernel d ((d:ℝ)-2) 1 ε 0 = ∫t in Ioi (0:ℝ),HeatKernel d (t+ε) 0-1 := by
      simp [RieszKernel,ne_of_gt hε,hpow]
    rw [←hv,hkernel]
    exact hlo.trans hset

  have coulomb_origin_unbounded (d:ℕ)(hd:2≤d)(T:ℝ) :
      ∃r:ℝ,0<r ∧ ∀ε:ℝ,0<ε→ε≤r→T<RieszKernel d ((d:ℝ)-2) 1 ε 0 := by
    let c : ℝ := 1/(16*Real.pi)
    have hc : 0<c := by dsimp[c];positivity
    have hcs : 8*Real.pi*c≤1 := by dsimp[c];field_simp;nlinarith [Real.pi_pos]
    let M := max T 0+c+1
    have hM : 0<M := by dsimp[M];linarith [le_max_right T 0]
    let r := c*Real.exp (-(8*Real.pi*M))
    have hr : 0<r := by dsimp[r];positivity
    have hrc : r≤c := by
      apply mul_le_of_le_one_right hc.le
      apply Real.exp_le_one_iff.mpr
      exact neg_nonpos.mpr (by positivity)
    have hlog : Real.log (c/r)=8*Real.pi*M := by
      rw [Real.log_div (ne_of_gt hc) (ne_of_gt hr)]
      dsimp[r]
      rw [Real.log_mul (ne_of_gt hc) (ne_of_gt (Real.exp_pos _)),Real.log_exp]
      ring
    refine ⟨r,hr,?_⟩
    intro ε hε hεr
    have hlo := origin_coulomb_lower d hd r c ε hr hc hrc hcs hε hεr
    rw [hlog] at hlo
    have heq : 1/(8*Real.pi)*(8*Real.pi*M)=M := by field_simp
    rw [heq] at hlo
    have hmax : T≤max T 0 := le_max_left _ _
    dsimp[M] at hlo
    linarith

  apply tendsto_atTop.2
  intro T
  obtain ⟨r,hr,hbound⟩ := coulomb_origin_unbounded d hd T
  have he : ∀ᶠ ε:ℝ in 𝓝[>]0, ε<r :=
    (eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,he] with ε hε hεr
  exact (hbound ε hε hεr.le).le
