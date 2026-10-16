import Tablet.RieszKernel
import Tablet.RieszGaussianImageRemainder
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds
open MeasureTheory Filter Set
open scoped Topology
-- [TABLET NODE: RieszCutoffContinuity]
theorem RieszCutoffContinuity (d : ℕ) (s a : ℝ) (hsd : s < (d:ℝ))
    (x : UnitAddTorus (Fin d)) (hx : x ≠ 0) :
    Tendsto (fun ε : ℝ => RieszKernel d s a ε x) (𝓝[>] 0)
      (𝓝 (RieszKernel d s a 0 x)) := by
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

  let latticePoint {d:ℕ} (n:Fin d→ℤ) : EuclideanSpace ℝ (Fin d) :=
    WithLp.toLp 2 (fun j=>(n j:ℝ))
  have lift_lattice {d:ℕ} (n:Fin d→ℤ) : TorusLift d (latticePoint n)=0 := by
    funext j
    change ((n j:ℝ):AddCircle (1:ℝ))=0
    exact (AddCircle.coe_eq_zero_iff (p:=(1:ℝ))).mpr ⟨n j,by simp⟩
  have lift_neg_lattice {d:ℕ} (n:Fin d→ℤ) : TorusLift d (-latticePoint n)=0 := by
    funext j
    have hj:=congrFun (lift_lattice n) j
    change ((n j:ℝ):AddCircle (1:ℝ))=0 at hj
    change ((-(n j:ℝ)):AddCircle (1:ℝ))=0
    simpa only [AddCircle.coe_neg,neg_zero] using congrArg Neg.neg hj
  have lift_continuous (d:ℕ) : Continuous (TorusLift d) := by
    apply continuous_pi
    intro j
    dsimp [TorusLift]
    fun_prop
  have distance_to_lattice (d:ℕ) (y:EuclideanSpace ℝ (Fin d))
      (hy:TorusLift d y≠0) :
      ∃δ:ℝ,0<δ ∧ ∀n:Fin d→ℤ,δ≤‖y+latticePoint n‖ := by
    have hU : IsOpen {z:EuclideanSpace ℝ (Fin d)|TorusLift d z≠0} :=
      isOpen_compl_singleton.preimage (lift_continuous d)
    obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hU y hy
    refine ⟨δ,hδ,?_⟩
    intro n
    have hn : ¬(-latticePoint n:EuclideanSpace ℝ (Fin d))∈Metric.ball y δ := by
      intro h
      have hbad:=hball h
      exact hbad (lift_neg_lattice n)
    have hdist : δ≤dist (-latticePoint n) y := le_of_not_gt hn
    simpa only [dist_eq_norm',sub_neg_eq_add] using hdist

  have lattice_norm_sq {d:ℕ} (n:Fin d→ℤ) : ‖latticePoint n‖^2=∑j,(n j:ℝ)^2 := by
   rw [EuclideanSpace.real_norm_sq_eq]

  have gaussian_local_split {d:ℕ} (y:EuclideanSpace ℝ (Fin d)) (n:Fin d→ℤ)
   (R δ t:ℝ) (hR:0≤R) (hδ:0<δ) (hy:‖y‖≤R)
   (hsep:δ≤‖y+latticePoint n‖) (ht:0<t) (ht1:t≤1) :
   Real.exp (-‖y+latticePoint n‖^2/(4*t)) ≤
   Real.exp (-δ^2/(8*t))*
   Real.exp (-(δ^2/(16*(δ^2+R^2+1)))*(∑j,(n j:ℝ)^2)) := by
   let r:=‖y+latticePoint n‖
   let q:=‖latticePoint n‖^2
   let S:=δ^2+R^2+1
   have hr : 0≤r := norm_nonneg _
   have hq : 0≤q := sq_nonneg _
   have hS : 0<S := by dsimp [S];positivity
   have hδ2 : δ^2≤r^2 := pow_le_pow_left₀ hδ.le hsep 2
   have hh : ‖latticePoint n‖≤r+R := by
     have hh := norm_sub_le (y+latticePoint n) y
     simp only [add_sub_cancel_left] at hh
     dsimp [r];linarith
   have hh2 := pow_le_pow_left₀ (norm_nonneg (latticePoint n)) hh 2
   have hqr : q≤2*r^2+2*R^2 := by
     dsimp [q];nlinarith [sq_nonneg (r-R)]
   have hqδ : q*δ^2≤2*S*r^2 := by
     have h1:=mul_le_mul_of_nonneg_right hqr (sq_nonneg δ)
     have h2:=mul_le_mul_of_nonneg_left hδ2 (show 0≤2*R^2 by positivity)
     dsimp [S];nlinarith [sq_nonneg r]
   have hgq : δ^2/(16*S)*q≤r^2/8 := by
     rw [div_mul_eq_mul_div]
     apply (div_le_iff₀ (show 0<16*S by positivity)).mpr
     calc
      δ^2*q ≤ 2*S*r^2 := by nlinarith only [hqδ]
      _ = r^2/8*(16*S) := by ring
   have hgt : r^2/8≤r^2/(8*t) := by
     apply (le_div_iff₀ (show 0<8*t by positivity)).mpr
     nlinarith [mul_le_of_le_one_right (sq_nonneg r) ht1]
   have hds : δ^2/(8*t)≤r^2/(8*t) := div_le_div_of_nonneg_right hδ2 (by positivity)
   rw [← Real.exp_add]
   apply Real.exp_le_exp.mpr
   rw [← lattice_norm_sq n]
   change -r^2/(4*t)≤ -δ^2/(8*t)+ -(δ^2/(16*S))*q
   have hsum : δ^2/(8*t)+δ^2/(16*S)*q≤r^2/(4*t) := by
     calc
      _ ≤ r^2/(8*t)+r^2/(8*t) := add_le_add hds (hgq.trans hgt)
      _ = _ := by ring
   simpa only [neg_add,neg_div,neg_mul] using neg_le_neg hsum

  have inverse_gaussian_uniform_bound (β c : ℝ) (hc : 0 < c) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → t^β*Real.exp (-c/t) ≤ C := by
    classical
    let f := fun t : ℝ => t^β*Real.exp (-c/t)
    have hlim : Tendsto f (𝓝[>] 0) (𝓝 0) := by
      have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-β) c hc).comp
        (tendsto_inv_nhdsGT_zero)
      apply h.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      change 0 < t at ht
      dsimp [f]
      rw [Real.inv_rpow ht.le,← Real.rpow_neg ht.le]
      congr 2
      ring
    have hc : ContinuousOn (Function.update f 0 0) (Icc 0 1) := by
      rw [continuousOn_update_iff]
      refine ⟨?_,fun _ => hlim.mono_left (nhdsWithin_mono _ ?_)⟩
      · intro t ht
        have ht0 : t ≠ 0 := by simpa using ht.2
        have htpos : 0 < t := lt_of_le_of_ne ht.1.1 (Ne.symm ht0)
        exact ((Real.continuousAt_rpow_const t β (Or.inl ht0)).mul
          (Real.continuous_exp.continuousAt.comp
            (continuousAt_const.div continuousAt_id ht0))).continuousWithinAt
      · intro t ht
        have ht0 : t ≠ 0 := by simpa using ht.2
        exact lt_of_le_of_ne ht.1.1 (Ne.symm ht0)
    obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
    refine ⟨max C 0,le_max_right _ _,?_⟩
    intro t ht ht1
    have h := hC t ⟨ht.le,ht1⟩
    rw [Function.update_of_ne (ne_of_gt ht)] at h
    change ‖t^β*Real.exp (-c/t)‖ ≤ C at h
    exact (le_abs_self _).trans ((by simpa only [Real.norm_eq_abs] using h :
      |t^β*Real.exp (-c/t)| ≤ C).trans (le_max_left _ _))

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

  have heat_point_uniform_bound (d : ℕ) (x : UnitAddTorus (Fin d)) (hx : x ≠ 0) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → |HeatKernel d t x| ≤ C := by
    classical
    let y : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2
      (fun j => (AddCircle.equivIco (1:ℝ) 0 (x j) : ℝ))
    have hxy : TorusLift d y = x := by
      funext j
      exact AddCircle.coe_equivIco
    have hy0 : TorusLift d y ≠ 0 := by rwa [hxy]
    obtain ⟨δ,hδ,hsep⟩ := distance_to_lattice d y hy0
    let R := ‖y‖
    let c := δ^2/(16*(δ^2+R^2+1))
    have hc : 0 < c := by dsimp [c];positivity
    have hs := gaussian_lattice_summable d c hc
    let A := ∑' n : Fin d → ℤ, Real.exp (-c*∑ j,(n j:ℝ)^2)
    have hA : 0 ≤ A := tsum_nonneg fun _ => Real.exp_nonneg _
    obtain ⟨D,hD,hDb⟩ := inverse_gaussian_uniform_bound (-(d:ℝ)/2) (δ^2/8) (by positivity)
    let S := (4*Real.pi)^(-(d:ℝ)/2)*D*A
    have hS : 0 ≤ S := by dsimp [S];positivity
    obtain ⟨L,hL,hLb⟩ := heat_decay_half d
    refine ⟨S+L+1,by positivity,?_⟩
    intro t ht
    by_cases ht1 : t ≤ 1
    · have hsplit (n : Fin d → ℤ) :
          Real.exp (-(∑ j,(y j+(n j:ℝ))^2)/(4*t)) ≤
          Real.exp (-δ^2/(8*t))*Real.exp (-c*∑ j,(n j:ℝ)^2) := by
        have hh := gaussian_local_split y n R δ t (norm_nonneg y) hδ (le_refl _) (hsep n) ht ht1
        have he : ‖y+latticePoint n‖^2 = ∑ j,(y j+(n j:ℝ))^2 := by
          rw [EuclideanSpace.real_norm_sq_eq]
          rfl
        simpa only [he] using hh
      have hm := hs.mul_left (Real.exp (-δ^2/(8*t)))
      have hi := Summable.of_nonneg_of_le (fun n => Real.exp_nonneg _) hsplit hm
      have hts : (∑'n : Fin d → ℤ,Real.exp (-(∑j,(y j+(n j:ℝ))^2)/(4*t))) ≤
          Real.exp (-δ^2/(8*t))*A := by
        simpa only [A,tsum_mul_left] using hi.tsum_le_tsum hsplit hm
      have hK := (RieszGaussianImageRemainder d).1 t ht y
      rw [hxy] at hK
      rw [hK,abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _) (tsum_nonneg fun _ => Real.exp_nonneg _))]
      have hb := mul_le_mul_of_nonneg_left hts (Real.rpow_nonneg (show 0≤4*Real.pi*t by positivity) (-(d:ℝ)/2))
      apply hb.trans
      have he : (4*Real.pi*t)^(-(d:ℝ)/2)*(Real.exp (-δ^2/(8*t))*A) =
        (4*Real.pi)^(-(d:ℝ)/2)*(t^(-(d:ℝ)/2)*Real.exp (-(δ^2/8)/t))*A := by
        rw [Real.mul_rpow (show 0≤4*Real.pi by positivity) ht.le]
        rw [show -δ^2/(8*t) = -(δ^2/8)/t by ring]
        ring
      rw [he]
      have hd := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hDb t ht ht1)
          (Real.rpow_nonneg (show 0 ≤ 4*Real.pi by positivity) (-(d:ℝ)/2))) hA
      exact hd.trans (by change S ≤ S+L+1;linarith)
    · have hd := hLb t 0 (by linarith) (le_refl 0) x
      simp only [add_zero] at hd
      have he : |HeatKernel d t x| ≤ |HeatKernel d t x-1|+1 := by
        simpa only [sub_add_cancel,abs_one] using abs_add_le (HeatKernel d t x-1) 1
      have hex : Real.exp (-t) ≤ 1 := by simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr ht.le)
      have hl := mul_le_of_le_one_right hL hex
      linarith

  have kernel_time_measurable (d : ℕ) (x : UnitAddTorus (Fin d)) :
      Measurable (fun t : ℝ => HeatKernel d t x) := by
    unfold HeatKernel
    apply Measurable.tsum
    intro k
    fun_prop
  have kernel_time_continuousAt (d : ℕ) (x : UnitAddTorus (Fin d))
      (t : ℝ) (ht : 0 < t) : ContinuousAt (fun v : ℝ => HeatKernel d v x) t := by
    have hs : Summable (fun k : Fin d → ℤ =>
        Real.exp (-(4*Real.pi^2*(t/2))*∑ j,(k j:ℝ)^2)) :=
      gaussian_lattice_summable d (4*Real.pi^2*(t/2)) (by positivity)
    have hc : ContinuousOn (fun v : ℝ => HeatKernel d v x) (Ioi (t/2)) := by
      unfold HeatKernel
      apply continuousOn_tsum (fun k => by fun_prop) hs
      intro k v hv
      rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
      apply (mul_le_of_le_one_right (Real.exp_nonneg _) (Real.abs_cos_le_one _)).trans
      apply Real.exp_le_exp.mpr
      have hq : 0 ≤ ∑ j,(k j:ℝ)^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hh := mul_le_mul_of_nonneg_right (le_of_lt hv) hq
      have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ 4*Real.pi^2 by positivity)
      nlinarith only [hh']
    exact hc.continuousAt (isOpen_Ioi.mem_nhds (half_lt_self ht))

  let α : ℝ := ((d:ℝ)-s)/2
  have hα : 0 < α := by dsimp [α];linarith
  obtain ⟨C,hC,hCb⟩ := heat_point_uniform_bound d x hx
  obtain ⟨L,hL,hLb⟩ := heat_decay_half d
  let b : ℝ → ℝ := fun t => if t ≤ 1 then
    (C+1)*t^(α-1) else L*(t^(α-1)*Real.exp (-t))
  have hbi : IntegrableOn b (Ioi 0) volume := by
    have hn : IntegrableOn (fun t:ℝ => (C+1)*t^(α-1)) (Ioc 0 1) volume :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1:ℝ)<α-1))).const_mul (C+1)
    have hl : IntegrableOn (fun t:ℝ => L*(t^(α-1)*Real.exp (-t))) (Ioi 1) volume := by
      have hg : IntegrableOn (fun t:ℝ=>t^(α-1)*Real.exp (-t)) (Ioi 0) volume := by
        simpa only [mul_comm] using Real.GammaIntegral_convergent hα
      exact (hg.mono_set (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤1))).const_mul L
    rw [←Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ)≤1),integrableOn_union]
    constructor
    · exact hn.congr_fun (fun t ht => by simp only [b,if_pos ht.2]) measurableSet_Ioc
    · exact hl.congr_fun (fun t ht => by simp only [b,if_neg (not_le.mpr (show (1:ℝ)<t from ht))]) measurableSet_Ioi
  have hm : ∀ ε : ℝ, AEStronglyMeasurable
      (fun t : ℝ => t^(α-1)*(HeatKernel d (t+ε) x-1))
      (volume.restrict (Ioi 0)) := by
    intro ε
    exact ((measurable_id.pow_const (α-1)).mul
      (((kernel_time_measurable d x).comp (measurable_id.add_const ε)).sub_const 1)).aestronglyMeasurable
  have hb : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ᵐ t ∂volume.restrict (Ioi 0),
      ‖t^(α-1)*(HeatKernel d (t+ε) x-1)‖ ≤ b t := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hε0 : 0 < ε := hε
    have hτ : 0 < t+ε := by linarith
    have hp : 0 ≤ t^(α-1) := Real.rpow_nonneg ht0.le _
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hp]
    by_cases ht1 : t ≤ 1
    · have hd : |HeatKernel d (t+ε) x-1| ≤ C+1 := by
        have htri := abs_sub (HeatKernel d (t+ε) x) (1:ℝ)
        simp only [abs_one] at htri
        linarith [hCb (t+ε) hτ]
      exact (mul_le_mul_of_nonneg_left hd hp).trans_eq (by simp only [b,if_pos ht1];ring)
    · have hd := hLb t ε (by linarith) hε0.le x
      exact (mul_le_mul_of_nonneg_left hd hp).trans_eq (by simp only [b,if_neg ht1];ring)
  have hlim : ∀ᵐ t ∂volume.restrict (Ioi 0),
      Tendsto (fun ε : ℝ => t^(α-1)*(HeatKernel d (t+ε) x-1)) (𝓝[>] 0)
        (𝓝 (t^(α-1)*(HeatKernel d t x-1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hτ : Tendsto (fun ε : ℝ => t+ε) (𝓝[>] 0) (𝓝 t) := by
      have he : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have hc : Tendsto (fun _ : ℝ => t) (𝓝[>] 0) (𝓝 t) := tendsto_const_nhds
      simpa only [add_zero] using hc.add he
    exact (((kernel_time_continuousAt d x t ht).tendsto.comp hτ).sub_const 1).const_mul (t^(α-1))
  have hi := tendsto_integral_filter_of_dominated_convergence b
    (Eventually.of_forall hm) hb hbi hlim
  have hc := hi.const_mul (a/Real.Gamma α)
  simpa [RieszKernel,hx,α] using hc
