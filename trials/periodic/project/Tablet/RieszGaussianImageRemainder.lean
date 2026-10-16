module

public import Tablet.HeatKernelFacts
public import Tablet.TorusLift
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section
open MeasureTheory Set Filter
open scoped Topology
-- [TABLET NODE: RieszGaussianImageRemainder]
theorem RieszGaussianImageRemainder (d : ℕ) :
    (∀ (t : ℝ), 0 < t → ∀ y : EuclideanSpace ℝ (Fin d),
      HeatKernel d t (TorusLift d y) = (4 * Real.pi * t)^(-(d : ℝ) / 2) *
        ∑' n : Fin d → ℤ, Real.exp (-(∑ j, (y j + (n j : ℝ))^2) / (4 * t))) ∧
    (∃ K : ℝ, 0 ≤ K ∧ ∀ (t : ℝ), 0 < t → t ≤ 1 →
      ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 1 / 4 →
      0 ≤ (∑' n : Fin d → ℤ, if n = 0 then (0 : ℝ) else
        Real.exp (-(∑ j, (y j + (n j : ℝ))^2) / (4 * t))) ∧
      (∑' n : Fin d → ℤ, if n = 0 then (0 : ℝ) else
        Real.exp (-(∑ j, (y j + (n j : ℝ))^2) / (4 * t))) ≤
          K * Real.exp (-1 / (16 * t))) ∧
    (∀ (α : ℝ), 0 < α → ∃ C : ℝ, 0 ≤ C ∧
      ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 1 / 4 →
      IntegrableOn (fun t : ℝ =>
        t^(α - 1) * (HeatKernel d t (TorusLift d y) - 1) -
          t^(α - 1) * (4 * Real.pi * t)^(-(d : ℝ) / 2) *
            Real.exp (-‖y‖^2 / (4 * t))) (Ioc 0 1) volume ∧
      |∫ t in Ioc 0 1,
        t^(α - 1) * (HeatKernel d t (TorusLift d y) - 1) -
          t^(α - 1) * (4 * Real.pi * t)^(-(d : ℝ) / 2) *
            Real.exp (-‖y‖^2 / (4 * t))| ≤ C) := by
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

  have inverse_gaussian_integrable (β c : ℝ) (hc : 0 < c) :
      IntegrableOn (fun t : ℝ => t^β*Real.exp (-c/t)) (Ioc 0 1) volume := by
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
    have hi : IntegrableOn (Function.update f 0 0) (Icc 0 1) volume := hc.integrableOn_Icc
    have hi' := hi.mono_set Ioc_subset_Icc_self
    apply hi'.congr_fun _ measurableSet_Ioc
    intro t ht
    rw [Function.update_of_ne (ne_of_gt ht.1)]
  have lattice_sq_one {d : ℕ} (n : Fin d→ℤ) (hn : n≠0) :
      (1:ℝ)≤∑j,(n j:ℝ)^2 := by
    have hex : ∃j,n j≠0 := by
      by_contra h
      push_neg at h
      apply hn
      funext j
      exact h j
    obtain ⟨j,hj⟩ := hex
    have hj2 : (1:ℝ)≤(n j:ℝ)^2 := by
      have hh : (1:ℤ)≤n j ∨ n j≤-1 := by omega
      have hsq : (1:ℤ)≤(n j)^2 := by rcases hh with hh | hh <;> nlinarith
      exact_mod_cast hsq
    exact hj2.trans (Finset.single_le_sum (fun k _=>sq_nonneg (n k:ℝ)) (Finset.mem_univ j))

  have shifted_lattice_sq {d : ℕ} (n : Fin d→ℤ) (hn : n≠0)
      (y : EuclideanSpace ℝ (Fin d)) (hy : ‖y‖≤1/4) :
      (∑j,(n j:ℝ)^2)/2 ≤ ∑j,(y j+(n j:ℝ))^2 := by
    let v : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (fun j=>(n j:ℝ))
    have hv2 : ‖v‖^2=∑j,(n j:ℝ)^2 := by rw [EuclideanSpace.real_norm_sq_eq]
    have hyv2 : ‖y+v‖^2=∑j,(y j+(n j:ℝ))^2 := by rw [EuclideanSpace.real_norm_sq_eq];rfl
    have hv : 1≤‖v‖ := by nlinarith [lattice_sq_one n hn,norm_nonneg v]
    have hh : ‖v‖≤‖y+v‖+‖y‖ := by simpa only [add_sub_cancel_left] using norm_sub_le (y+v) y
    have hl : (3/4:ℝ)*‖v‖≤‖y+v‖ := by linarith
    have hs := pow_le_pow_left₀ (show 0≤(3/4:ℝ)*‖v‖ by positivity) hl 2
    rw [hyv2] at hs
    nlinarith [hv2,sq_nonneg ‖v‖]

  have gaussian_image_bound {d : ℕ} (n : Fin d→ℤ) (hn : n≠0)
      (y : EuclideanSpace ℝ (Fin d)) (hy : ‖y‖≤1/4)
      (t : ℝ) (ht : 0<t) (ht1 : t≤1) :
      Real.exp (-(∑j,(y j+(n j:ℝ))^2)/(4*t)) ≤
        Real.exp (-1/(16*t))*Real.exp (-(∑j,(n j:ℝ)^2)/16) := by
    let q : ℝ := ∑j,(n j:ℝ)^2
    let Q : ℝ := ∑j,(y j+(n j:ℝ))^2
    have hq : 1≤q := lattice_sq_one n hn
    have hq0 : 0≤q := by linarith
    have hQ : q/2≤Q := shifted_lattice_sq n hn y hy
    have hsmall : q*t≤q := mul_le_of_le_one_right hq0 ht1
    have hnum : 1+q*t≤2*q := by linarith
    have hsplit : 1/(16*t)+q/16≤q/(8*t) := by
      have h := div_le_div_of_nonneg_right hnum (show 0≤16*t by positivity)
      convert h using 1 <;> first | rfl | (field_simp [ne_of_gt ht] <;> ring)
    have hmain : q/(8*t)≤Q/(4*t) := by
      have h := div_le_div_of_nonneg_right hQ (show 0≤4*t by positivity)
      convert h using 1 <;> first | rfl | (field_simp [ne_of_gt ht] <;> ring)
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    simpa only [q,Q,neg_add,neg_div] using neg_le_neg (hsplit.trans hmain)

  have nonzero_image_uniform_majorant (d : ℕ) :
      ∃K:ℝ,0≤K ∧ ∀t:ℝ,0<t→t≤1→∀y:EuclideanSpace ℝ (Fin d),‖y‖≤1/4→
        0≤(∑'n:Fin d→ℤ,if n=0 then (0:ℝ) else Real.exp (-(∑j,(y j+(n j:ℝ))^2)/(4*t))) ∧
        (∑'n:Fin d→ℤ,if n=0 then (0:ℝ) else Real.exp (-(∑j,(y j+(n j:ℝ))^2)/(4*t))) ≤
          K*Real.exp (-1/(16*t)) := by
    classical
    let b := fun n:Fin d→ℤ=>Real.exp (-(∑j,(n j:ℝ)^2)/16)
    let K := ∑'n,b n
    have hs : Summable b := by
      convert gaussian_lattice_summable d (1/16) (by norm_num) using 1
      funext n
      dsimp only [b]
      ring_nf
    refine ⟨K,tsum_nonneg (fun _=>Real.exp_nonneg _),?_⟩
    intro t ht ht1 y hy
    let F := fun n:Fin d→ℤ=>if n=0 then (0:ℝ) else Real.exp (-(∑j,(y j+(n j:ℝ))^2)/(4*t))
    have hpos n : 0≤F n := by dsimp [F];split_ifs <;> positivity
    have hb n : F n≤Real.exp (-1/(16*t))*b n := by
      by_cases hn:n=0
      · simp only [F,hn,↓reduceIte]
        positivity
      · simpa only [F,b,if_neg hn] using gaussian_image_bound n hn y hy t ht ht1
    have hsum := Summable.of_nonneg_of_le hpos hb (hs.mul_left (Real.exp (-1/(16*t))))
    refine ⟨tsum_nonneg hpos,?_⟩
    calc
      (∑'n,F n) ≤ ∑'n,Real.exp (-1/(16*t))*b n := Summable.tsum_le_tsum hb hsum (hs.mul_left _)
      _ = K*Real.exp (-1/(16*t)) := by rw [tsum_mul_left];exact mul_comm _ _

  have heat_gaussian_lift (d : ℕ) (t : ℝ) (ht : 0<t) (y : EuclideanSpace ℝ (Fin d)) :
      HeatKernel d t (TorusLift d y)=(4*Real.pi*t)^(-(d:ℝ)/2)*
        ∑'n:Fin d→ℤ,Real.exp (-(∑j,(y j+(n j:ℝ))^2)/(4*t)) := by
    classical
    let r := fun j=>(AddCircle.equivIco (1:ℝ) 0 (TorusLift d y j):ℝ)
    have hex (j:Fin d) : ∃m:ℤ,(m:ℝ)=r j-y j := by
      have hh : (((r j-y j):ℝ):AddCircle (1:ℝ))=0 := by
        rw [AddCircle.coe_sub]
        have he : (r j:AddCircle (1:ℝ))=(y j:AddCircle (1:ℝ)) := by
          exact AddCircle.coe_equivIco
        rw [he,sub_self]
      obtain ⟨m,hm⟩ := (AddCircle.coe_eq_zero_iff (1:ℝ)).mp hh
      exact ⟨m,by simpa only [zsmul_eq_mul,mul_one] using hm⟩
    choose m hm using hex
    rw [(HeatKernelFacts d t ht).2.2.2.2.1 (TorusLift d y)]
    congr 1
    have he := (Equiv.addLeft m).tsum_eq (fun n:Fin d→ℤ=>Real.exp (-(∑j,(y j+(n j:ℝ))^2)/(4*t)))
    rw [←he]
    apply tsum_congr
    intro n
    congr 3
    apply Finset.sum_congr rfl
    intro j _
    change (r j+(n j:ℝ))^2=(y j+(((m+n) j:ℤ):ℝ))^2
    simp only [Pi.add_apply,Int.cast_add]
    have hj := hm j
    change (r j+(n j:ℝ))^2=(y j+((m j:ℝ)+(n j:ℝ)))^2
    congr 1
    linarith

  have gaussian_lift_split (d : ℕ) (t : ℝ) (ht : 0<t) (ht1 : t≤1)
      (y : EuclideanSpace ℝ (Fin d)) (hy : ‖y‖≤1/4) :
      HeatKernel d t (TorusLift d y)=(4*Real.pi*t)^(-(d:ℝ)/2)*
        (Real.exp (-‖y‖^2/(4*t)) +
          ∑'n:Fin d→ℤ,if n=0 then 0 else Real.exp (-(∑j,(y j+(n j:ℝ))^2)/(4*t))) := by
    classical
    let g := fun n:Fin d→ℤ=>Real.exp (-(∑j,(y j+(n j:ℝ))^2)/(4*t))
    let F := fun n:Fin d→ℤ=>if n=0 then (0:ℝ) else g n
    let b := fun n:Fin d→ℤ=>Real.exp (-(∑j,(n j:ℝ)^2)/16)
    have hs : Summable b := by
      convert gaussian_lattice_summable d (1/16) (by norm_num) using 1
      funext n
      dsimp only [b]
      ring_nf
    have hpos n : 0≤F n := by dsimp [F,g];split_ifs <;> positivity
    have hb n : F n≤Real.exp (-1/(16*t))*b n := by
      by_cases hn:n=0
      · simp only [F,hn,↓reduceIte]
        positivity
      · simpa only [F,g,b,if_neg hn] using gaussian_image_bound n hn y hy t ht ht1
    have hF := Summable.of_nonneg_of_le hpos hb (hs.mul_left (Real.exp (-1/(16*t))))
    have h0 := (hasSum_ite_eq (0:Fin d→ℤ) (g 0)).summable
    have hg : Summable g := by
      convert h0.add hF using 1
      funext n
      dsimp [F]
      by_cases hn:n=0 <;> simp [hn]
    rw [heat_gaussian_lift d t ht y]
    congr 1
    rw [hg.tsum_eq_add_tsum_ite 0]
    congr 1
    dsimp [g]
    simp only [Pi.zero_apply,Int.cast_zero,add_zero]
    rw [EuclideanSpace.real_norm_sq_eq]

  let imageRemainder (d : ℕ) (α : ℝ) (y : EuclideanSpace ℝ (Fin d)) (t : ℝ) : ℝ :=
    t^(α-1)*(HeatKernel d t (TorusLift d y)-1) -
      t^(α-1)*(4*Real.pi*t)^(-(d:ℝ)/2)*Real.exp (-‖y‖^2/(4*t))

  have image_remainder_measurable (d : ℕ) (α : ℝ) (y : EuclideanSpace ℝ (Fin d)) :
      Measurable (imageRemainder d α y) := by
    have hh : Measurable (fun p : ℝ × UnitAddTorus (Fin d) => HeatKernel d p.1 p.2) := by
      unfold HeatKernel
      simp_rw [cos_eq_character_re]
      apply Measurable.tsum
      intro k
      exact ((measurable_const.mul measurable_fst).mul measurable_const).exp.mul
        ((Complex.continuous_re.comp (UnitAddTorus.mFourier k).continuous).measurable.comp measurable_snd)
    exact (measurable_id.pow_const _).mul
        ((hh.comp (measurable_id.prodMk measurable_const)).sub measurable_const) |>.sub
        (((measurable_id.pow_const _).mul
          ((measurable_const.mul measurable_id).pow_const _)).mul
          ((measurable_const.div (measurable_const.mul measurable_id)).exp))

  have image_remainder_bound (d : ℕ) (α K : ℝ) (hK : 0≤K)
      (hmajor : ∀t:ℝ,0<t→t≤1→∀y:EuclideanSpace ℝ (Fin d),‖y‖≤1/4→
        0≤(∑'n:Fin d→ℤ,if n=0 then (0:ℝ) else Real.exp (-(∑j,(y j+(n j:ℝ))^2)/(4*t))) ∧
        (∑'n:Fin d→ℤ,if n=0 then (0:ℝ) else Real.exp (-(∑j,(y j+(n j:ℝ))^2)/(4*t))) ≤ K*Real.exp (-1/(16*t)))
      (t : ℝ) (ht : 0<t) (ht1 : t≤1) (y : EuclideanSpace ℝ (Fin d)) (hy : ‖y‖≤1/4) :
      |imageRemainder d α y t|≤
        ((4*Real.pi)^(-(d:ℝ)/2)*K)*(t^(α-1-(d:ℝ)/2)*Real.exp (-(1/16)/t)) + t^(α-1) := by
    let F := ∑'n:Fin d→ℤ,if n=0 then (0:ℝ) else Real.exp (-(∑j,(y j+(n j:ℝ))^2)/(4*t))
    have hF0 : 0≤F := (hmajor t ht ht1 y hy).1
    have hFb : F≤K*Real.exp (-1/(16*t)) := (hmajor t ht ht1 y hy).2
    have heq : imageRemainder d α y t=t^(α-1)*(4*Real.pi*t)^(-(d:ℝ)/2)*F-t^(α-1) := by
      unfold imageRemainder
      rw [gaussian_lift_split d t ht ht1 y hy]
      dsimp only [F]
      ring
    have hr : 0≤t^(α-1) := Real.rpow_nonneg ht.le _
    have hp : 0≤(4*Real.pi*t)^(-(d:ℝ)/2) := Real.rpow_nonneg (by positivity) _
    rw [heq]
    calc
      _ ≤ |t^(α-1)*(4*Real.pi*t)^(-(d:ℝ)/2)*F|+|t^(α-1)| := abs_sub _ _
      _ = t^(α-1)*(4*Real.pi*t)^(-(d:ℝ)/2)*F+t^(α-1) := by
        rw [abs_of_nonneg (mul_nonneg (mul_nonneg hr hp) hF0),abs_of_nonneg hr]
      _ ≤ t^(α-1)*(4*Real.pi*t)^(-(d:ℝ)/2)*(K*Real.exp (-1/(16*t)))+t^(α-1) :=
        add_le_add (mul_le_mul_of_nonneg_left hFb (mul_nonneg hr hp)) le_rfl
      _ = _ := by
        rw [Real.mul_rpow (show 0≤4*Real.pi by positivity) ht.le]
        have he : t^(α-1)*t^(-(d:ℝ)/2)=t^(α-1-(d:ℝ)/2) := by
          rw [←Real.rpow_add ht]
          congr 1
          ring
        calc
          _ = ((4*Real.pi)^(-(d:ℝ)/2)*K)*((t^(α-1)*t^(-(d:ℝ)/2))*Real.exp (-(1/16)/t))+t^(α-1) := by
            congr 1
            have he' : (-1:ℝ)/(16*t)=-(1/16)/t := by ring
            rw [he']
            ring
          _ = _ := by rw [he]

  have bounded_image_remainder (d : ℕ) (α : ℝ) (hα : 0<α) :
      ∃C:ℝ,0≤C ∧ ∀y:EuclideanSpace ℝ (Fin d),‖y‖≤1/4→
        IntegrableOn (imageRemainder d α y) (Set.Ioc 0 1) volume ∧
        |∫t in Set.Ioc 0 1,imageRemainder d α y t|≤C := by
    obtain ⟨K,hK,hmajor⟩ := nonzero_image_uniform_majorant d
    let B := fun t:ℝ=>((4*Real.pi)^(-(d:ℝ)/2)*K)*
        (t^(α-1-(d:ℝ)/2)*Real.exp (-(1/16)/t))+t^(α-1)
    have hri : IntegrableOn (fun t:ℝ=>t^(α-1)) (Set.Ioc 0 1) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))
    have hBi : IntegrableOn B (Set.Ioc 0 1) volume :=
      ((inverse_gaussian_integrable (α-1-(d:ℝ)/2) (1/16) (by norm_num)).const_mul _).add hri
    have hB0 (t:ℝ) (ht:t∈Set.Ioc (0:ℝ) 1) : 0≤B t := by
      have ht0 : 0≤t := ht.1.le
      dsimp [B]
      positivity
    let C := ∫t in Set.Ioc 0 1,B t
    refine ⟨C,integral_nonneg_of_ae ?_,?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hB0 t ht
    · intro y hy
      have hib : ∀ᵐt:ℝ∂volume.restrict (Set.Ioc 0 1),‖imageRemainder d α y t‖≤B t := by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        rw [Real.norm_eq_abs]
        exact image_remainder_bound d α K hK hmajor t ht.1 ht.2 y hy
      have hi : IntegrableOn (imageRemainder d α y) (Set.Ioc 0 1) volume :=
        hBi.mono' (image_remainder_measurable d α y).aestronglyMeasurable hib
      refine ⟨hi,?_⟩
      calc
        _ ≤ ∫t in Set.Ioc 0 1,|imageRemainder d α y t| := abs_integral_le_integral_abs
        _ ≤ C := integral_mono_ae hi.abs hBi (by
          filter_upwards [hib] with t ht
          simpa only [Real.norm_eq_abs] using ht)

  refine ⟨heat_gaussian_lift d, nonzero_image_uniform_majorant d, ?_⟩
  intro α hα
  simpa only [imageRemainder] using bounded_image_remainder d α hα
