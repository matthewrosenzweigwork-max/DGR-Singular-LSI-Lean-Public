module

public import Tablet.RieszKernel
public import Tablet.HeatKernelFacts
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Tablet.CenteredKernelBounds
public import Tablet.CenteredPairEnergy
public import Tablet.RieszMellinNear

@[expose] public section
open MeasureTheory Set Filter
open scoped Topology
-- [TABLET NODE: RieszMellinNearCap]
theorem RieszMellinNearCap (d:ℕ) (s a:ℝ) (hsd:s<(d:ℝ)) (ha:0<a)
    (δ ε:ℝ) (hδ:0<δ) (hε:0≤ε) (M:ℝ) (hM:1≤M)
    (r:UnitAddTorus (Fin d)→ℝ) (hr:Measurable r)
    (hrb:∀ᵐx∂(volume:Measure (UnitAddTorus (Fin d))),0≤r x ∧ r x≤M)
    (hrmass:∫x,r x=1) :
    let α:=((d:ℝ)-s)/2
    let m:=(a/Real.Gamma α)*δ^α/α
    let G:=RieszMellinNear d s a δ ε
    Measurable G ∧ Integrable G volume ∧ (∀x,0≤G x) ∧ (∫x,G x)=m ∧
    (∀x,0≤BackgroundPotential G r x ∧ BackgroundPotential G r x≤M*m) ∧
    0≤BackgroundPairMean G r ∧ (∀x y,-2*M*m≤CenteredKernel G r x y) ∧
    (∀N:ℕ,0<N→∀X:Configuration d N,-((N:ℝ)-1)*M*m≤CenteredPairEnergy G r X) := by
-- BODY
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
  have near_joint (d:ℕ) (α δ ε:ℝ) (hα:0<α) (hδ:0<δ) (hε:0≤ε) :
      Integrable (fun p:ℝ×UnitAddTorus (Fin d)=>p.1^(α-1)*HeatKernel d (p.1+ε) p.2)
        ((volume.restrict (Ioc 0 δ)).prod volume) := by
    letI:IsProbabilityMeasure (volume:Measure (AddCircle (1:ℝ))):=by
      rw [AddCircle.volume_eq_smul_haarAddCircle];simp;infer_instance
    have hm:Measurable (fun p:ℝ×UnitAddTorus (Fin d)=>p.1^(α-1)*HeatKernel d (p.1+ε) p.2):=
      (measurable_fst.pow_const _).mul ((heat_joint_measurable d).comp
        ((measurable_fst.add_const ε).prodMk measurable_snd))
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact ((HeatKernelFacts d (t+ε) (add_pos_of_pos_of_nonneg ht.1 hε)).1.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)).const_mul _
    · apply (power_integrable α δ hα hδ).congr
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have hp:∀x,0≤HeatKernel d (t+ε) x:=(HeatKernelFacts d (t+ε) (add_pos_of_pos_of_nonneg ht.1 hε)).2.1
      have hr:0≤t^(α-1):=Real.rpow_nonneg ht.1.le _
      simp only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hr (hp _)),integral_const_mul,
        (HeatKernelFacts d (t+ε) (add_pos_of_pos_of_nonneg ht.1 hε)).2.2.2.1,mul_one]
  
  
  have near_raw_properties (d:ℕ) (α δ ε:ℝ) (hα:0<α) (hδ:0<δ) (hε:0≤ε) :
      let G:=fun x:UnitAddTorus (Fin d)=>∫t in Ioc (0:ℝ) δ,t^(α-1)*HeatKernel d (t+ε) x
      Measurable G ∧ Integrable G volume ∧ (∀x,0≤G x) ∧ (∫x,G x)=δ^α/α := by
    letI:IsProbabilityMeasure (volume:Measure (AddCircle (1:ℝ))):=by
      rw [AddCircle.volume_eq_smul_haarAddCircle];simp;infer_instance
    have hm:Measurable (fun p:ℝ×UnitAddTorus (Fin d)=>p.1^(α-1)*HeatKernel d (p.1+ε) p.2):=
      (measurable_fst.pow_const _).mul ((heat_joint_measurable d).comp
        ((measurable_fst.add_const ε).prodMk measurable_snd))
    have hi:=near_joint d α δ ε hα hδ hε
    refine ⟨hm.stronglyMeasurable.integral_prod_left'.measurable,hi.integral_prod_right,?_,?_⟩
    · intro x
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact mul_nonneg (Real.rpow_nonneg ht.1.le _) ((HeatKernelFacts d (t+ε)
        (add_pos_of_pos_of_nonneg ht.1 hε)).2.1 x)
    · have hs:Integrable (Function.uncurry (fun (x:UnitAddTorus (Fin d)) (t:ℝ)=>
          t^(α-1)*HeatKernel d (t+ε) x)) (volume.prod (volume.restrict (Ioc 0 δ))) := by
        convert hi.swap using 1 <;> rfl
      rw [integral_integral_swap hs]
      have he:(fun t:ℝ=>∫x:UnitAddTorus (Fin d),t^(α-1)*HeatKernel d (t+ε) x)=ᵐ[volume.restrict (Ioc 0 δ)]
          (fun t:ℝ=>t^(α-1)):=by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        rw [integral_const_mul,(HeatKernelFacts d (t+ε)
          (add_pos_of_pos_of_nonneg ht.1 hε)).2.2.2.1,mul_one]
      rw [integral_congr_ae he]
      exact power_mass α δ hα hδ
  have positive_nearfield_cap (d:ℕ) (g r:UnitAddTorus (Fin d)→ℝ)
      (hg:Measurable g) (hi:Integrable g volume) (hn:∀x,0≤g x)
      (hr:Measurable r) (M:ℝ) (hM:1≤M)
      (hrb:∀ᵐx∂(volume:Measure (UnitAddTorus (Fin d))),0≤r x ∧ r x≤M)
      (hmass:∫x,r x=1) :
      (∀x,0≤BackgroundPotential g r x ∧ BackgroundPotential g r x≤M*(∫y,g y)) ∧
      0≤BackgroundPairMean g r ∧
      (∀x y,-2*M*(∫z,g z)≤CenteredKernel g r x y) ∧
      (∀(N:ℕ),0<N→∀X:Configuration d N,
        -((N:ℝ)-1)*M*(∫z,g z)≤CenteredPairEnergy g r X) := by
    obtain ⟨_,hb,_,_,_,_,_⟩:=CenteredKernelBounds d g r hg hi hr M 0 hM (by rfl) hrb hmass
      (by simpa using hn)
    have hpos(x):0≤BackgroundPotential g r x:=by
      apply integral_nonneg_of_ae
      filter_upwards [hrb] with y hy
      exact mul_nonneg hy.1 (hn _)
    have hup(x):BackgroundPotential g r x≤M*(∫y,g y):=by
      have h:∫y,|g y|=∫y,g y:=integral_congr_ae (Eventually.of_forall fun y=>abs_of_nonneg (hn y))
      rw [h] at hb
      exact (le_abs_self _).trans (hb x).2
    have hJ:0≤BackgroundPairMean g r:=by
      apply integral_nonneg_of_ae
      filter_upwards [hrb] with y hy
      exact mul_nonneg (hpos y) hy.1
    have hlow(x y):-2*M*(∫z,g z)≤CenteredKernel g r x y:=by
      unfold CenteredKernel
      linarith [hn (x-y),hup x,hup y]
    refine ⟨fun x=>⟨hpos x,hup x⟩,hJ,hlow,?_⟩
    intro N hN X
    have hcount : (∑ i : Fin N,∑ j : Fin N,if i < j then (1:ℝ) else 0) =
        (N:ℝ)*((N:ℝ)-1)/2 := by
      have hterm (i j : Fin N) : (if j = i then (0:ℝ) else 1) =
          (if i < j then 1 else 0)+(if j < i then 1 else 0) := by
        rcases lt_trichotomy i j with h|h|h
        · simp [h,ne_of_gt h,not_lt_of_gt h]
        · subst j;simp
        · simp [h,ne_of_lt h,not_lt_of_gt h]
      have hs : (∑ i : Fin N,∑ j : Fin N,if j = i then (0:ℝ) else 1) =
          2*(∑ i : Fin N,∑ j : Fin N,if i < j then (1:ℝ) else 0) := by
        simp_rw [hterm,Finset.sum_add_distrib]
        rw [Finset.sum_comm (f := fun i j : Fin N => if j < i then (1:ℝ) else 0)]
        ring
      have hrw (i : Fin N) : (∑ j : Fin N,if j = i then (0:ℝ) else 1) = (N:ℝ)-1 := by
        have ht (j : Fin N) : (if j = i then (0:ℝ) else 1)=1-(if j = i then 1 else 0) := by
          split_ifs <;>ring
        simp_rw [ht]
        simp [Finset.sum_sub_distrib]
      simp_rw [hrw] at hs
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
      linarith
    have hnz:(N:ℝ)≠0:=by exact_mod_cast (show N≠0 by omega)
    calc
      _ = (N:ℝ)⁻¹*∑i:Fin N,∑j:Fin N,if i<j then -2*M*(∫z,g z) else 0:=by
        have ht (i j:Fin N):(if i<j then -2*M*(∫z,g z) else 0)=
            (if i<j then (1:ℝ) else 0)*(-2*M*(∫z,g z)):=by split_ifs <;>ring
        simp_rw [ht,←Finset.sum_mul]
        rw [hcount]
        field_simp
      _ ≤ _ := by
        unfold CenteredPairEnergy
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg N))
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        split_ifs
        · exact hlow _ _
        · rfl
  have riesz_near_properties (d:ℕ) (s a:ℝ) (hsd:s<(d:ℝ)) (ha:0<a)
      (δ ε:ℝ) (hδ:0<δ) (hε:0≤ε) :
      let α:=((d:ℝ)-s)/2
      let m:=(a/Real.Gamma α)*δ^α/α
      Measurable (RieszMellinNear d s a δ ε) ∧
      Integrable (RieszMellinNear d s a δ ε) volume ∧
      (∀x,0≤RieszMellinNear d s a δ ε x) ∧
      (∫x,RieszMellinNear d s a δ ε x)=m := by
    let α:=((d:ℝ)-s)/2
    have hα:0<α:=by dsimp[α];linarith
    obtain ⟨hm,hi,hn,hI⟩:=near_raw_properties d α δ ε hα hδ hε
    have hc:0≤a/Real.Gamma α:=(div_pos ha (Real.Gamma_pos_of_pos hα)).le
    refine ⟨hm.const_mul _,hi.const_mul _,fun x=>mul_nonneg hc (hn x),?_⟩
    change (∫x,(a/Real.Gamma α)*(∫t in Ioc (0:ℝ) δ,t^(α-1)*HeatKernel d (t+ε) x))=_
    rw [integral_const_mul,hI]
    ring
  obtain ⟨hm,hi,hn,hI⟩:=riesz_near_properties d s a hsd ha δ ε hδ hε
  have hc:=positive_nearfield_cap d (RieszMellinNear d s a δ ε) r hm hi hn hr M hM hrb hrmass
  rw [hI] at hc
  exact ⟨hm,hi,hn,hI,hc⟩
