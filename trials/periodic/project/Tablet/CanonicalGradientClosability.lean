import Tablet.CollisionSet
import Tablet.CanonicalLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Tablet.ConfigurationLift
import Tablet.TorusLift
import Tablet.ConfigurationCalculus
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Tablet.CanonicalDensityLocalComparison
import Tablet.CoordinateGradient
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Tablet.GradientGraphClosure
open MeasureTheory Set Filter
open scoped Topology ContDiff
attribute [local instance] Classical.propDecidable
-- [TABLET NODE: CanonicalGradientClosability]
theorem CanonicalGradientClosability (d N:ℕ) (hd:2≤d) (hN:2≤N)
    (s a l u β:ℝ) (hs:0≤s) (hsd:s<(d:ℝ)) (ha:0<a)
    (q:BoundedBackground d l u) (hβ:0≤β) (ε:ℝ) (hε:0≤ε) :
    ∀ (f:MeasureTheory.Lp ℝ 2 (CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β))
      (v w:MeasureTheory.Lp (EuclideanSpace ℝ (Fin N×Fin d)) 2
        (CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β)),
      (f,v)∈GradientGraphClosure (CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β) false →
      (f,w)∈GradientGraphClosure (CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β) false → v=w := by
-- BODY
  have circle_probability : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
    infer_instance
  have circle_null : NullSingletonClass (volume : Measure (AddCircle (1 : ℝ))) := by
    constructor
    intro x
    have h := AddCircle.volume_closedBall (T := 1) (x := x) 0
    simpa using h
  have difference_preserving (d N : ℕ) (i j : Fin N) (hij : i ≠ j) :
      MeasurePreserving (fun X : Configuration d N => X i-X j) volume volume := by
    letI := circle_probability
    have hp : MeasurePreserving (fun X : Configuration d N => (X i,X j)) volume
        ((volume : Measure (UnitAddTorus (Fin d))).prod volume) := by
      have hi := (ProbabilityTheory.iIndepFun_pi (μ := fun _ : Fin N =>
        (volume : Measure (UnitAddTorus (Fin d)))) (X := fun _ => id)
        (fun _ => aemeasurable_id)).indepFun hij
      refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), ?_⟩
      change Measure.map (fun X : Configuration d N => (X i,X j))
        (Measure.pi (fun _ : Fin N => (volume : Measure (UnitAddTorus (Fin d))))) = _
      have h := hi.map_prod_eq_prod_map_map
        (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
      simpa only [(measurePreserving_eval (fun _ : Fin N =>
        (volume : Measure (UnitAddTorus (Fin d)))) i).map_eq,
        (measurePreserving_eval (fun _ : Fin N =>
        (volume : Measure (UnitAddTorus (Fin d)))) j).map_eq] using h
    exact (measurePreserving_fst.comp (measurePreserving_sub_prod volume volume)).comp hp
  have collision_haar_null (d N : ℕ) (hd : 0 < d) :
      (volume : Measure (Configuration d N)) (CollisionSet d N) = 0 := by
    letI := circle_probability
    letI := circle_null
    letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
    have hnull : NullSingletonClass (volume : Measure (UnitAddTorus (Fin d))) := by
      infer_instance
    letI := hnull
    have hp (i j : Fin N) : (volume : Measure (Configuration d N)) {X | i<j ∧ X i=X j} = 0 := by
      by_cases hij : i<j
      · have hm := (difference_preserving d N i j (ne_of_lt hij)).measure_preimage
          (measurableSet_singleton (0 : UnitAddTorus (Fin d))).nullMeasurableSet
        change volume {X : Configuration d N | X i-X j=0} = volume {(0 : UnitAddTorus (Fin d))} at hm
        simpa only [sub_eq_zero, hij, true_and, measure_singleton] using hm
      · simp [hij]
    have he : CollisionSet d N = ⋃ i : Fin N, ⋃ j : Fin N, {X | i<j ∧ X i=X j} := by
      ext X
      simp [CollisionSet]
    rw [he]
    exact measure_iUnion_null fun i => measure_iUnion_null (hp i)
  have torus_lift_cube (d:ℕ) :
      MeasurePreserving (TorusLift d)
        (volume.restrict {y:EuclideanSpace ℝ (Fin d)|∀j,y j∈Ioc (0:ℝ) 1}) volume := by
    have hpi := measurePreserving_pi
      (fun _:Fin d=>(volume:Measure ℝ).restrict (Ioc 0 1))
      (fun _:Fin d=>(volume:Measure (AddCircle (1:ℝ))))
      (f := fun _:Fin d=>(fun x:ℝ=>(x:AddCircle (1:ℝ))))
      (fun _=>by simpa using AddCircle.measurePreserving_mk 1 0)
    have hof := (PiLp.volume_preserving_ofLp (Fin d)).restrict_preimage
      (s := Set.pi univ (fun _:Fin d=>Ioc (0:ℝ) 1))
      (MeasurableSet.univ_pi (fun _=>measurableSet_Ioc))
    have hmeasure : (volume:Measure (Fin d→ℝ)).restrict (Set.pi univ (fun _=>Ioc (0:ℝ) 1)) =
        Measure.pi (fun _:Fin d=>(volume:Measure ℝ).restrict (Ioc 0 1)) :=
      Measure.restrict_pi_pi (fun _:Fin d=>(volume:Measure ℝ)) _
    rw [hmeasure] at hof
    have he : WithLp.ofLp ⁻¹' (Set.pi univ (fun _:Fin d=>Ioc (0:ℝ) 1)) =
        {y:EuclideanSpace ℝ (Fin d)|∀j,y j∈Ioc (0:ℝ) 1} := by ext y; simp
    rw [he] at hof
    convert! hpi.comp hof using 1 <;> rfl
  have configuration_lift_cube (d N:ℕ) :
      MeasurePreserving (ConfigurationLift d N)
        (volume.restrict {y:EuclideanSpace ℝ (Fin N×Fin d)|∀ij,y ij∈Ioc (0:ℝ) 1}) volume := by
    let e := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (finProdFinEquiv:Fin N×Fin d≃Fin (N*d))
    have he := e.measurePreserving.restrict_preimage
      (s := {y:EuclideanSpace ℝ (Fin (N*d))|∀j,y j∈Ioc (0:ℝ) 1})
      (by
        convert (MeasurableSet.iInter fun j=>(PiLp.continuous_apply 2 (fun _:Fin (N*d)=>ℝ) j).measurable
          (measurableSet_Ioc : MeasurableSet (Ioc (0:ℝ) 1))) using 1
        ext y; simp)
    have hset : e ⁻¹' {y:EuclideanSpace ℝ (Fin (N*d))|∀j,y j∈Ioc (0:ℝ) 1} =
        {y:EuclideanSpace ℝ (Fin N×Fin d)|∀ij,y ij∈Ioc (0:ℝ) 1} := by
      ext y
      change (∀j,y (finProdFinEquiv.symm j)∈Ioc (0:ℝ) 1) ↔ _
      constructor
      · intro h ij; simpa using h (finProdFinEquiv ij)
      · intro h j; exact h (finProdFinEquiv.symm j)
    rw [hset] at he
    have hcalc := ConfigurationCalculus d N
    let ef : Configuration d N≃ᵐUnitAddTorus (Fin (N*d)) :=
      { toEquiv:=ConfigurationFlatten d N
        measurable_toFun:=hcalc.1
        measurable_invFun:=hcalc.2.1 }
    have hef : MeasurePreserving ef := ⟨hcalc.1,hcalc.2.2.1⟩
    have hp := hef.symm.comp ((torus_lift_cube (N*d)).comp he)
    convert! hp using 1
    funext y i j
    change (y (i,j):AddCircle (1:ℝ)) = ((e y) (finProdFinEquiv (i,j)):AddCircle (1:ℝ))
    change (y (i,j):AddCircle (1:ℝ)) = (y (finProdFinEquiv.symm (finProdFinEquiv (i,j))):AddCircle (1:ℝ))
    rw [Equiv.symm_apply_apply]
  have preserving_density {Ω Ξ:Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
      (μ:Measure Ω) (ν:Measure Ξ) (f:Ω→Ξ) (hf:MeasurePreserving f μ ν)
      (r:Ξ→ENNReal) (hr:Measurable r) :
      MeasurePreserving f (μ.withDensity (r∘f)) (ν.withDensity r) := by
    refine ⟨hf.measurable,?_⟩
    ext s hs
    rw [Measure.map_apply hf.measurable hs,withDensity_apply _ (hf.measurable hs),withDensity_apply _ hs]
    exact hf.setLIntegral_comp_preimage hs hr
  have local_measure_domination {Ω:Type} [MeasurableSpace Ω] (μ:Measure Ω)
      (r:Ω→ℝ) (K:Set Ω) (hK:MeasurableSet K) (m:ℝ) (hm:0<m)
      (hbound:∀ᵐx∂μ,x∈K → m≤r x) :
      μ.restrict K≤ENNReal.ofReal m⁻¹ • μ.withDensity (fun x=>ENNReal.ofReal (r x)) := by
    rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top,←withDensity_indicator_one hK]
    apply withDensity_mono
    filter_upwards [hbound] with x hx
    by_cases hX:x∈K
    · simp only [Set.indicator_of_mem hX,Pi.one_apply]
      change 1≤ENNReal.ofReal m⁻¹*ENNReal.ofReal (r x)
      rw [←ENNReal.ofReal_mul (inv_nonneg.mpr hm.le)]
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal
        ((one_le_inv_mul₀ hm).mpr (hx hX))
    · simp [Set.indicator_of_notMem hX]
  have weighted_local_pullback {Ω Ξ E:Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
      [NormedAddCommGroup E] [NormedSpace ℝ E]
      (μ:Measure Ω) (ν:Measure Ξ) (f:Ω→Ξ) (hf:MeasurePreserving f μ ν)
      (r:Ξ→ℝ) (hr:Measurable r) (K:Set Ω) (hK:MeasurableSet K) (m:ℝ) (hm:0<m)
      (hbound:∀ᵐx∂μ,x∈K → m≤r (f x)) :
      Measure.QuasiMeasurePreserving f (μ.restrict K) (ν.withDensity (fun x=>ENNReal.ofReal (r x))) ∧
      ∃T:Lp E 2 (ν.withDensity (fun x=>ENNReal.ofReal (r x))) →L[ℝ] Lp E 2 (μ.restrict K),
        ∀v,T v=ᵐ[μ.restrict K] (v:Ξ→E)∘f := by
    let P := ν.withDensity (fun x=>ENNReal.ofReal (r x))
    let Q := μ.withDensity (fun x=>ENNReal.ofReal (r (f x)))
    have hp : MeasurePreserving f Q P := by
      refine ⟨hf.measurable,?_⟩
      ext s hs
      rw [Measure.map_apply hf.measurable hs,withDensity_apply _ (hf.measurable hs),withDensity_apply _ hs]
      exact hf.setLIntegral_comp_preimage hs hr.ennreal_ofReal
    have hd := local_measure_domination μ (fun x=>r (f x)) K hK m hm hbound
    let R : Lp E 2 Q→L[ℝ] Lp E 2 (μ.restrict K) :=
      Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top hd
    let C : Lp E 2 P→L[ℝ] Lp E 2 Q :=
      (Lp.compMeasurePreservingₗᵢ ℝ f hp).toContinuousLinearMap
    refine ⟨hp.quasiMeasurePreserving.mono_left (Measure.absolutelyContinuous_of_le_smul hd),R.comp C,?_⟩
    intro v
    have hR : (R (C v):Ω→E)=ᵐ[μ.restrict K] (C v:Ω→E) :=
      Lp.coeFn_LpToLpOfMeasureLeSMul _ _ _
    have hC : (C v:Ω→E)=ᵐ[Q] (v:Ξ→E)∘f := Lp.coeFn_compMeasurePreserving v hp
    exact hR.trans ((Measure.absolutelyContinuous_of_le_smul hd).ae_eq hC)
  have actual_local_lp_pullback (d N:ℕ) (hd:2≤d) (hN:2≤N)
      (s a l u β:ℝ) (hs:0≤s) (hsd:s<(d:ℝ)) (ha:0<a)
      (q:BoundedBackground d l u) (hβ:0≤β) (ε:ℝ) (hε:0≤ε)
      (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
      (K:Set (EuclideanSpace ℝ (Fin N×Fin d))) (hK:IsCompact K)
      (hcube:K⊆{y:EuclideanSpace ℝ (Fin N×Fin d)|∀ij,y ij∈Ioc (0:ℝ) 1})
      (hfree:Disjoint (ConfigurationLift d N ''K) (CollisionSet d N)) :
      Measure.QuasiMeasurePreserving (ConfigurationLift d N) (volume.restrict K)
        (CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β) ∧
      ∃T:Lp E 2 (CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β) →L[ℝ]
          Lp E 2 (volume.restrict K),
        ∀v,T v=ᵐ[volume.restrict K] (v:Configuration d N→E)∘ConfigurationLift d N := by
    let W := GibbsWeight (N := N) (RieszKernel d s a ε) q.density β
    let Z := ∫X,W X
    let r := fun X:Configuration d N=>W X/Z
    let μ := (volume:Measure (EuclideanSpace ℝ (Fin N×Fin d))).restrict
      {y|∀ij,y ij∈Ioc (0:ℝ) 1}
    have hp : MeasurePreserving (ConfigurationLift d N) μ volume := configuration_lift_cube d N
    obtain ⟨L,M,hL,hM,hall⟩ := CanonicalLawUniformBounds d N hd hN s a l u β hs hsd ha q hβ
    have hr : Measurable r := (hall ε hε).1.div_const Z
    have hLift : Continuous (ConfigurationLift d N) := by
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      exact QuotientAddGroup.continuous_mk.comp (PiLp.continuous_apply 2 (fun _:Fin N×Fin d=>ℝ) (i,j))
    obtain ⟨m,hm,hmb⟩ := (CanonicalDensityLocalComparison d N hd hN s a l u β hs hsd ha q hβ ε hε).2
      (ConfigurationLift d N ''K) (hK.image hLift) hfree
    have hb : ∀ᵐy∂μ,y∈K → m≤r (ConfigurationLift d N y) := by
      have hh := hp.quasiMeasurePreserving.ae hmb
      filter_upwards [hh] with y hy
      intro hY
      simpa only [r,div_eq_mul_inv,mul_comm] using hy (mem_image_of_mem _ hY)
    have hT := weighted_local_pullback (E := E) μ volume (ConfigurationLift d N) hp r hr K hK.measurableSet m hm hb
    have he : μ.restrict K=(volume:Measure (EuclideanSpace ℝ (Fin N×Fin d))).restrict K := by
      rw [Measure.restrict_restrict hK.measurableSet,inter_eq_left.mpr hcube]
    rw [he] at hT
    exact hT
  have gradient_on_lift {d N : ℕ} (f : Configuration d N → ℝ)
      (y : EuclideanSpace ℝ (Fin N×Fin d)) (ij : Fin N×Fin d) :
      CoordinateGradient f (ConfigurationLift d N y) ij =
        fderiv ℝ (fun x=>f (ConfigurationLift d N x)) y (EuclideanSpace.single ij 1) := by
    have lift_translation_eq (y z : EuclideanSpace ℝ (Fin N×Fin d))
        (h : ConfigurationLift d N y=ConfigurationLift d N z)
        (x : EuclideanSpace ℝ (Fin N×Fin d)) :
        ConfigurationLift d N (x+(z-y))=ConfigurationLift d N x := by
      funext i j
      have hj := congrFun (congrFun h i) j
      change (y (i,j):AddCircle (1:ℝ))=(z (i,j):AddCircle (1:ℝ)) at hj
      simp only [ConfigurationLift,PiLp.add_apply,PiLp.sub_apply]
      rw [AddCircle.coe_add,AddCircle.coe_sub,←hj,sub_self,add_zero]
    have lift_fderiv_eq (y z : EuclideanSpace ℝ (Fin N×Fin d))
        (h : ConfigurationLift d N y=ConfigurationLift d N z) :
        fderiv ℝ (fun x=>f (ConfigurationLift d N x)) y=
          fderiv ℝ (fun x=>f (ConfigurationLift d N x)) z := by
      let Q:=fun x=>f (ConfigurationLift d N x)
      have hfun : (fun x=>Q (x+(z-y)))=Q := by
        funext x
        exact congrArg f (lift_translation_eq y z h x)
      have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := Q) (x := y) (z-y)
      rw [hfun] at hd
      simpa using hd
    let z : EuclideanSpace ℝ (Fin N×Fin d) := WithLp.toLp 2
      (fun ij=>(AddCircle.equivIco (1:ℝ) 0 (ConfigurationLift d N y ij.1 ij.2):ℝ))
    have hz : ConfigurationLift d N z=ConfigurationLift d N y := by
      funext i j
      simp [ConfigurationLift,z,AddCircle.coe_equivIco]
    change fderiv ℝ (fun x=>f (ConfigurationLift d N x)) z (EuclideanSpace.single ij 1)=_
    rw [lift_fderiv_eq z y hz]
  have lp_test_integral_tendsto {Ω:Type} [MeasurableSpace Ω] (P:Measure Ω)
      (f:ℕ→Lp ℝ 2 P) (g:Lp ℝ 2 P) (hf:Tendsto f atTop (𝓝 g))
      (φ:Ω→ℝ) (hφ:MemLp φ 2 P) :
      Tendsto (fun n=>∫x,φ x*f n x∂P) atTop (𝓝 (∫x,φ x*g x∂P)) := by
    have he (v:Lp ℝ 2 P) : inner ℝ (hφ.toLp φ) v=∫x,φ x*v x∂P := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hφ.coeFn_toLp] with x hx
      rw [hx]
      simp only [Real.inner_apply]
    have hcont : Continuous (fun v:Lp ℝ 2 P=>inner ℝ (hφ.toLp φ) v) :=
      continuous_const.inner continuous_id
    simpa only [Function.comp_def,he] using hcont.continuousAt.tendsto.comp hf
  have collision_closed (d N:ℕ) : IsClosed (CollisionSet d N) := by
    have he : CollisionSet d N=⋃i:Fin N,⋃j:Fin N,{X:Configuration d N|i<j∧X i=X j} := by
      ext X; simp [CollisionSet]
    rw [he]
    apply isClosed_iUnion_of_finite
    intro i
    apply isClosed_iUnion_of_finite
    intro j
    by_cases hij:i<j
    · simpa only [hij,true_and] using isClosed_eq (continuous_apply i) (continuous_apply j)
    · simp [hij]
  let configuration_chart (d N:ℕ) : Set (EuclideanSpace ℝ (Fin N×Fin d)) :=
    {y|(∀ij,y ij∈Ioo (0:ℝ) 1)∧ConfigurationLift d N y∉CollisionSet d N}
  have configuration_chart_open (d N:ℕ) : IsOpen (configuration_chart d N) := by
    have hc:Continuous (ConfigurationLift d N) := by
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      exact QuotientAddGroup.continuous_mk.comp (PiLp.continuous_apply 2 (fun _:Fin N×Fin d=>ℝ) (i,j))
    have hi : IsOpen {y:EuclideanSpace ℝ (Fin N×Fin d)|∀ij,y ij∈Ioo (0:ℝ) 1} := by
      convert (isOpen_iInter_of_finite fun ij=>(PiLp.continuous_apply 2 (fun _:Fin N×Fin d=>ℝ) ij).isOpen_preimage (Ioo (0:ℝ) 1) isOpen_Ioo) using 1
      ext y; simp
    exact hi.inter ((collision_closed d N).isOpen_compl.preimage hc)
  have configuration_chart_full (d N:ℕ) (hd:0<d) :
      ∀ᵐy:EuclideanSpace ℝ (Fin N×Fin d)∂
        volume.restrict {y:EuclideanSpace ℝ (Fin N×Fin d)|∀ij,y ij∈Ioc (0:ℝ) 1},
        y∈configuration_chart d N := by
    let C:Set (EuclideanSpace ℝ (Fin N×Fin d)):= {y|∀ij,y ij∈Ioc (0:ℝ) 1}
    have hC:MeasurableSet C := by
      convert (MeasurableSet.iInter fun ij=>(PiLp.continuous_apply 2 (fun _:Fin N×Fin d=>ℝ) ij).measurable
        (measurableSet_Ioc:MeasurableSet (Ioc (0:ℝ) 1))) using 1
      ext y; simp [C]
    have hmem:∀ᵐy∂volume.restrict C,y∈C:=ae_restrict_mem hC
    have hne:∀ᵐy:EuclideanSpace ℝ (Fin N×Fin d)∂volume,∀ij,y ij≠1 := by
      rw [ae_all_iff]
      intro ij
      have h := (PiLp.volume_preserving_ofLp (Fin N×Fin d)).quasiMeasurePreserving.ae
        (Measure.ae_eval_ne (fun _:Fin N×Fin d=>(volume:Measure ℝ)) ij 1)
      convert! h using 1
    have hner:∀ᵐy∂volume.restrict C,∀ij,y ij≠1:=hne.filter_mono (ae_mono Measure.restrict_le_self)
    have hf:∀ᵐX:Configuration d N∂volume,X∉CollisionSet d N := by
      rw [ae_iff]
      simpa using collision_haar_null d N hd
    have hfr := (configuration_lift_cube d N).quasiMeasurePreserving.ae hf
    filter_upwards [hmem,hner,hfr] with y hy hny hfy
    exact ⟨fun ij=>⟨(hy ij).1,lt_of_le_of_ne (hy ij).2 (hny ij)⟩,hfy⟩
  have canonical_gradient_test_zero (d N:ℕ) (hd:2≤d) (hN:2≤N)
      (s a l u β:ℝ) (hs:0≤s) (hsd:s<(d:ℝ)) (ha:0<a)
      (q:BoundedBackground d l u) (hβ:0≤β) (ε:ℝ) (hε:0≤ε)
      (g:ℕ→Configuration d N→ℝ)
      (hgs:∀n,g n∈SmoothCore d N)
      (hg:∀n,MemLp (g n) 2 (CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β))
      (hD:∀n,MemLp (CoordinateGradient (g n)) 2
        (CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β))
      (v:Lp (EuclideanSpace ℝ (Fin N×Fin d)) 2
        (CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β))
      (hzero:Tendsto (fun n=>(hg n).toLp (g n)) atTop (𝓝 0))
      (hv:Tendsto (fun n=>(hD n).toLp (CoordinateGradient (g n))) atTop (𝓝 v))
      (φ:EuclideanSpace ℝ (Fin N×Fin d)→ℝ) (hφ:ContDiff ℝ ∞ φ) (hφs:HasCompactSupport φ)
      (hcube:tsupport φ⊆{y:EuclideanSpace ℝ (Fin N×Fin d)|∀ij,y ij∈Ioc (0:ℝ) 1})
      (hfree:Disjoint (ConfigurationLift d N ''tsupport φ) (CollisionSet d N))
      (ij:Fin N×Fin d) :
      (∫y,φ y*(v (ConfigurationLift d N y)) ij)=0 := by
    let K:=tsupport φ
    let μ:Measure (EuclideanSpace ℝ (Fin N×Fin d)):=volume.restrict K
    have hK:IsCompact K:=hφs
    letI : IsFiniteMeasure μ := ⟨by simpa [μ] using hK.measure_lt_top⟩
    obtain ⟨hp,Ts,hTs⟩ := actual_local_lp_pullback d N hd hN s a l u β hs hsd ha q hβ ε hε ℝ K hK hcube hfree
    obtain ⟨_,Tv,hTv⟩ := actual_local_lp_pullback d N hd hN s a l u β hs hsd ha q hβ ε hε
      (EuclideanSpace ℝ (Fin N×Fin d)) K hK hcube hfree
    let F:=fun n=>(hg n).toLp (g n)
    let D:=fun n=>(hD n).toLp (CoordinateGradient (g n))
    let π : EuclideanSpace ℝ (Fin N×Fin d)→L[ℝ] ℝ := PiLp.proj 2 (fun _:Fin N×Fin d=>ℝ) ij
    let R:=π.compLpL 2 μ
    let ψ:=fun y=>fderiv ℝ φ y (EuclideanSpace.single ij 1)
    have hψc:Continuous ψ := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hψs:HasCompactSupport ψ:=hφs.fderiv_apply ℝ _
    have htest (f:EuclideanSpace ℝ (Fin N×Fin d)→ℝ) (hf:Continuous f) (hfs:HasCompactSupport f) :
        MemLp f 2 μ := by
      obtain ⟨C,hC⟩ := hfs.exists_bound_of_continuous hf
      exact MemLp.of_bound hf.aestronglyMeasurable C (Eventually.of_forall hC)
    have hφlp:=htest φ hφ.continuous hφs
    have hψlp:=htest ψ hψc hψs
    have hscoef (n:ℕ) : (Ts (F n):_→ℝ)=ᵐ[μ] (fun y=>g n (ConfigurationLift d N y)) :=
      (hTs _).trans (hp.ae (hg n).coeFn_toLp)
    have hdcoef (n:ℕ) : (R (Tv (D n)):_→ℝ)=ᵐ[μ]
        (fun y=>fderiv ℝ (fun z=>g n (ConfigurationLift d N z)) y (EuclideanSpace.single ij 1)) := by
      filter_upwards [π.coeFn_compLpL (Tv (D n)),hTv (D n),hp.ae (hD n).coeFn_toLp] with y hy hyt hraw
      dsimp only [R] at hy ⊢
      rw [hy,hyt]
      dsimp only [D,Function.comp_apply]
      rw [hraw]
      exact gradient_on_lift (g n) y ij
    have hvcoef : (R (Tv v):_→ℝ)=ᵐ[μ] (fun y=>(v (ConfigurationLift d N y)) ij) := by
      filter_upwards [π.coeFn_compLpL (Tv v),hTv v] with y hy hyt
      dsimp only [R] at hy ⊢
      rw [hy,hyt]
      rfl
    have hsconv : Tendsto (fun n=>∫y,ψ y*g n (ConfigurationLift d N y)∂μ) atTop (𝓝 (0:ℝ)) := by
      have ht := lp_test_integral_tendsto μ (fun n=>Ts (F n)) 0
        (by simpa only [F,μ,Function.comp_def,map_zero] using Ts.continuous.continuousAt.tendsto.comp hzero) ψ hψlp
      have hzint : (∫y,ψ y*(0:Lp ℝ 2 μ) y∂μ)=0 := by
        calc
          _ = ∫y,(0:ℝ)∂μ := integral_congr_ae ((Lp.coeFn_zero ℝ 2 μ).mono fun y hy=>by rw [hy];simp)
          _ = 0 := by simp
      rw [hzint] at ht
      apply ht.congr'
      exact Eventually.of_forall fun n=>integral_congr_ae ((hscoef n).mono fun y hy=>by dsimp only;rw [hy])
    have hdconv : Tendsto (fun n=>∫y,φ y*fderiv ℝ (fun z=>g n (ConfigurationLift d N z)) y
        (EuclideanSpace.single ij 1)∂μ) atTop (𝓝 (∫y,φ y*(v (ConfigurationLift d N y)) ij∂μ)) := by
      have ht := lp_test_integral_tendsto μ (fun n=>R (Tv (D n))) (R (Tv v))
        ((R.continuous.comp Tv.continuous).continuousAt.tendsto.comp hv) φ hφlp
      have heq : (∫y,φ y*(R (Tv v)) y∂μ)=(∫y,φ y*(v (ConfigurationLift d N y)) ij∂μ) :=
        integral_congr_ae (hvcoef.mono fun y hy=>by dsimp only;rw [hy])
      rw [heq] at ht
      apply ht.congr'
      exact Eventually.of_forall fun n=>integral_congr_ae ((hdcoef n).mono fun y hy=>by dsimp only;rw [hy])
    have hibp (n:ℕ) : (∫y,φ y*fderiv ℝ (fun z=>g n (ConfigurationLift d N z)) y
        (EuclideanSpace.single ij 1)∂μ)=-(∫y,ψ y*g n (ConfigurationLift d N y)∂μ) := by
      let f:=fun y=>g n (ConfigurationLift d N y)
      have hfc:ContDiff ℝ ∞ f:=hgs n
      have hdc : Continuous (fun y=>fderiv ℝ f y (EuclideanSpace.single ij 1)) :=
        (hfc.continuous_fderiv (by simp)).clm_apply continuous_const
      have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (μ := (volume:Measure (EuclideanSpace ℝ (Fin N×Fin d))))
        (f := f) (g := φ) (v := EuclideanSpace.single ij 1)
        ((hdc.mul hφ.continuous).integrable_of_hasCompactSupport hφs.mul_left)
        ((hfc.continuous.mul hψc).integrable_of_hasCompactSupport hψs.mul_left)
        ((hfc.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hφs.mul_left)
        (fun _ _=>hfc.differentiable (by simp) _)
        (fun _ _=>hφ.differentiable (by simp) _)
      have hs : (∫y,ψ y*f y∂μ)=∫y,f y*ψ y := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
        · simp_rw [mul_comm]
        · intro y hy
          change y∉tsupport φ at hy
          simp [ψ,fderiv_of_notMem_tsupport ℝ hy]
      have hd : (∫y,φ y*fderiv ℝ f y (EuclideanSpace.single ij 1)∂μ)=
          ∫y,fderiv ℝ f y (EuclideanSpace.single ij 1)*φ y := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
        · simp_rw [mul_comm]
        · intro y hy
          have hz : φ y=0 := by
            by_contra hz
            exact hy ((subset_tsupport φ) hz)
          rw [hz,zero_mul]
      rw [hs,hd]
      dsimp only [ψ]
      linarith
    have hlim0 : Tendsto (fun n=>∫y,φ y*fderiv ℝ (fun z=>g n (ConfigurationLift d N z)) y
        (EuclideanSpace.single ij 1)∂μ) atTop (𝓝 (0:ℝ)) := by
      simpa only [hibp,neg_zero] using hsconv.neg
    have hresult := tendsto_nhds_unique hdconv hlim0
    have hout (y:EuclideanSpace ℝ (Fin N×Fin d)) (hy:y∉K) : φ y*(v (ConfigurationLift d N y)) ij=0 := by
      have hz : φ y=0 := by
        by_contra hz
        exact hy ((subset_tsupport φ) hz)
      rw [hz,zero_mul]
    calc
      _ = ∫y,φ y*(v (ConfigurationLift d N y)) ij∂μ :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hout).symm
      _ = 0 := hresult
  have canonical_gradient_null_sequence (d N:ℕ) (hd:2≤d) (hN:2≤N)
      (s a l u β:ℝ) (hs:0≤s) (hsd:s<(d:ℝ)) (ha:0<a)
      (q:BoundedBackground d l u) (hβ:0≤β) (ε:ℝ) (hε:0≤ε)
      (g:ℕ→Configuration d N→ℝ)
      (hgs:∀n,g n∈SmoothCore d N)
      (hg:∀n,MemLp (g n) 2 (CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β))
      (hD:∀n,MemLp (CoordinateGradient (g n)) 2
        (CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β))
      (v:Lp (EuclideanSpace ℝ (Fin N×Fin d)) 2
        (CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β))
      (hzero:Tendsto (fun n=>(hg n).toLp (g n)) atTop (𝓝 0))
      (hv:Tendsto (fun n=>(hD n).toLp (CoordinateGradient (g n))) atTop (𝓝 v)) : v=0 := by
    let U:=configuration_chart d N
    have hU:IsOpen U:=configuration_chart_open d N
    have hcubeK (K:Set (EuclideanSpace ℝ (Fin N×Fin d))) (hKU:K⊆U) :
        K⊆{y:EuclideanSpace ℝ (Fin N×Fin d)|∀ij,y ij∈Ioc (0:ℝ) 1} :=
      fun y hy ij=>⟨((hKU hy).1 ij).1,((hKU hy).1 ij).2.le⟩
    have hfreeK (K:Set (EuclideanSpace ℝ (Fin N×Fin d))) (hKU:K⊆U) :
        Disjoint (ConfigurationLift d N ''K) (CollisionSet d N) := by
      apply Set.disjoint_left.mpr
      rintro X ⟨y,hy,rfl⟩ hX
      exact (hKU hy).2 hX
    have hpart (ij:Fin N×Fin d) : ∀ᵐy:EuclideanSpace ℝ (Fin N×Fin d)∂volume,
        y∈U → (v (ConfigurationLift d N y)) ij=0 := by
      have hlocal : LocallyIntegrableOn (fun y=>(v (ConfigurationLift d N y)) ij) U volume := by
        rw [locallyIntegrableOn_iff hU.isLocallyClosed]
        intro K hKU hK
        let μ:Measure (EuclideanSpace ℝ (Fin N×Fin d)):=volume.restrict K
        letI:IsFiniteMeasure μ:=⟨by simpa [μ] using hK.measure_lt_top⟩
        obtain ⟨_,T,hT⟩ := actual_local_lp_pullback d N hd hN s a l u β hs hsd ha q hβ ε hε
          (EuclideanSpace ℝ (Fin N×Fin d)) K hK (hcubeK K hKU) (hfreeK K hKU)
        let π:EuclideanSpace ℝ (Fin N×Fin d)→L[ℝ] ℝ:=PiLp.proj 2 (fun _:Fin N×Fin d=>ℝ) ij
        have he : (π.compLp (T v):_→ℝ)=ᵐ[μ] (fun y=>(v (ConfigurationLift d N y)) ij) := by
          filter_upwards [π.coeFn_compLp (T v),hT v] with y hy hyt
          rw [hy,hyt]
          rfl
        exact ((Lp.memLp (π.compLp (T v))).integrable (by norm_num)).congr he
      apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hlocal
      intro φ hφ hφs hφU
      simpa only [smul_eq_mul] using canonical_gradient_test_zero d N hd hN s a l u β hs hsd ha q hβ ε hε
        g hgs hg hD v hzero hv φ hφ hφs (hcubeK (tsupport φ) hφU) (hfreeK (tsupport φ) hφU) ij
    have hparts : ∀ᵐy:EuclideanSpace ℝ (Fin N×Fin d)∂volume,
        ∀ij,y∈U → (v (ConfigurationLift d N y)) ij=0 := (ae_all_iff).2 hpart
    have hzeroU : ∀ᵐy:EuclideanSpace ℝ (Fin N×Fin d)∂volume,
        y∈U → v (ConfigurationLift d N y)=0 := by
      filter_upwards [hparts] with y hy
      intro hY
      ext ij
      exact hy ij hY
    let μ:Measure (EuclideanSpace ℝ (Fin N×Fin d)):=volume.restrict
      {y:EuclideanSpace ℝ (Fin N×Fin d)|∀ij,y ij∈Ioc (0:ℝ) 1}
    have hzeroμ : ∀ᵐy∂μ,v (ConfigurationLift d N y)=0 := by
      filter_upwards [hzeroU.filter_mono (ae_mono Measure.restrict_le_self),
        configuration_chart_full d N (by omega)] with y hy hY
      exact hy hY
    let W:=GibbsWeight (N := N) (RieszKernel d s a ε) q.density β
    let r:=fun X:Configuration d N=>W X/(∫Y,W Y)
    obtain ⟨L,M,hL,hM,hall⟩ := CanonicalLawUniformBounds d N hd hN s a l u β hs hsd ha q hβ
    have hr:Measurable (fun X=>ENNReal.ofReal (r X)):=((hall ε hε).1.div_const _).ennreal_ofReal
    have hp:=preserving_density μ volume (ConfigurationLift d N) (configuration_lift_cube d N)
      (fun X=>ENNReal.ofReal (r X)) hr
    have hzeroρ : ∀ᵐy∂μ.withDensity ((fun X=>ENNReal.ofReal (r X))∘ConfigurationLift d N),
        v (ConfigurationLift d N y)=0 := by
      have hac : μ.withDensity ((fun X=>ENNReal.ofReal (r X))∘ConfigurationLift d N) ≪ μ :=
        withDensity_absolutelyContinuous μ _
      exact hzeroμ.filter_mono hac.ae_le
    have hmeas:MeasurableSet {X:Configuration d N|v X=0}:=
      measurableSet_eq_fun (Lp.stronglyMeasurable v).measurable measurable_const
    have hzeroP : ∀ᵐX∂CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β,v X=0 := by
      change ∀ᵐX∂volume.withDensity (fun X=>ENNReal.ofReal (r X)),v X=0
      rw [←hp.map_eq,ae_map_iff hp.aemeasurable hmeas]
      exact hzeroρ
    exact Lp.eq_zero_iff_ae_eq_zero.mpr hzeroP
  have coordinate_gradient_sub {d N:ℕ} {f g:Configuration d N→ℝ}
      (hf:f∈SmoothCore d N) (hg:g∈SmoothCore d N) :
      CoordinateGradient (fun X=>f X-g X)=fun X=>CoordinateGradient f X-CoordinateGradient g X := by
    funext X
    let y:EuclideanSpace ℝ (Fin N×Fin d):=WithLp.toLp 2
      (fun ij=>(AddCircle.equivIco (1:ℝ) 0 (X ij.1 ij.2):ℝ))
    have hfd:DifferentiableAt ℝ (fun y=>f (ConfigurationLift d N y)) y:=
      (show ContDiff ℝ ∞ (fun y=>f (ConfigurationLift d N y)) from hf).differentiable (by simp) |>.differentiableAt
    have hgd:DifferentiableAt ℝ (fun y=>g (ConfigurationLift d N y)) y:=
      (show ContDiff ℝ ∞ (fun y=>g (ConfigurationLift d N y)) from hg).differentiable (by simp) |>.differentiableAt
    ext ij
    change fderiv ℝ (fun z=>f (ConfigurationLift d N z)-g (ConfigurationLift d N z)) y
      (EuclideanSpace.single ij 1)=_
    change fderiv ℝ ((fun z=>f (ConfigurationLift d N z))-(fun z=>g (ConfigurationLift d N z))) y
      (EuclideanSpace.single ij 1)=_
    rw [fderiv_sub hfd hgd]
    rfl
  have canonical_gradient_unique (d N:ℕ) (hd:2≤d) (hN:2≤N)
      (s a l u β:ℝ) (hs:0≤s) (hsd:s<(d:ℝ)) (ha:0<a)
      (q:BoundedBackground d l u) (hβ:0≤β) (ε:ℝ) (hε:0≤ε)
      (f:Lp ℝ 2 (CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β))
      (v w:Lp (EuclideanSpace ℝ (Fin N×Fin d)) 2
        (CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β))
      (hv:(f,v)∈GradientGraphClosure (CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β) false)
      (hw:(f,w)∈GradientGraphClosure (CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β) false) : v=w := by
    rw [GradientGraphClosure,mem_closure_iff_seq_limit] at hv hw
    obtain ⟨x,hx,hxt⟩:=hv
    obtain ⟨y,hy,hyt⟩:=hw
    have hx' : ∀n,∃(g:Configuration d N→ℝ) (hg:MemLp g 2 _)
        (hD:MemLp (CoordinateGradient g) 2 _),g∈SmoothCore d N ∧
        x n=(hg.toLp g,hD.toLp (CoordinateGradient g)):=by simpa using hx
    have hy' : ∀n,∃(g:Configuration d N→ℝ) (hg:MemLp g 2 _)
        (hD:MemLp (CoordinateGradient g) 2 _),g∈SmoothCore d N ∧
        y n=(hg.toLp g,hD.toLp (CoordinateGradient g)):=by simpa using hy
    choose g hg hD hgs hxe using hx'
    choose k hk hE hks hye using hy'
    let z:=fun n X=>g n X-k n X
    have hzs:∀n,z n∈SmoothCore d N:=by
      intro n
      exact (show ContDiff ℝ ∞ (fun y=>g n (ConfigurationLift d N y)) from hgs n).sub
        (show ContDiff ℝ ∞ (fun y=>k n (ConfigurationLift d N y)) from hks n)
    have hz:∀n,MemLp (z n) 2 (CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β):=fun n=>(hg n).sub (hk n)
    have hDz:∀n,MemLp (CoordinateGradient (z n)) 2 (CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β):=by
      intro n
      rw [show CoordinateGradient (z n)=fun X=>CoordinateGradient (g n) X-CoordinateGradient (k n) X
        from coordinate_gradient_sub (hgs n) (hks n)]
      exact (hD n).sub (hE n)
    have hfun:Tendsto (fun n=>(hz n).toLp (z n)) atTop (𝓝 0):=by
      have h := hxt.fst_nhds.sub hyt.fst_nhds
      simp only [sub_self] at h
      convert h using 1
      funext n
      rw [hxe,hye]
      simp only [Prod.fst,←MemLp.toLp_sub]
      apply MemLp.toLp_congr
      exact Filter.Eventually.of_forall (fun X=>rfl)
    have hgrad:Tendsto (fun n=>(hDz n).toLp (CoordinateGradient (z n))) atTop (𝓝 (v-w)):=by
      have h := hxt.snd_nhds.sub hyt.snd_nhds
      convert h using 1
      funext n
      rw [hxe,hye]
      simp only [Prod.snd,←MemLp.toLp_sub]
      apply MemLp.toLp_congr
      exact Filter.Eventually.of_forall (fun X=>congrFun (coordinate_gradient_sub (hgs n) (hks n)) X)
    have hzv:=canonical_gradient_null_sequence d N hd hN s a l u β hs hsd ha q hβ ε hε
      z hzs hz hDz (v-w) hfun hgrad
    exact sub_eq_zero.mp hzv
  exact canonical_gradient_unique d N hd hN s a l u β hs hsd ha q hβ ε hε
