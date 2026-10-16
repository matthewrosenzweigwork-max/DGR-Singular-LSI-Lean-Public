module

public import Tablet.RieszLocalStructure
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.Tactic

@[expose] public section
open MeasureTheory Metric Set
open scoped ENNReal NNReal
-- [TABLET NODE: RieszL2Threshold]
theorem RieszL2Threshold (d : ℕ) (hd : 2 ≤ d) (s a : ℝ)
    (hs : 0 ≤ s) (hsd : s < (d : ℝ)) (ha : 0 < a) :
    MeasureTheory.MemLp (RieszKernel d s a 0) 2 (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d))) ↔
      s < (d : ℝ) / 2 := by
-- BODY
  classical
  let signedCube (d:ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
    {y | ∀j, y j ∈ Set.Ioc (-(1:ℝ)/2) (1/2)}
  let closedCube (d:ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
    {y | ∀j, y j ∈ Set.Icc (-(1:ℝ)/2) (1/2)}

  have lift_signedCube_preserving (d:ℕ) :
      MeasurePreserving (TorusLift d) (volume.restrict (signedCube d))
        (volume:Measure (UnitAddTorus (Fin d))) := by
    let C : Set (Fin d→ℝ) := Set.univ.pi (fun _=>Set.Ioc (-(1:ℝ)/2) (1/2))
    have hC : MeasurableSet C := MeasurableSet.univ_pi (fun _=>measurableSet_Ioc)
    have hflat := (PiLp.volume_preserving_ofLp (Fin d)).restrict_preimage hC
    have hpi := measurePreserving_pi
      (fun _:Fin d=>(volume:Measure ℝ).restrict (Set.Ioc (-(1:ℝ)/2) (1/2)))
      (fun _:Fin d=>(volume:Measure (AddCircle (1:ℝ))))
      (f:=fun _:Fin d=>((↑):ℝ→AddCircle (1:ℝ)))
      (fun _=>by convert (AddCircle.measurePreserving_mk (1:ℝ) (-(1:ℝ)/2)) using 1 <;> first | rfl | norm_num)
    have hrestrict : (volume:Measure (Fin d→ℝ)).restrict C =
        Measure.pi (fun _:Fin d=>(volume:Measure ℝ).restrict (Set.Ioc (-(1:ℝ)/2) (1/2))) :=
      Measure.restrict_pi_pi (fun _:Fin d=>(volume:Measure ℝ)) _
    rw [←hrestrict] at hpi
    have hs : WithLp.ofLp ⁻¹' C = signedCube d := by
      ext y
      simp only [signedCube,C,Set.mem_preimage,Set.mem_setOf_eq,Set.mem_pi,Set.mem_univ,true_implies]
    rw [hs] at hflat
    convert! hpi.comp hflat using 1 <;> rfl

  have memLp_signedCube_iff (d:ℕ) (f:UnitAddTorus (Fin d)→ℝ) (hf:Measurable f) :
      MemLp f 2 (volume:Measure (UnitAddTorus (Fin d))) ↔
        MemLp (fun y:EuclideanSpace ℝ (Fin d)=>f (TorusLift d y)) 2
          (volume.restrict (signedCube d)) := by
    have hp:=lift_signedCube_preserving d
    have hm : AEStronglyMeasurable f (Measure.map (TorusLift d) (volume.restrict (signedCube d))) := by
      rw [hp.map_eq]
      exact hf.aestronglyMeasurable
    have h := memLp_map_measure_iff (p:=2) hm hp.aemeasurable
    simpa only [hp.map_eq,Function.comp_def] using h

  have lift_zero_closedCube (d:ℕ) (y:EuclideanSpace ℝ (Fin d)) (hy:y∈closedCube d) :
      TorusLift d y=0 ↔ y=0 := by
    constructor
    · intro h
      apply PiLp.ext
      intro j
      have hj : (y j:AddCircle (1:ℝ))=0 := congrFun h j
      obtain ⟨n,hn⟩ := (AddCircle.coe_eq_zero_iff (p:=(1:ℝ))).mp hj
      simp only [zsmul_eq_mul,mul_one] at hn
      have hlo := (hy j).1
      have hhi := (hy j).2
      have hnzero : n=0 := by
        by_contra hn0
        have hh : (1:ℤ)≤n ∨ n≤-1 := by omega
        rcases hh with hh | hh
        · have : (1:ℝ)≤(n:ℝ) := by exact_mod_cast hh
          linarith
        · have : (n:ℝ)≤-1 := by exact_mod_cast hh
          linarith
      change y j = 0
      simpa only [hnzero,Int.cast_zero] using hn.symm
    · rintro rfl
      rfl

  have ball_subset_signedCube (d:ℕ) {r:ℝ} (hr:r≤1/2) :
      Metric.ball (0:EuclideanSpace ℝ (Fin d)) r ⊆ signedCube d := by
    intro y hy j
    have hnorm : ‖y‖<r := by simpa only [Metric.mem_ball,dist_zero_right] using hy
    have hb : |y j|<1/2 := lt_of_le_of_lt (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le y j) (hnorm.trans_le hr)
    constructor <;> linarith [(abs_lt.mp hb).1,(abs_lt.mp hb).2]

  have power_integrable_iff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
      (μ : Measure E) [μ.IsAddHaarMeasure] (s r : ℝ) (hr : 0 < r) :
      IntegrableOn (fun x : E => ‖x‖ ^ (-s)) (ball 0 r) μ ↔
        s < (Module.finrank ℝ E : ℝ) := by
    rw [integrableOn_fun_norm_addHaar μ (f := fun y : ℝ => y ^ (-s))]
    have hd : 0 < Module.finrank ℝ E := Module.finrank_pos
    have heq : (fun y : ℝ => y ^ (Module.finrank ℝ E - 1) • y ^ (-s)) =ᵐ[
        volume.restrict (Ioo 0 r)]
        (fun y : ℝ => y ^ ((Module.finrank ℝ E : ℝ) - 1 - s)) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with y hy
      rw [smul_eq_mul, ← Real.rpow_natCast, ← Real.rpow_add hy.1]
      congr 1
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hd.ne'), Nat.cast_one]
      ring
    change Integrable (fun y : ℝ => y ^ (Module.finrank ℝ E - 1) • y ^ (-s)) (volume.restrict (Ioo 0 r)) ↔ _
    rw [integrable_congr heq]
    change IntegrableOn (fun y : ℝ => y ^ ((Module.finrank ℝ E : ℝ) - 1 - s)) (Ioo 0 r) ↔ _
    rw [intervalIntegral.integrableOn_Ioo_rpow_iff hr]
    constructor <;> intro h <;> linarith

  have power_memLp_two_iff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
      (μ : Measure E) [μ.IsAddHaarMeasure] (s r : ℝ) (hr : 0 < r) :
      MemLp (fun x : E => ‖x‖ ^ (-s)) 2 (μ.restrict (ball 0 r)) ↔
        2*s < (Module.finrank ℝ E : ℝ) := by
    have hm : AEStronglyMeasurable (fun x : E => ‖x‖ ^ (-s)) (μ.restrict (ball 0 r)) :=
      (continuous_norm.measurable.pow_const (-s)).aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq hm]
    have heq : (fun x : E => (‖x‖ ^ (-s))^2) = (fun x => ‖x‖ ^ (-(2*s))) := by
      ext x
      rw [← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _)]
      congr 1
      ring
    rw [heq]
    exact power_integrable_iff μ (2*s) r hr

  have log_inverse_bound (t ε : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (hε : 0 < ε) :
      ‖Real.log (1/t)‖ ≤ ε⁻¹ * t ^ (-ε) := by
    by_cases hz : t = 0
    · subst t
      simp [Real.zero_rpow (neg_ne_zero.mpr hε.ne')]
    have hp : 0 < t := lt_of_le_of_ne ht (Ne.symm hz)
    have hi : 1 ≤ 1/t := (le_div_iff₀ hp).mpr (by simpa using ht1)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hi)]
    have hb := Real.log_le_rpow_div (show 0 ≤ 1/t by positivity) hε
    simpa only [one_div, ← Real.rpow_neg_eq_inv_rpow, div_eq_mul_inv, mul_one, mul_comm] using hb

  have log_memLp_two {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
      (μ : Measure E) [μ.IsAddHaarMeasure] (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
      MemLp (fun x : E => Real.log (1/‖x‖)) 2 (μ.restrict (ball 0 r)) := by
    let ε : ℝ := (Module.finrank ℝ E : ℝ)/4
    have hd : 0 < (Module.finrank ℝ E : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
    have hε : 0 < ε := by dsimp [ε]; positivity
    have hp := (power_memLp_two_iff μ ε r hr).mpr (by dsimp [ε]; linarith)
    have hm : AEStronglyMeasurable (fun x : E => Real.log (1/‖x‖))
        (μ.restrict (ball 0 r)) :=
      (Real.measurable_log.comp (measurable_const.div continuous_norm.measurable)).aestronglyMeasurable
    apply (hp.const_mul ε⁻¹).mono' hm
    filter_upwards [self_mem_ae_restrict measurableSet_ball] with x hx
    exact log_inverse_bound ‖x‖ ε (norm_nonneg _) (le_trans (le_of_lt (mem_ball_zero_iff.mp hx)) hr1) hε

  have bounded_remainder_iff {α : Type} [MeasurableSpace α] (μ : Measure α)
      [IsFiniteMeasure μ] (f g : α → ℝ) (b C : ℝ) (hb : b ≠ 0)
      (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
      (hbound : ∀ᵐ x ∂μ, |f x - b*g x| ≤ C) :
      MemLp f 2 μ ↔ MemLp g 2 μ := by
    have hr : MemLp (fun x => f x-b*g x) 2 μ := MemLp.of_bound
      (hf.sub (hg.const_mul b)) C (by simpa only [Real.norm_eq_abs] using hbound)
    constructor
    · intro h
      have hbg : MemLp (fun x => b*g x) 2 μ := by
        convert h.sub hr using 1
        ext x
        simp only [Pi.sub_apply]
        ring
      convert hbg.const_mul b⁻¹ using 1
      ext x
      field_simp
    · intro h
      convert hr.add (h.const_mul b) using 1
      ext x
      simp only [Pi.add_apply]
      ring

  have compact_closedCube (d:ℕ) : IsCompact (closedCube d) := by
    have hc := isCompact_univ_pi (fun _:Fin d=>isCompact_Icc (a:=-(1:ℝ)/2) (b:=1/2))
    have hp := (PiLp.homeomorph 2 (fun _:Fin d=>ℝ)).isCompact_preimage.mpr hc
    convert hp using 1
    ext y
    simp only [closedCube,Set.mem_preimage,Set.mem_setOf_eq,
      Set.mem_pi,Set.mem_univ,true_implies]
    rfl

  have measurable_signedCube (d:ℕ) : MeasurableSet (signedCube d) := by
    have hc : MeasurableSet (Set.univ.pi (fun _:Fin d=>Set.Ioc (-(1:ℝ)/2) (1/2))) :=
      MeasurableSet.univ_pi (fun _=>measurableSet_Ioc)
    convert hc.preimage (PiLp.continuous_ofLp (p:=2) (β:=fun _:Fin d=>ℝ)).measurable using 1
    ext y
    simp only [signedCube,Set.mem_preimage,Set.mem_setOf_eq,
      Set.mem_pi,Set.mem_univ,true_implies]

  have signedCube_finite (d:ℕ) : IsFiniteMeasure
      ((volume:Measure (EuclideanSpace ℝ (Fin d))).restrict (signedCube d)) := by
    apply isFiniteMeasure_restrict.mpr
    apply lt_top_iff_ne_top.mp
    exact (measure_mono (show signedCube d ⊆ closedCube d from
      fun y hy j=>(hy j).imp le_of_lt id)).trans_lt (compact_closedCube d).measure_lt_top

  have cube_memLp_iff_ball (d:ℕ) (f:EuclideanSpace ℝ (Fin d)→ℝ)
      (hf:Measurable f) (hfc:ContinuousOn f {y|TorusLift d y≠0}) :
      MemLp f 2 (volume.restrict (signedCube d)) ↔
        MemLp f 2 (volume.restrict (ball 0 (1/8))) := by
    classical
    have hsub := ball_subset_signedCube d (r:=(1/8:ℝ)) (by norm_num)
    constructor
    · intro h
      exact h.mono_measure (Measure.restrict_mono_set volume hsub)
    · intro h
      let ν : Measure (EuclideanSpace ℝ (Fin d)) := volume.restrict (signedCube d)
      haveI : IsFiniteMeasure ν := signedCube_finite d
      let K := closedCube d ∩ (ball (0:EuclideanSpace ℝ (Fin d)) (1/8))ᶜ
      have hK : IsCompact K := (compact_closedCube d).inter_right isOpen_ball.isClosed_compl
      have hKsub : K ⊆ {y|TorusLift d y≠0} := by
        intro y hy hzero
        have hyzero := (lift_zero_closedCube d y hy.1).mp hzero
        subst y
        exact hy.2 (by simp only [mem_ball,dist_self]; norm_num)
      obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn (hfc.mono hKsub)
      have hnear : MemLp f 2 (ν.restrict (ball 0 (1/8))) :=
        h.mono_measure (Measure.restrict_mono_measure Measure.restrict_le_self _)
      have hfar : MemLp f 2 (ν.restrict (ball 0 (1/8))ᶜ) := by
        apply MemLp.of_bound hf.aestronglyMeasurable C
        filter_upwards [self_mem_ae_restrict isOpen_ball.measurableSet.compl,
          ae_restrict_of_ae (self_mem_ae_restrict (measurable_signedCube d))] with y hy hycube
        exact hC y ⟨fun j=>(hycube j).imp le_of_lt id,hy⟩
      simpa only [Set.piecewise_same] using hnear.piecewise isOpen_ball.measurableSet hfar

  letI : Nonempty (Fin d) := ⟨⟨0,by omega⟩⟩
  obtain ⟨c,hc,hall⟩ := RieszL1Foundation d hd s a hs hsd ha
  have hmeas := (hall 0 (by norm_num)).1
  let f := fun y : EuclideanSpace ℝ (Fin d) => RieszKernel d s a 0 (TorusLift d y)
  have hf : Measurable f := hmeas.comp (lift_signedCube_preserving d).measurable
  obtain ⟨hcont,_,b,C,hb,hC,happrox⟩ := RieszLocalStructure d hd s a hs hsd ha
  rw [memLp_signedCube_iff d _ hmeas]
  change MemLp f 2 (volume.restrict (signedCube d)) ↔ _
  rw [cube_memLp_iff_ball d f hf hcont.continuousOn]
  let μ : Measure (EuclideanSpace ℝ (Fin d)) := volume.restrict (ball 0 (1/8))
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let model := fun y : EuclideanSpace ℝ (Fin d) =>
    if s=0 then Real.log (1/‖y‖) else ‖y‖^(-s)
  have hm : Measurable model := by
    by_cases hz:s=0
    · convert! Real.measurable_log.comp
        ((measurable_const (a:=(1:ℝ))).div (continuous_norm.measurable : Measurable (fun y : EuclideanSpace ℝ (Fin d) => ‖y‖))) using 1
      simp only [model,if_pos hz,Function.comp_def,Pi.div_apply]
    · simpa only [model,if_neg hz] using continuous_norm.measurable.pow_const (-s)
  have hbound : ∀ᵐ y ∂μ, |f y-b*model y|≤C := by
    filter_upwards [self_mem_ae_restrict measurableSet_ball,
      ae_restrict_of_ae ((volume : Measure (EuclideanSpace ℝ (Fin d))).ae_ne 0)] with y hy hy0
    have hnpos : 0<‖y‖ := norm_pos_iff.mpr hy0
    have hnsmall : ‖y‖<1/4 := (mem_ball_zero_iff.mp hy).trans (by norm_num)
    convert! happrox y hnpos hnsmall using 1 <;> simp only [f,model,mul_ite]
    rfl
  rw [bounded_remainder_iff μ f model b C hb.ne' hf.aestronglyMeasurable
    hm.aestronglyMeasurable hbound]
  by_cases hz:s=0
  · have hm2 : MemLp model 2 μ := by
      simpa only [model,if_pos hz,μ] using log_memLp_two
        (volume : Measure (EuclideanSpace ℝ (Fin d))) (1/8) (by norm_num) (by norm_num)
    have hs2 : s<(d:ℝ)/2 := by
      have hdpos : (0:ℝ)<d := by exact_mod_cast (show 0<d by omega)
      rw [hz]
      positivity
    exact iff_of_true hm2 hs2
  · have hh := power_memLp_two_iff (volume : Measure (EuclideanSpace ℝ (Fin d)))
      s (1/8) (by norm_num)
    have hh' : MemLp (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ (-s)) 2
        (volume.restrict (ball 0 (1/8))) ↔ 2*s < (d:ℝ) := by
      simpa only [finrank_euclideanSpace_fin] using hh
    simpa only [model,if_neg hz,μ] using hh'.trans
      (by constructor <;> intro h <;> linarith : 2*s < (d:ℝ) ↔ s<(d:ℝ)/2)
