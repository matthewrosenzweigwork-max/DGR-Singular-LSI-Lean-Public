module

public import Tablet.HeatIncrementLaw
public import Tablet.HeatKernelFacts
public import Tablet.MeasurePreservingDensityTransport
public import Tablet.BoundedJointDensityMarginal
public import Mathlib.MeasureTheory.Group.Prod

@[expose] public section
open MeasureTheory
open scoped ENNReal
-- [TABLET NODE: HeatBoundedReferencePushforward]
theorem HeatBoundedReferencePushforward (d : ℕ) (t : ℝ) (ht : 0<t)
    (r : UnitAddTorus (Fin d)→ℝ) (u : ℝ) (hu : 0≤u) (hr : Measurable r)
    (hrb : ∀ᵐx∂(volume : Measure (UnitAddTorus (Fin d))),r x∈Set.Icc 0 u) :
    Measure.map (fun p : UnitAddTorus (Fin d) × UnitAddTorus (Fin d) => p.1+p.2)
      (((volume : Measure (UnitAddTorus (Fin d))).withDensity (fun x=>ENNReal.ofReal (r x))).prod (HeatIncrementLaw d t)) =
      (volume : Measure (UnitAddTorus (Fin d))).withDensity (fun x=>ENNReal.ofReal (HeatSemigroup d t r x)) := by
-- BODY
  haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp; infer_instance
  haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := inferInstance
  let T:=UnitAddTorus (Fin d)
  let m:Measure T:=volume
  let S:T×T→T×T:=fun p=>(p.1+p.2,p.2)
  let v:T×T→ℝ:=fun p=>r (p.1-p.2)*HeatKernel d t p.2
  let ρ:T×T→ℝ≥0∞:=fun p=>ENNReal.ofReal (r (p.1-p.2))*ENNReal.ofReal (HeatKernel d t p.2)
  have hS:MeasurePreserving S (m.prod m) (m.prod m):=measurePreserving_add_prod m m
  have hp:Continuous (HeatKernel d t):=(HeatKernelFacts d t ht).1
  have hpn:= (HeatKernelFacts d t ht).2.1
  have hv:Measurable v := (hr.comp (measurable_fst.sub measurable_snd)).mul (hp.measurable.comp measurable_snd)
  have hρ:Measurable ρ:=((hr.comp (measurable_fst.sub measurable_snd)).ennreal_ofReal).mul ((hp.measurable.comp measurable_snd).ennreal_ofReal)
  have htransport:=MeasurePreservingDensityTransport (m.prod m) (m.prod m) S hS ρ hρ
  have he : ρ ∘ S=fun p:T×T=>ENNReal.ofReal (r p.1)*ENNReal.ofReal (HeatKernel d t p.2) := by
    funext p
    simp [ρ,S]
  rw [he] at htransport
  have hprod : (m.withDensity (fun x=>ENNReal.ofReal (r x))).prod (HeatIncrementLaw d t)=
      (m.prod m).withDensity (fun p=>ENNReal.ofReal (r p.1)*ENNReal.ofReal (HeatKernel d t p.2)) := by
    exact prod_withDensity hr.ennreal_ofReal hp.measurable.ennreal_ofReal
  have hrd:∀ᵐp∂m.prod m,r (p.1-p.2)∈Set.Icc 0 u :=
    (quasiMeasurePreserving_sub_of_right_invariant m m).ae hrb
  obtain ⟨C,hC⟩ := (isCompact_univ:IsCompact (Set.univ:Set T)).exists_bound_of_continuousOn hp.continuousOn
  have hCp:0≤C:=le_trans (norm_nonneg (HeatKernel d t (0:T))) (hC 0 (Set.mem_univ _))
  have hvb:∀ᵐp∂m.prod m,v p∈Set.Icc 0 (u*C) := by
    filter_upwards [hrd] with p hp'
    have hrn:0≤r (p.1-p.2):=hp'.1
    have hpb:HeatKernel d t p.2≤C:=le_trans (le_abs_self _) (hC p.2 (Set.mem_univ _))
    exact ⟨mul_nonneg hrn (hpn _),mul_le_mul hp'.2 hpb (hpn _) hu⟩
  have hrhov:ρ=ᵐ[m.prod m] fun p=>ENNReal.ofReal (v p):=by
    filter_upwards [hrd] with p hp'
    exact (ENNReal.ofReal_mul (hp'.1)).symm
  have hmarg:=BoundedJointDensityMarginal m m v (u*C)
    (mul_nonneg hu hCp) hv hvb
  have hinner: (fun x=>∫y,v (x,y)∂m)=HeatSemigroup d t r :=by
    funext x
    unfold HeatSemigroup
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y=>mul_comm _ _
  have hmap : Measure.map (fun p:T×T=>p.1+p.2) ((m.withDensity (fun x=>ENNReal.ofReal (r x))).prod (HeatIncrementLaw d t))=
      ((m.prod m).withDensity ρ).fst :=by
    rw [hprod,←htransport]
    unfold Measure.fst
    rw [Measure.map_map measurable_fst hS.measurable]
    rfl
  rw [hmap,withDensity_congr_ae hrhov,hmarg]
  congr 1
  funext x
  rw [congrFun hinner x]
