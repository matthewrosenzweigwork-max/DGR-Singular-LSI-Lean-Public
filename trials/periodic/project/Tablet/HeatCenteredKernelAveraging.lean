module

public import Tablet.HeatDoubleIncrementAveraging
public import Tablet.HeatBoundedCenteredBackgroundIdentity

@[expose] public section
open MeasureTheory
-- [TABLET NODE: HeatCenteredKernelAveraging]
theorem HeatCenteredKernelAveraging (d : ℕ) (t : ℝ) (ht : 0<t)
    (r : UnitAddTorus (Fin d)→ℝ) (M : ℝ) (hM : 1≤M) (hr : Measurable r)
    (hrb : ∀ᵐx∂(volume : Measure (UnitAddTorus (Fin d))),0≤r x∧r x≤M)
    (hrmass : ∫x,r x∂volume=1) (g : UnitAddTorus (Fin d)→ℝ)
    (hg : Measurable g) (hgi : Integrable g volume) (c : ℝ) (hc : 0≤c) (hgl : ∀x,-c≤g x) :
    let r':=HeatSemigroup d t r
    ∀x y, Integrable (fun p:UnitAddTorus (Fin d)×UnitAddTorus (Fin d)=>CenteredKernel g r' (x+p.1) (y+p.2))
      ((HeatIncrementLaw d t).prod (HeatIncrementLaw d t)) ∧
    (∫p,CenteredKernel g r' (x+p.1) (y+p.2)∂(HeatIncrementLaw d t).prod (HeatIncrementLaw d t))=
      CenteredKernel (HeatSemigroup d (t+t) g) r x y := by
-- BODY
  haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp; infer_instance
  haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := inferInstance
  let T:=UnitAddTorus (Fin d)
  let ν:=HeatIncrementLaw d t
  haveI : IsProbabilityMeasure ν := (HeatIncrementAveraging d t ht).1
  have hrn : ∀ᵐx∂(volume : Measure T),‖r x‖≤M :=by
    filter_upwards [hrb] with x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2
  have hri : Integrable r volume := Integrable.of_bound hr.aestronglyMeasurable M hrn
  have hP:=HeatOperatorBounds d t ht r hr hri
  let r':T→ℝ:=HeatSemigroup d t r
  have hr'b:∀ᵐx∂(volume : Measure T),0≤r' x∧r' x≤M:=
    Filter.Eventually.of_forall (hP.2.2.2.2.1 0 M hrb)
  have hr'mass : ∫x,r' x∂volume=1:=hP.2.2.1.trans hrmass
  have hB:=CenteredKernelBounds d g r' hg hgi hP.1 M c hM hc hr'b hr'mass hgl
  have hBi : Integrable (BackgroundPotential g r') volume :=by
    apply Integrable.of_bound hB.1.aestronglyMeasurable (M*∫x,|g x|∂volume)
    exact Filter.Eventually.of_forall fun x=>by simpa only [Real.norm_eq_abs] using (hB.2.1 x).2
  have hcenter:=HeatBoundedCenteredBackgroundIdentity d t ht r M hM hr hrb hrmass g hg hgi c hc hgl
  dsimp only
  intro x y
  have hpair:=HeatDoubleIncrementAveraging d t ht g hg hgi x y
  have hbx:=((HeatIncrementAveraging d t ht).2 _ hBi x).1
  have hby:=((HeatIncrementAveraging d t ht).2 _ hBi y).1
  have hxf:Integrable (fun p:T×T=>BackgroundPotential g r' (x+p.1)) (ν.prod ν):=hbx.1.comp_fst ν
  have hyf:Integrable (fun p:T×T=>BackgroundPotential g r' (y+p.2)) (ν.prod ν):=hby.1.comp_snd ν
  have hconst:Integrable (fun _:T×T=>BackgroundPairMean g r') (ν.prod ν):=integrable_const _
  have hiK : Integrable (fun p:T×T=>CenteredKernel g r' (x+p.1) (y+p.2)) (ν.prod ν):=
    ((hpair.1.sub hxf).sub hyf).add hconst
  refine ⟨hiK,?_⟩
  unfold CenteredKernel
  change (∫p:T×T,g ((x+p.1)-(y+p.2))-BackgroundPotential g r' (x+p.1)-BackgroundPotential g r' (y+p.2)+BackgroundPairMean g r'∂ν.prod ν)=_
  have hadd:=integral_add ((hpair.1.sub hxf).sub hyf) hconst
  have hsub2:=integral_sub (hpair.1.sub hxf) hyf
  have hsub1:=integral_sub hpair.1 hxf
  dsimp only [Pi.add_apply,Pi.sub_apply] at hadd hsub2 hsub1
  rw [hadd,hsub2,hsub1,hpair.2]
  rw [integral_fun_fst (fun z:T=>BackgroundPotential g r' (x+z)),
    integral_fun_snd (fun z:T=>BackgroundPotential g r' (y+z)),integral_const]
  simp only [Measure.real,measure_univ,ENNReal.toReal_one,one_smul]
  rw [hbx.2,hby.2,hcenter.1 x,hcenter.1 y,hcenter.2]
