module

public import Tablet.HeatCenteredPartitionComparison
public import Tablet.RieszL1Foundation

@[expose] public section
open MeasureTheory
-- [TABLET NODE: RieszCenteredHeatPartitionComparison]
theorem RieszCenteredHeatPartitionComparison (d N : ℕ) (hd : 2≤d)
    (s a ε β M : ℝ) (hs : 0≤s) (hsd : s<(d:ℝ)) (ha : 0<a)
    (hε : 0≤ε) (hβ : 0≤β) (hM : 1≤M) (r : UnitAddTorus (Fin d)→ℝ)
    (hr : Measurable r) (hrb : ∀ᵐx∂(volume : Measure (UnitAddTorus (Fin d))),0≤r x∧r x≤M)
    (hrmass : ∫x,r x∂volume=1) :
    let rε := if ε=0 then r else HeatSemigroup d (ε/2) r
    Measurable rε ∧ Integrable rε volume ∧
    (∀ᵐx∂(volume : Measure (UnitAddTorus (Fin d))),0≤rε x∧rε x≤M) ∧
    (∫x,rε x∂volume)=1 ∧
    CenteredPartition (N:=N) (RieszKernel d s a ε) r β ≤
      CenteredPartition (N:=N) (RieszKernel d s a 0) rε β := by
-- BODY
  haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=by
    rw [AddCircle.volume_eq_smul_haarAddCircle];simp;infer_instance
  haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) :=inferInstance
  have hrNorm:∀ᵐx∂(volume : Measure (UnitAddTorus (Fin d))),‖r x‖≤M:=by
    filter_upwards [hrb] with x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2
  have hri:Integrable r volume:=Integrable.of_bound hr.aestronglyMeasurable M hrNorm
  by_cases hz:ε=0
  · simp only [hz,if_pos rfl]
    exact ⟨hr,hri,hrb,hrmass,le_rfl⟩
  · have hp:0<ε/2:=by positivity
    simp only [if_neg hz]
    have hP:=HeatOperatorBounds d (ε/2) hp r hr hri
    refine ⟨hP.1,hP.2.1,Filter.Eventually.of_forall (hP.2.2.2.2.1 0 M hrb),hP.2.2.1.trans hrmass,?_⟩
    obtain ⟨c,hc,hg⟩:=RieszL1Foundation d hd s a hs hsd ha
    have hg0:=hg 0 le_rfl
    have hheat:(RieszKernel d s a ε)=HeatSemigroup d (ε/2+ε/2) (RieszKernel d s a 0):=by
      rw [show ε/2+ε/2=ε by ring]
      exact funext ((hg ε hε).2.2.2.2.2.2 (lt_of_le_of_ne hε (Ne.symm hz)))
    rw [hheat]
    exact HeatCenteredPartitionComparison d N (ε/2) hp r M hM hr hrb hrmass
      (RieszKernel d s a 0) hg0.1 hg0.2.1 c hc hg0.2.2.2.2.1 β hβ
