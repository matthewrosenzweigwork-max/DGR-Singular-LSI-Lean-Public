import Tablet.EntropyFiniteCentering
import Tablet.TorusDefectiveLogSobolev
import Tablet.TorusHaarPoincare
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Analysis.Calculus.ContDiff.WithLp
open MeasureTheory
open scoped ContDiff
-- [TABLET NODE: TorusHaarLogSobolev]
theorem TorusHaarLogSobolev (d:ℕ) (hd:0<d) :
    ∃ C:ℝ,0<C ∧ ∀f:UnitAddTorus (Fin d)→ℝ,TorusSmooth f→
      Entropy (volume : Measure (UnitAddTorus (Fin d))) (fun x=>f x^2) ≤
        C*(∫ x,‖TorusGradient f x‖^2) := by
-- BODY
  obtain ⟨C,hC,hdef⟩:=TorusDefectiveLogSobolev d hd
  refine ⟨32*C+48,by linarith,?_⟩
  intro f hf
  haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1:ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simpa using (inferInstance : IsProbabilityMeasure AddCircle.haarAddCircle)
  haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin d=>
      (volume : Measure (AddCircle (1:ℝ))))))
  let a:=∫x,f x
  let g:=fun x=>f x-a
  have hg:TorusSmooth g:=hf.sub contDiff_const
  have quotient : IsOpenQuotientMap (TorusLift d) := by
    have hc : IsOpenQuotientMap ((↑) : ℝ → AddCircle (1:ℝ)) :=
      QuotientAddGroup.isOpenQuotientMap_mk
    have hpi:=IsOpenQuotientMap.piMap (fun _ : Fin d=>hc)
    exact hpi.comp (PiLp.homeomorph 2 (fun _ : Fin d=>ℝ)).isOpenQuotientMap
  have hgc:Continuous g:=quotient.continuous_comp_iff.mp hg.continuous
  have hgb:∃B:ℝ,∀ᵐ x∂(volume:Measure (UnitAddTorus (Fin d))),|g x|≤B:=by
    obtain ⟨B,hB⟩:=isCompact_univ.bddAbove_image (f:=fun x=>‖g x‖) hgc.norm.continuousOn
    refine ⟨B,Filter.Eventually.of_forall fun x=>?_⟩
    exact hB (Set.mem_image_of_mem _ (Set.mem_univ x))
  have hcen:=EntropyFiniteCentering volume g hgc.measurable hgb a
  have hfun : (fun x=>(g x+a)^2)=(fun x=>f x^2):=by funext x;dsimp [g];ring
  rw [hfun] at hcen
  have hgrad:TorusGradient g=TorusGradient f:=by
    funext x
    unfold TorusGradient
    simp [g,fderiv_sub_const]
  have hpi: (∫ x,g x^2) ≤ ∫ x,‖TorusGradient f x‖^2 :=
    (TorusHaarPoincare d hd).1 f hf
  have hdg:=hdef g hg
  rw [hgrad] at hdg
  have henergy : 0≤∫ x,‖TorusGradient f x‖^2:=integral_nonneg fun x=>sq_nonneg _
  nlinarith
