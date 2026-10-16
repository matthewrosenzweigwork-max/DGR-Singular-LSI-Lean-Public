import Tablet.ConditionalFisherAggregation
import Tablet.Entropy
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
open MeasureTheory
open scoped ContDiff
-- [TABLET NODE: ConditionalEntropyAggregation]
theorem ConditionalEntropyAggregation (d N:ℕ)(P:Measure (Configuration d N))
    [IsFiniteMeasure P] (K:Fin N→Configuration d N→Measure (UnitAddTorus (Fin d)))
    (hK:∀i X,IsProbabilityMeasure (K i X))
    (hrow:∀i:Fin N,∀F:Configuration d N→ℝ,Measurable F→
      (∃C:ℝ,∀X,|F X|≤C)→
      Integrable (fun X=>∫z,F (Replacement X i z)∂K i X) P ∧
      (∫X,∫z,F (Replacement X i z)∂K i X∂P)=(∫X,F X∂P))
    (σ:ℝ)(hσ:0<σ)
    (hLSI:∀i X,∀g:UnitAddTorus (Fin d)→ℝ,TorusSmooth g→
      Entropy (K i X) (fun z=>g z^2)≤(2/σ)*(∫z,‖TorusGradient g z‖^2∂K i X))
    (f:Configuration d N→ℝ)(hf:f∈SmoothCore d N) :
    (∀i:Fin N,Integrable (fun X=>Entropy (K i X) (fun z=>f (Replacement X i z)^2)) P) ∧
      (∑i:Fin N,∫X,Entropy (K i X) (fun z=>f (Replacement X i z)^2)∂P)≤
        (2/σ)*PhysicalEnergy P f := by
-- BODY
  classical
  have hq:IsOpenQuotientMap (ConfigurationLift d N):=by
    have hc:IsOpenQuotientMap ((↑):ℝ→AddCircle (1:ℝ)):=QuotientAddGroup.isOpenQuotientMap_mk
    have hp:=IsOpenQuotientMap.piMap (fun _:Fin N×Fin d=>hc)
    exact (Homeomorph.piCurry (X:=Fin N) (Y:=Fin d) (Z:=AddCircle (1:ℝ))).isOpenQuotientMap.comp
      (hp.comp (PiLp.homeomorph 2 (fun _:Fin N×Fin d=>ℝ)).isOpenQuotientMap)
  have cf:Continuous f:=hq.continuous_comp_iff.mp
    (show ContDiff ℝ ∞ (fun y=>f (ConfigurationLift d N y)) from hf).continuous
  have bounded {F:Configuration d N→ℝ}(cF:Continuous F):∃C:ℝ,∀X,|F X|≤C:=by
    obtain ⟨C,hC⟩:=isCompact_univ.exists_bound_of_continuousOn cF.continuousOn
    exact ⟨C,fun X=>by simpa only [Real.norm_eq_abs] using hC X (Set.mem_univ X)⟩
  obtain ⟨C,hC⟩:=bounded cf
  have cb:∀X,f X^2≤C^2:=by
    intro X
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (f X)) (hC X) 2
  have cfl:Continuous (fun X=>f X^2*Real.log (f X^2)):=
    Real.continuous_mul_log.comp (cf.pow 2)
  have hm2:=fun i=>hrow i (fun X=>f X^2) (cf.pow 2).measurable (bounded (cf.pow 2))
  have hml:=fun i=>hrow i (fun X=>f X^2*Real.log (f X^2)) cfl.measurable (bounded cfl)
  let M:=fun (i:Fin N)(X:Configuration d N)=>∫z,f (Replacement X i z)^2∂K i X
  have hMi:∀i,Integrable (M i) P:=fun i=>(hm2 i).1
  have hMb:∀i X,0≤M i X ∧ M i X≤C^2:=by
    intro i X
    haveI:=hK i X
    have hR:Continuous (fun z:UnitAddTorus (Fin d)=>Replacement X i z):=by
      apply continuous_pi
      intro j
      by_cases hj:j=i
      · subst j
        change Continuous (fun z : UnitAddTorus (Fin d) => Function.update X i z i)
        simp only [Function.update_self]
        exact continuous_id
      · simpa [Replacement,Function.update_of_ne hj] using
          (continuous_const:Continuous (fun _:UnitAddTorus (Fin d)=>X j))
    have hcR:Continuous (fun z=>f (Replacement X i z)^2):=(cf.comp hR).pow 2
    have hi:Integrable (fun z=>f (Replacement X i z)^2) (K i X):=
      hcR.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    refine ⟨integral_nonneg (fun z=>sq_nonneg _),?_⟩
    have hh:=integral_mono hi (integrable_const (C^2)) (fun z=>cb (Replacement X i z))
    simpa using hh
  have hcI : IsCompact (Set.Icc (0:ℝ) (C^2)) := isCompact_Icc
  obtain ⟨D,hD⟩:=hcI.exists_bound_of_continuousOn
    Real.continuous_mul_log.continuousOn
  have hMli:∀i,Integrable (fun X=>M i X*Real.log (M i X)) P:=by
    intro i
    apply Integrable.of_bound
      (Real.continuous_mul_log.comp_aestronglyMeasurable (hMi i).aestronglyMeasurable) D
    apply Filter.Eventually.of_forall
    intro X
    exact hD (M i X) (hMb i X)
  have hCEi:∀i,Integrable (fun X=>Entropy (K i X) (fun z=>f (Replacement X i z)^2)) P:=by
    intro i
    exact (hml i).1.sub (hMli i)
  have hFisher:=ConditionalFisherAggregation d N P K hrow f hf
  have hcalc:=(ConfigurationCalculus d N).2.2.2 f hf
  have hlocal:∀i X,Entropy (K i X) (fun z=>f (Replacement X i z)^2)≤
      (2/σ)*(∫z,‖TorusGradient (fun y=>f (Replacement X i y)) z‖^2∂K i X):=by
    intro i X
    exact hLSI i X _ (hcalc.2.2.2.2.2.2.1 X i).1
  refine ⟨hCEi,?_⟩
  calc
    (∑i:Fin N,∫X,Entropy (K i X) (fun z=>f (Replacement X i z)^2)∂P)≤
        ∑i:Fin N,(2/σ)*(∫X,∫z,‖TorusGradient (fun y=>f (Replacement X i y)) z‖^2∂K i X∂P):=by
      apply Finset.sum_le_sum
      intro i hi
      have hh:=integral_mono (hCEi i) ((hFisher.1 i).const_mul (2/σ)) (hlocal i)
      change (∫X,Entropy (K i X) (fun z=>f (Replacement X i z)^2)∂P)≤
        ∫X,(2/σ)*(∫z,‖TorusGradient (fun y=>f (Replacement X i y)) z‖^2∂K i X)∂P at hh
      rwa[integral_const_mul] at hh
    _ =(2/σ)*PhysicalEnergy P f:=by
      rw[←Finset.mul_sum,hFisher.2]
