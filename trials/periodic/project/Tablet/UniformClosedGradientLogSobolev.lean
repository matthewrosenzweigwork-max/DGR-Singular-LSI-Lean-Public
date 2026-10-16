module

public import Tablet.UniformRegularizedLogSobolev
public import Tablet.CanonicalCutoffConvergence
public import Tablet.Entropy
public import Tablet.EntropyExtension
public import Tablet.SmoothCore
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Tablet.UniformSmoothPoincare
public import Tablet.GradientClosureInequalityExtension

@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff
-- [TABLET NODE: UniformClosedGradientLogSobolev]
theorem UniformClosedGradientLogSobolev (d:ℕ)(hd:2≤d)(s a B l u:ℝ)
    (hs:0≤s)(hsd:s≤(d:ℝ)-2)(hL:s<(d:ℝ)/2)(ha:0<a)(hB:0≤B)(hl:0<l)(hl1:l≤1)(hu:1≤u) :
    ∃rate:ℝ,0<rate ∧ ∀N:ℕ,2≤N→∀β:ℝ,0≤β→β≤B→
      ∀q:BoundedBackground d l u,∀ε:ℝ,0≤ε→
      let P:=CanonicalLaw (N:=N) (RieszKernel d s a ε) q.density β
      ∀(f:Lp ℝ 2 P)(v:Lp (EuclideanSpace ℝ (Fin N×Fin d)) 2 P),
        (f,v)∈GradientGraphClosure P false →
        ExtendedEntropy P (fun X=>f X^2)≤ENNReal.ofReal ((2/rate)*ClosedGradientEnergy v) := by
-- BODY
  have canonical_smooth_entropy_convergence (d N:ℕ) (hd:2≤d) (hN:2≤N)
      (s a l u β:ℝ) (hs:0≤s) (hsd:s<(d:ℝ)) (ha:0<a)
      (q:BoundedBackground d l u) (hβ:0≤β)
      (f:Configuration d N→ℝ) (hf:f∈SmoothCore d N) :
      Tendsto (fun ε=>Entropy (CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β) (fun X=>f X^2))
        (𝓝[>] 0) (𝓝 (Entropy (CanonicalLaw (N := N) (RieszKernel d s a 0) q.density β) (fun X=>f X^2))) := by
    have hq:IsOpenQuotientMap (ConfigurationLift d N):=by
      have hc:IsOpenQuotientMap ((↑):ℝ→AddCircle (1:ℝ)):=QuotientAddGroup.isOpenQuotientMap_mk
      have hp:=IsOpenQuotientMap.piMap (fun _:Fin N×Fin d=>hc)
      have he:=(PiLp.homeomorph 2 (fun _:Fin N×Fin d=>ℝ)).isOpenQuotientMap
      exact (Homeomorph.piCurry (X:=Fin N) (Y:=Fin d) (Z:=AddCircle (1:ℝ))).isOpenQuotientMap.comp (hp.comp he)
    have hc:Continuous f:=hq.continuous_comp_iff.mp
      (show ContDiff ℝ ∞ (fun y=>f (ConfigurationLift d N y)) from hf).continuous
    have bounded (h:Configuration d N→ℝ) (hh:Continuous h):∃C:ℝ,∀X,|h X|≤C:=by
      obtain ⟨X0,hX0,hmax⟩:=isCompact_univ.exists_isMaxOn Set.univ_nonempty hh.abs.continuousOn
      exact ⟨|h X0|,fun X=>hmax (mem_univ X)⟩
    have hw:=(CanonicalCutoffConvergence d N hd hN s a l u β hs hsd ha q hβ).2.2.2
    have hsquare:=hw (fun X=>f X^2) (hc.pow 2).measurable (bounded _ (hc.pow 2))
    have hlog:=Real.continuous_mul_log.comp (hc.pow 2)
    have hlogged:=hw (fun X=>f X^2*Real.log (f X^2)) hlog.measurable (bounded _ hlog)
    exact hlogged.sub (Real.continuous_mul_log.continuousAt.tendsto.comp hsquare)
  
  have smooth_extended_entropy_value {d N:ℕ} (P:Measure (Configuration d N))
      [IsProbabilityMeasure P] (f:Configuration d N→ℝ) (hf:f∈SmoothCore d N) :
      ExtendedEntropy P (fun X=>f X^2)=ENNReal.ofReal (Entropy P (fun X=>f X^2)) := by
    have hq:IsOpenQuotientMap (ConfigurationLift d N):=by
      have hc:IsOpenQuotientMap ((↑):ℝ→AddCircle (1:ℝ)):=QuotientAddGroup.isOpenQuotientMap_mk
      have hp:=IsOpenQuotientMap.piMap (fun _:Fin N×Fin d=>hc)
      have he:=(PiLp.homeomorph 2 (fun _:Fin N×Fin d=>ℝ)).isOpenQuotientMap
      exact (Homeomorph.piCurry (X:=Fin N) (Y:=Fin d) (Z:=AddCircle (1:ℝ))).isOpenQuotientMap.comp (hp.comp he)
    have hc:Continuous f:=hq.continuous_comp_iff.mp
      (show ContDiff ℝ ∞ (fun y=>f (ConfigurationLift d N y)) from hf).continuous
    have hi:Integrable (fun X=>f X^2) P:=(hc.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hlog:Integrable (fun X=>f X^2*Real.log (f X^2)) P:=
      (Real.continuous_mul_log.comp (hc.pow 2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    exact (EntropyExtension P _ (hc.pow 2).measurable (Eventually.of_forall fun X=>sq_nonneg (f X)) hi).2 hlog
  have close_regularized_log_sobolev (d:ℕ)(hd:2≤d)(s a B l u:ℝ)
      (hs:0≤s)(hsd:s≤(d:ℝ)-2)(ha:0<a)(hB:0≤B)(hl:0<l)(hl1:l≤1)(hu:1≤u)
      (hglobal:∃rate:ℝ,0<rate ∧ ∀N:ℕ,2≤N→∀β:ℝ,0≤β→β≤B→
        ∀q:BoundedBackground d l u,∀ε:ℝ,0<ε→∀f:Configuration d N→ℝ,f∈SmoothCore d N→
        Entropy (CanonicalLaw (N:=N) (RieszKernel d s a ε) q.density β) (fun X=>f X^2)≤
          (2/rate)*PhysicalEnergy (CanonicalLaw (N:=N) (RieszKernel d s a ε) q.density β) f) :
      ∃rate:ℝ,0<rate ∧ ∀N:ℕ,2≤N→∀β:ℝ,0≤β→β≤B→
        ∀q:BoundedBackground d l u,∀ε:ℝ,0≤ε→
        let P:=CanonicalLaw (N:=N) (RieszKernel d s a ε) q.density β
        ∀(f:Lp ℝ 2 P)(v:Lp (EuclideanSpace ℝ (Fin N×Fin d)) 2 P),
          (f,v)∈GradientGraphClosure P false →
          ExtendedEntropy P (fun X=>f X^2)≤ENNReal.ofReal ((2/rate)*ClosedGradientEnergy v) := by
    obtain ⟨rate,hrate,hreg⟩:=hglobal
    obtain ⟨rpi,hrpi,hpi⟩:=UniformSmoothPoincare d hd s a B l u hs hsd ha hB hl hl1 hu
    refine ⟨rate,hrate,?_⟩
    intro N hN β hβ hβB q ε hε
    dsimp only
    let P:=CanonicalLaw (N:=N) (RieszKernel d s a ε) q.density β
    have hsd':s<(d:ℝ):=by linarith
    have hconv:=CanonicalCutoffConvergence d N hd hN s a l u β hs hsd' ha q hβ
    letI:IsProbabilityMeasure P:=hconv.1 ε hε
    have hsmooth:∀g:Configuration d N→ℝ,g∈SmoothCore d N→
        Entropy P (fun X=>g X^2)≤(2/rate)*PhysicalEnergy P g := by
      intro g hg
      by_cases he:ε=0
      · subst ε
        have hEnt:=canonical_smooth_entropy_convergence d N hd hN s a l u β hs hsd' ha q hβ g hg
        have hc:=(ConfigurationCalculus d N).2.2.2 g hg
        obtain ⟨D,hD⟩:=hc.2.2.2.2.1
        have hE:=hconv.2.2.2 (fun X=>‖CoordinateGradient g X‖^2) hc.2.2.2.1
          ⟨D,fun X=>by simpa only [abs_of_nonneg (sq_nonneg ‖CoordinateGradient g X‖)] using hD X⟩
        apply le_of_tendsto_of_tendsto hEnt (hE.const_mul (2/rate))
        filter_upwards [self_mem_nhdsWithin] with δ hδ
        exact hreg N hN β hβ hβB q δ hδ g hg
      · exact hreg N hN β hβ hβB q ε (lt_of_le_of_ne hε (Ne.symm he)) g hg
    intro f v hfv
    apply (GradientClosureInequalityExtension d N P rpi⁻¹ (2/rate) _ _ f v hfv).2
    · intro g hg _ _
      exact hpi N hN β hβ hβB q ε hε g hg
    · intro g hg _ _
      rw [smooth_extended_entropy_value P g hg]
      exact ENNReal.ofReal_le_ofReal (hsmooth g hg)
  exact close_regularized_log_sobolev d hd s a B l u hs hsd ha hB hl hl1 hu
    (UniformRegularizedLogSobolev d hd s a B l u hs hsd hL ha hB hl hl1 hu)
