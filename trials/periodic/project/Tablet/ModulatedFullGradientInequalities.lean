import Tablet.ModulatedClosedGradientPoincare
import Tablet.ModulatedClosedGradientLogSobolev
open MeasureTheory ProbabilityTheory Set
-- [TABLET NODE: ModulatedFullGradientInequalities]
theorem ModulatedFullGradientInequalities (d:ℕ)(hd:2≤d)(s a B l u:ℝ)
    (hs:0≤s)(hsd:s≤(d:ℝ)-2)(ha:0<a)(hl:0<l)(hl1:l≤1)(hu:1≤u) :
    ∃lambdaRate:ℝ,0<lambdaRate ∧
      (∀N:ℕ,2≤N→∀β:ℝ,0≤β→β≤B→∀ε:ℝ,0≤ε→∀r:BoundedBackground d l u,
        let g:=RieszKernel d s a ε
        let h:=BackgroundPotential g r.density
        let J:=BackgroundPairMean g r.density
        let P:=NormalizedTilt (volume:Measure (Configuration d N))
          (fun X=>Real.exp (-β*(PairEnergy g X-(∑i:Fin N,h (X i))+(N:ℝ)*(J/2)))*ProductDensity r.density X)
        ∀(f:Lp ℝ 2 P)(v:Lp (EuclideanSpace ℝ (Fin N×Fin d)) 2 P),
          (f,v)∈GradientGraphClosure P false→
          variance (f:Configuration d N→ℝ) P≤lambdaRate⁻¹*ClosedGradientEnergy v) ∧
      (s<(d:ℝ)/2→∃ρ:ℝ,0<ρ ∧
        ∀N:ℕ,2≤N→∀β:ℝ,0≤β→β≤B→∀ε:ℝ,0≤ε→∀r:BoundedBackground d l u,
          let g:=RieszKernel d s a ε
          let h:=BackgroundPotential g r.density
          let J:=BackgroundPairMean g r.density
          let P:=NormalizedTilt (volume:Measure (Configuration d N))
            (fun X=>Real.exp (-β*(PairEnergy g X-(∑i:Fin N,h (X i))+(N:ℝ)*(J/2)))*ProductDensity r.density X)
          ∀(f:Lp ℝ 2 P)(v:Lp (EuclideanSpace ℝ (Fin N×Fin d)) 2 P),
            (f,v)∈GradientGraphClosure P false→
            ExtendedEntropy P (fun X=>f X^2)≤ENNReal.ofReal ((2/ρ)*ClosedGradientEnergy v)) ∧
      (∀N:ℕ,2≤N→∀β:ℝ,0≤β→β≤B→∀ε:ℝ,0≤ε→∀r:BoundedBackground d l u,
        let g:=RieszKernel d s a ε
        let h:=BackgroundPotential g r.density
        let J:=BackgroundPairMean g r.density
        let P:=NormalizedTilt (volume:Measure (Configuration d N))
          (fun X=>Real.exp (-β*(PairEnergy g X-(∑i:Fin N,h (X i))+(N:ℝ)*(J/2)))*ProductDensity r.density X)
        GradientGraphClosure P false=GradientGraphClosure P true ∧
        GradientFormDomain P false=GradientFormDomain P true ∧
        ∀f:Lp ℝ 2 P,f∈GradientFormDomain P false→
          ∃!v:Lp (EuclideanSpace ℝ (Fin N×Fin d)) 2 P,(f,v)∈GradientGraphClosure P false) :=by
-- BODY
  let cap:=max 0 B
  have hcap:0≤cap:=le_max_left _ _
  have hBcap:B≤cap:=le_max_right _ _
  obtain ⟨lambdaRate,hlambdaRate,hPI⟩:=ModulatedClosedGradientPoincare d hd s a cap l u
    hs hsd ha hcap hl hl1 hu
  refine ⟨lambdaRate,hlambdaRate,?_,?_,?_⟩
  · intro N hN β hβ hβB ε hε r
    exact (hPI N hN β hβ (hβB.trans hBcap) ε hε r).2.2.2
  · intro hHS
    obtain ⟨ρ,hρ,hLSI⟩:=ModulatedClosedGradientLogSobolev d hd s a cap l u
      hs hsd hHS ha hcap hl hl1 hu
    refine ⟨ρ,hρ,?_⟩
    intro N hN β hβ hβB ε hε r
    exact hLSI N hN β hβ (hβB.trans hBcap) ε hε r
  · intro N hN β hβ hβB ε hε r
    have h:=hPI N hN β hβ (hβB.trans hBcap) ε hε r
    exact ⟨h.1,h.2.1,h.2.2.1⟩
