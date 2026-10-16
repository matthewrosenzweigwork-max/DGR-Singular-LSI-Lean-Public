import Tablet.UniformClosedGradientPoincare
import Tablet.UniformClosedGradientLogSobolev
import Tablet.CanonicalGradientCoreEquality
open MeasureTheory ProbabilityTheory Set
-- [TABLET NODE: UniformFullGradientInequalities]
theorem UniformFullGradientInequalities (d:ℕ)(hd:2≤d)(s a B l u:ℝ)
    (hs:0≤s)(hsd:s≤(d:ℝ)-2)(ha:0<a)(hl:0<l)(hl1:l≤1)(hu:1≤u) :
    ∃lambdaRate:ℝ,0<lambdaRate ∧
      (∀N:ℕ,2≤N→∀β:ℝ,0≤β→β≤B→∀q:BoundedBackground d l u,∀ε:ℝ,0≤ε→
        let P:=CanonicalLaw (N:=N) (RieszKernel d s a ε) q.density β
        ∀(f:Lp ℝ 2 P)(v:Lp (EuclideanSpace ℝ (Fin N×Fin d)) 2 P),
          (f,v)∈GradientGraphClosure P false→
          variance (f:Configuration d N→ℝ) P≤lambdaRate⁻¹*ClosedGradientEnergy v) ∧
      (s<(d:ℝ)/2→∃ρ:ℝ,0<ρ ∧
        ∀N:ℕ,2≤N→∀β:ℝ,0≤β→β≤B→∀q:BoundedBackground d l u,∀ε:ℝ,0≤ε→
          let P:=CanonicalLaw (N:=N) (RieszKernel d s a ε) q.density β
          ∀(f:Lp ℝ 2 P)(v:Lp (EuclideanSpace ℝ (Fin N×Fin d)) 2 P),
            (f,v)∈GradientGraphClosure P false→
            ExtendedEntropy P (fun X=>f X^2)≤ENNReal.ofReal ((2/ρ)*ClosedGradientEnergy v)) ∧
      (∀N:ℕ,2≤N→∀β:ℝ,0≤β→β≤B→∀q:BoundedBackground d l u,∀ε:ℝ,0≤ε→
        let P:=CanonicalLaw (N:=N) (RieszKernel d s a ε) q.density β
        GradientGraphClosure P false=GradientGraphClosure P true ∧
        GradientFormDomain P false=GradientFormDomain P true ∧
        ∀f:Lp ℝ 2 P,f∈GradientFormDomain P false→
          ∃!v:Lp (EuclideanSpace ℝ (Fin N×Fin d)) 2 P,(f,v)∈GradientGraphClosure P false) := by
-- BODY
  let cap:=max 0 B
  have hcap : 0≤cap := le_max_left _ _
  have hBcap : B≤cap := le_max_right _ _
  obtain ⟨lambdaRate,hlambdaRate,hPI⟩:=UniformClosedGradientPoincare d hd s a cap l u hs hsd ha hcap hl hl1 hu
  refine ⟨lambdaRate,hlambdaRate,?_,?_,?_⟩
  · intro N hN β hβ hβB q ε hε
    exact hPI N hN β hβ (hβB.trans hBcap) q ε hε
  · intro hL
    obtain ⟨ρ,hρ,hLSI⟩:=UniformClosedGradientLogSobolev d hd s a cap l u hs hsd hL ha hcap hl hl1 hu
    refine ⟨ρ,hρ,?_⟩
    intro N hN β hβ hβB q ε hε
    exact hLSI N hN β hβ (hβB.trans hBcap) q ε hε
  · intro N hN β hβ hβB q ε hε
    have hsd' : s<(d:ℝ) := by linarith
    exact CanonicalGradientCoreEquality d N hd hN s a l u β hs hsd' ha q hβ ε hε
