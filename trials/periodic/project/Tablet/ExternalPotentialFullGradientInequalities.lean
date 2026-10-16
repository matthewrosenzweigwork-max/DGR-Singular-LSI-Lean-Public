import Tablet.ExternalPotentialClosedGradientPoincare
import Tablet.ExternalPotentialClosedGradientLogSobolev
open MeasureTheory ProbabilityTheory Set
-- [TABLET NODE: ExternalPotentialFullGradientInequalities]
theorem ExternalPotentialFullGradientInequalities (d : ℕ) (hd : 2≤d) (s a B L : ℝ)
    (hs : 0≤s) (hsd : s≤(d:ℝ)-2) (ha : 0<a) (hL : 0≤L) :
    (∃ rate : ℝ, 0 < rate ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ β : ℝ, 0 ≤ β → β ≤ B → ∀ ε : ℝ, 0 ≤ ε →
      ∀ A : ℝ, ∀ V : UnitAddTorus (Fin d) → ℝ, Measurable V →
      (∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), A ≤ V x ∧ V x ≤ A+L) →
      let P := NormalizedTilt (volume : Measure (Configuration d N))
        (fun X => Real.exp (-β*(∑ i : Fin N, V (X i))-β*PairEnergy (RieszKernel d s a ε) X))
      GradientGraphClosure P false = GradientGraphClosure P true ∧
      GradientFormDomain P false = GradientFormDomain P true ∧
      (∀ f : Lp ℝ 2 P, f ∈ GradientFormDomain P false →
        ∃! v : Lp (EuclideanSpace ℝ (Fin N×Fin d)) 2 P,
          (f,v) ∈ GradientGraphClosure P false) ∧
      (∀ (f : Lp ℝ 2 P) (v : Lp (EuclideanSpace ℝ (Fin N×Fin d)) 2 P),
        (f,v) ∈ GradientGraphClosure P false →
        variance (f : Configuration d N → ℝ) P ≤ rate⁻¹*ClosedGradientEnergy v)) ∧
    (s<(d:ℝ)/2 → ∃ rate : ℝ, 0 < rate ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ β : ℝ, 0 ≤ β → β ≤ B → ∀ ε : ℝ, 0 ≤ ε →
      ∀ A : ℝ, ∀ V : UnitAddTorus (Fin d) → ℝ, Measurable V →
      (∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), A ≤ V x ∧ V x ≤ A+L) →
      let P := NormalizedTilt (volume : Measure (Configuration d N))
        (fun X => Real.exp (-β*(∑ i : Fin N, V (X i))-β*PairEnergy (RieszKernel d s a ε) X))
      ∀ (f : Lp ℝ 2 P) (v : Lp (EuclideanSpace ℝ (Fin N×Fin d)) 2 P),
        (f,v) ∈ GradientGraphClosure P false →
        ExtendedEntropy P (fun X => f X^2) ≤ ENNReal.ofReal ((2/rate)*ClosedGradientEnergy v)) := by
-- BODY
  have hcap : 0≤max 0 B := le_max_left _ _
  have hBcap : B≤max 0 B := le_max_right _ _
  constructor
  · obtain ⟨rate,hrate,hPI⟩ := ExternalPotentialClosedGradientPoincare d hd s a (max 0 B) L hs hsd ha hcap hL
    refine ⟨rate,hrate,?_⟩
    intro N hN β hβ hβB ε hε A V hV hbounds
    exact hPI N hN β hβ (hβB.trans hBcap) ε hε A V hV hbounds
  · intro hHS
    obtain ⟨rate,hrate,hLSI⟩ := ExternalPotentialClosedGradientLogSobolev d hd s a (max 0 B) L hs hsd hHS ha hcap hL
    refine ⟨rate,hrate,?_⟩
    intro N hN β hβ hβB ε hε A V hV hbounds
    exact hLSI N hN β hβ (hβB.trans hBcap) ε hε A V hV hbounds
