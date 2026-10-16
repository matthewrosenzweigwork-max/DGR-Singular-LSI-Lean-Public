import Tablet.UniformClosedGradientPoincare
import Tablet.CanonicalGradientCoreEquality
import Tablet.ExternalPotentialBackground
import Tablet.ExternalPotentialLawRewrite
open MeasureTheory ProbabilityTheory Set
-- [TABLET NODE: ExternalPotentialClosedGradientPoincare]
theorem ExternalPotentialClosedGradientPoincare (d : ℕ) (hd : 2 ≤ d) (s a B L : ℝ)
    (hs : 0 ≤ s) (hsd : s ≤ (d : ℝ)-2) (ha : 0 < a)
    (hB : 0 ≤ B) (hL : 0 ≤ L) :
    ∃ rate : ℝ, 0 < rate ∧ ∀ N : ℕ, 2 ≤ N →
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
        variance (f : Configuration d N → ℝ) P ≤ rate⁻¹*ClosedGradientEnergy v) := by
-- BODY
  have hlo : 0 < Real.exp (-B*L) := Real.exp_pos _
  have hlo1 : Real.exp (-B*L) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hhi1 : 1 ≤ Real.exp (B*L) := Real.one_le_exp_iff.mpr (mul_nonneg hB hL)
  obtain ⟨rate,hrate,hPI⟩ := UniformClosedGradientPoincare d hd s a B
    (Real.exp (-B*L)) (Real.exp (B*L)) hs hsd ha hB hlo hlo1 hhi1
  refine ⟨rate,hrate,?_⟩
  intro N hN β hβ hβB ε hε A V hV hbounds
  obtain ⟨hZ,q,hq⟩ := ExternalPotentialBackground d V hV A L B β hL hB hβ hβB hbounds
  have heq := ExternalPotentialLawRewrite d N (RieszKernel d s a ε) V β
    (∫ y, Real.exp (-β*V y)) hZ
  have hqd : q.density = (fun x => Real.exp (-β*V x)/(∫ y, Real.exp (-β*V y))) := funext hq
  rw [← hqd] at heq
  dsimp only
  rw [heq]
  have hsd' : s < (d : ℝ) := by linarith
  exact ⟨(CanonicalGradientCoreEquality d N hd hN s a _ _ β hs hsd' ha q hβ ε hε).1,
    (CanonicalGradientCoreEquality d N hd hN s a _ _ β hs hsd' ha q hβ ε hε).2.1,
    (CanonicalGradientCoreEquality d N hd hN s a _ _ β hs hsd' ha q hβ ε hε).2.2,
    hPI N hN β hβ hβB q ε hε⟩
