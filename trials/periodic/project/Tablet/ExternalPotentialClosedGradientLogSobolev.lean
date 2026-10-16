module

public import Tablet.UniformClosedGradientPoincare
public import Tablet.UniformClosedGradientLogSobolev
public import Tablet.CanonicalGradientCoreEquality
public import Tablet.ExternalPotentialBackground
public import Tablet.ExternalPotentialLawRewrite

@[expose] public section
open MeasureTheory ProbabilityTheory Set
-- [TABLET NODE: ExternalPotentialClosedGradientLogSobolev]
theorem ExternalPotentialClosedGradientLogSobolev (d : ℕ) (hd : 2 ≤ d) (s a B L : ℝ)
    (hs : 0 ≤ s) (hsd : s ≤ (d : ℝ)-2) (hHS : s < (d : ℝ)/2)
    (ha : 0 < a) (hB : 0 ≤ B) (hL : 0 ≤ L) :
    ∃ rate : ℝ, 0 < rate ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ β : ℝ, 0 ≤ β → β ≤ B → ∀ ε : ℝ, 0 ≤ ε →
      ∀ A : ℝ, ∀ V : UnitAddTorus (Fin d) → ℝ, Measurable V →
      (∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), A ≤ V x ∧ V x ≤ A+L) →
      let P := NormalizedTilt (volume : Measure (Configuration d N))
        (fun X => Real.exp (-β*(∑ i : Fin N, V (X i))-β*PairEnergy (RieszKernel d s a ε) X))
      ∀ (f : Lp ℝ 2 P) (v : Lp (EuclideanSpace ℝ (Fin N×Fin d)) 2 P),
        (f,v) ∈ GradientGraphClosure P false →
        ExtendedEntropy P (fun X => f X^2) ≤ ENNReal.ofReal ((2/rate)*ClosedGradientEnergy v) := by
-- BODY
  have hlo : 0 < Real.exp (-B*L) := Real.exp_pos _
  have hlo1 : Real.exp (-B*L) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hhi1 : 1 ≤ Real.exp (B*L) := Real.one_le_exp_iff.mpr (mul_nonneg hB hL)
  obtain ⟨rate,hrate,hLSI⟩ := UniformClosedGradientLogSobolev d hd s a B
    (Real.exp (-B*L)) (Real.exp (B*L)) hs hsd hHS ha hB hlo hlo1 hhi1
  refine ⟨rate,hrate,?_⟩
  intro N hN β hβ hβB ε hε A V hV hbounds
  obtain ⟨hZ,q,hq⟩ := ExternalPotentialBackground d V hV A L B β hL hB hβ hβB hbounds
  have heq := ExternalPotentialLawRewrite d N (RieszKernel d s a ε) V β
    (∫ y, Real.exp (-β*V y)) hZ
  have hqd : q.density = (fun x => Real.exp (-β*V x)/(∫ y, Real.exp (-β*V y))) := funext hq
  rw [← hqd] at heq
  dsimp only
  rw [heq]
  exact hLSI N hN β hβ hβB q ε hε
