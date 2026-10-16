module

public import Tablet.UniformFullGradientInequalities
public import Tablet.ModulatedFullGradientInequalities
public import Tablet.ExternalPotentialFullGradientInequalities

@[expose] public section
open MeasureTheory ProbabilityTheory Set

-- These evidence-only adapters derive each concrete specialization from the actual final main.
theorem ActualFinalPoincare (d : ℕ) (hd : 2 ≤ d) (s a B l u : ℝ)
    (hs : 0 ≤ s) (hsd : s ≤ (d : ℝ)-2) (ha : 0 < a) (_hB : 0 ≤ B)
    (hl : 0 < l) (hl1 : l ≤ 1) (hu : 1 ≤ u) :
    ∃ rate : ℝ, 0 < rate ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ β : ℝ, 0 ≤ β → β ≤ B → ∀ q : BoundedBackground d l u,
      ∀ ε : ℝ, 0 ≤ ε →
      let P := CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β
      ∀ (f : Lp ℝ 2 P) (v : Lp (EuclideanSpace ℝ (Fin N × Fin d)) 2 P),
        (f,v) ∈ GradientGraphClosure P false →
        variance (f : Configuration d N → ℝ) P ≤ rate⁻¹ * ClosedGradientEnergy v := by
  obtain ⟨rate,hpos,hPI,_hLSI,_hgraph⟩ :=
    UniformFullGradientInequalities d hd s a B l u hs hsd ha hl hl1 hu
  exact ⟨rate,hpos,hPI⟩

theorem ActualFinalLogSobolev (d : ℕ) (hd : 2 ≤ d) (s a B l u : ℝ)
    (hs : 0 ≤ s) (hsd : s ≤ (d : ℝ)-2) (hHS : s < (d : ℝ)/2)
    (ha : 0 < a) (_hB : 0 ≤ B) (hl : 0 < l) (hl1 : l ≤ 1) (hu : 1 ≤ u) :
    ∃ rate : ℝ, 0 < rate ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ β : ℝ, 0 ≤ β → β ≤ B → ∀ q : BoundedBackground d l u,
      ∀ ε : ℝ, 0 ≤ ε →
      let P := CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β
      ∀ (f : Lp ℝ 2 P) (v : Lp (EuclideanSpace ℝ (Fin N × Fin d)) 2 P),
        (f,v) ∈ GradientGraphClosure P false →
        ExtendedEntropy P (fun X => f X ^ 2) ≤
          ENNReal.ofReal ((2/rate) * ClosedGradientEnergy v) := by
  obtain ⟨_rate,_hpos,_hPI,hLSI,_hgraph⟩ :=
    UniformFullGradientInequalities d hd s a B l u hs hsd ha hl hl1 hu
  exact hLSI hHS

theorem ActualFinalGraphEquality (a ε : ℝ) (ha : 0 < a) (hε : 0 ≤ ε)
    (q : BoundedBackground 2 (1/2) (3/2)) :
    let P := CanonicalLaw (N := 2) (RieszKernel 2 0 a ε) q.density 0
    GradientGraphClosure P false = GradientGraphClosure P true := by
  obtain ⟨_rate,_hpos,_hPI,_hLSI,hgraph⟩ :=
    UniformFullGradientInequalities 2 (by norm_num) 0 a 0 (1/2) (3/2)
      (by norm_num) (by norm_num) ha (by norm_num) (by norm_num) (by norm_num)
  exact (hgraph 2 (by norm_num) 0 (by norm_num) (by norm_num) q ε hε).1
