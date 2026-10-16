module

public import Collective140

@[expose] public section
set_option autoImplicit false
open MeasureTheory

example (B : ℝ) (hB : 0 ≤ B) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ N : ℕ, 2 ≤ N → ∀ coupling ε : ℝ,
      0 ≤ coupling → coupling ≤ B → 0 ≤ ε →
      ∀ q ∈ ClosedGradientGraph
        (GibbsLaw (N:=N) (ProbabilityTheory.stdGaussian (OneParticle 4)) 2 coupling ε),
        ρ * LawVariance
          (GibbsLaw (N:=N) (ProbabilityTheory.stdGaussian (OneParticle 4)) 2 coupling ε) q.1
          ≤ ClosedPhysicalEnergy q := by
  exact (WholeSpaceCollective.allCutoffs 4 (by norm_num) 2 B
    (by norm_num) (by norm_num) hB).2.2.2

example (B : ℝ) (hB : 0 ≤ B) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ V : OneParticle 3 → ℝ, TwoSidedPotential 3 1 2 V →
      ∀ b : OneParticle 3 → ℝ, BoundedMultiplier 3 2 b →
      ∀ N : ℕ, 2 ≤ N → ∀ coupling ε : ℝ,
        0 ≤ coupling → coupling ≤ B → 0 ≤ ε →
      ∀ q ∈ ClosedGradientGraph
        (GibbsLaw (N:=N) (ReferenceLaw V b) (1/2) coupling ε),
        ρ * LawVariance
          (GibbsLaw (N:=N) (ReferenceLaw V b) (1/2) coupling ε) q.1
          ≤ ClosedPhysicalEnergy q := by
  exact (WholeSpaceCollective.allCutoffs 3 (by norm_num) (1/2) B
    (by norm_num) (by norm_num) hB).2.2.1 1 2 2
      (by norm_num) (by norm_num) (by norm_num)
