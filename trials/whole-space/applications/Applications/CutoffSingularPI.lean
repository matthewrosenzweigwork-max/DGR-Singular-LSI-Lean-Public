module

public import Collective140
public import Tablet.QuadraticGaussianClass
public import Tablet.QuadraticGaussianReference

@[expose] public section
open MeasureTheory
open scoped ENNReal ContDiff
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace WholeSpaceAcceptedCutoffApplications

/-- Literal d=3 Coulomb, coupling one: a single rate for zero and positive cutoffs. -/
theorem gaussianCoulombCommonCutoffRate :
    ∃ ρ : ℝ,0 < ρ ∧ ∀ N : ℕ,2 ≤ N → ∀ ε : ℝ,0 ≤ ε →
      ∀ q ∈ ClosedGradientGraph
        (GibbsLaw (N:=N) (ProbabilityTheory.stdGaussian (OneParticle 3)) 1 1 ε),
        ρ*LawVariance
          (GibbsLaw (N:=N) (ProbabilityTheory.stdGaussian (OneParticle 3)) 1 1 ε) q.1 ≤
          ClosedPhysicalEnergy q := by
  let V : OneParticle 3 → ℝ := fun x => ‖x‖^2/2
  let b : OneParticle 3 → ℝ := fun _ => 1
  have hV : GrowthClassPotential 3 1 1 (fun R => R^2/2) (fun _ => 3) V :=
    (QuadraticGaussianClass 3 1).2.2.2.2.2.2.2
  have hb : BoundedMultiplier 3 1 b := by
    refine ⟨measurable_const,1,1,zero_lt_one,le_rfl,(by norm_num),?_⟩
    intro x
    exact ⟨le_rfl,le_rfl⟩
  have hGaussian : ReferenceLaw V b=ProbabilityTheory.stdGaussian (OneParticle 3) :=
    (QuadraticGaussianReference 3).2.1
  obtain ⟨ρ,hρ,hPI⟩ := (WholeSpaceCollective.allCutoffs 3 (by norm_num) 1 1
    (by norm_num) (by norm_num) (by norm_num)).1 1 1 (by norm_num) (by norm_num)
    (fun _ => 3) (fun R => R^2/2)
  refine ⟨ρ,hρ,?_⟩
  intro N hN ε hε q hq
  have h := hPI V hV b hb N hN 1 ε (by norm_num) le_rfl hε
  rw [hGaussian] at h
  exact h q hq

/-- The genuinely nonzero coupling is one and the singular cutoff is exactly zero. -/
theorem gaussianCoulombSingularNonzeroCoupling :
    ∃ ρ : ℝ,0 < ρ ∧ ∀ N : ℕ,2 ≤ N →
      ∀ q ∈ ClosedGradientGraph
        (GibbsLaw (N:=N) (ProbabilityTheory.stdGaussian (OneParticle 3)) 1 1 0),
        ρ*LawVariance
          (GibbsLaw (N:=N) (ProbabilityTheory.stdGaussian (OneParticle 3)) 1 1 0) q.1 ≤
          ClosedPhysicalEnergy q := by
  obtain ⟨ρ,hρ,hPI⟩ := gaussianCoulombCommonCutoffRate
  exact ⟨ρ,hρ,fun N hN q hq => hPI N hN 0 le_rfl q hq⟩

/-- The same rho witnesses both laws, despite their different L2 closed domains. -/
theorem gaussianPositiveAndZeroCutoffsShareRate :
    ∃ ρ : ℝ,0 < ρ ∧ ∀ N : ℕ,2 ≤ N → ∀ ε : ℝ,0 < ε →
      (∀ q ∈ ClosedGradientGraph
          (GibbsLaw (N:=N) (ProbabilityTheory.stdGaussian (OneParticle 3)) 1 1 0),
        ρ*LawVariance
          (GibbsLaw (N:=N) (ProbabilityTheory.stdGaussian (OneParticle 3)) 1 1 0) q.1 ≤
          ClosedPhysicalEnergy q) ∧
      (∀ q ∈ ClosedGradientGraph
          (GibbsLaw (N:=N) (ProbabilityTheory.stdGaussian (OneParticle 3)) 1 1 ε),
        ρ*LawVariance
          (GibbsLaw (N:=N) (ProbabilityTheory.stdGaussian (OneParticle 3)) 1 1 ε) q.1 ≤
          ClosedPhysicalEnergy q) := by
  obtain ⟨ρ,hρ,hPI⟩ := gaussianCoulombCommonCutoffRate
  exact ⟨ρ,hρ,fun N hN ε hε => ⟨hPI N hN 0 le_rfl,hPI N hN ε hε.le⟩⟩

end WholeSpaceAcceptedCutoffApplications
