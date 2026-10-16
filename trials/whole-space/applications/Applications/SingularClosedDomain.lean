import Applications.CutoffSingularPI
import Tablet.GibbsClosedCoreEquality
import Tablet.GibbsClosedConstants
import Tablet.GibbsClosedGradientUnique
open MeasureTheory
open scoped ENNReal ContDiff
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace WholeSpaceAcceptedCutoffApplications

/-- Actual two-particle singular Coulomb law, its full domain, and the constant test. -/
theorem twoParticleSingularGaussianClosedApplication :
    let P := GibbsLaw (N:=2) (ProbabilityTheory.stdGaussian (OneParticle 3)) 1 1 0
    ∃ ρ : ℝ,0 < ρ ∧ IsProbabilityMeasure P ∧
      closure (CollisionFreeGradientCore P)=ClosedGradientGraph P ∧
      (∀ (f : Lp ℝ 2 P) (v w : Lp (ParticleConfig 3 2) 2 P),
        (f,v) ∈ ClosedGradientGraph P → (f,w) ∈ ClosedGradientGraph P → v=w) ∧
      (∃ hf : MemLp (fun _ : ParticleConfig 3 2 => (1:ℝ)) 2 P,
        (hf.toLp (fun _ => (1:ℝ)),(0 : Lp (ParticleConfig 3 2) 2 P)) ∈ ClosedGradientGraph P ∧
        ρ*LawVariance P (hf.toLp (fun _ => (1:ℝ))) ≤ 0) ∧
      ∀ q ∈ ClosedGradientGraph P,ρ*LawVariance P q.1 ≤ ClosedPhysicalEnergy q := by
  classical
  dsimp only
  let V : OneParticle 3 → ℝ := fun x => ‖x‖^2/2
  let b : OneParticle 3 → ℝ := fun _ => 1
  have hV : PotentialBounds 3 1 V := (QuadraticGaussianClass 3 1).2.2.2.2.1.toPotentialBounds
  have hb : BoundedMultiplier 3 1 b := by
    refine ⟨measurable_const,1,1,zero_lt_one,le_rfl,(by norm_num),?_⟩
    intro x
    exact ⟨le_rfl,le_rfl⟩
  have hGaussian : ReferenceLaw V b=ProbabilityTheory.stdGaussian (OneParticle 3) :=
    (QuadraticGaussianReference 3).2.1
  rw [←hGaussian]
  let P := GibbsLaw (N:=2) (ReferenceLaw V b) 1 1 0
  haveI : IsProbabilityMeasure (ReferenceLaw V b) :=
    (ConvexReferenceNormalization V b 1 1 zero_lt_one hV hb).2.2
  have hprob : IsProbabilityMeasure P := by
    have h := (SingularGibbsNormalization (N:=2) (by norm_num) (ReferenceLaw V b)
      (withDensity_absolutelyContinuous _ _) 1 1 (by norm_num) (by norm_num)).2.2
    exact h
  have hcore : closure (CollisionFreeGradientCore P)=ClosedGradientGraph P := by
    have h := GibbsClosedCoreEquality (N:=2) (by norm_num : 3 ≤ 3) V b 1 1 zero_lt_one hV hb
      1 1 0 (by norm_num) (by norm_num) le_rfl
    exact h
  have hunique (f : Lp ℝ 2 P) (v w : Lp (ParticleConfig 3 2) 2 P)
      (hv : (f,v) ∈ ClosedGradientGraph P) (hw : (f,w) ∈ ClosedGradientGraph P) : v=w := by
    have h := GibbsClosedGradientUnique (N:=2) (by norm_num : 0 < 3) V b 1 1 zero_lt_one hV hb
      1 1 0 (by norm_num) (by norm_num) le_rfl
    exact h f v w hv hw
  have hone : ∃ hf : MemLp (fun _ : ParticleConfig 3 2 => (1:ℝ)) 2 P,
      (hf.toLp (fun _ => (1:ℝ)),(0 : Lp (ParticleConfig 3 2) 2 P)) ∈ ClosedGradientGraph P := by
    have h := GibbsClosedConstants (N:=2) (by norm_num : 0 < 3) V b 1 1 zero_lt_one hV hb
      1 1 0 (by norm_num) (by norm_num) le_rfl
    exact h
  obtain ⟨ρ,hρ,hPI⟩ := gaussianCoulombSingularNonzeroCoupling
  have hfull : ∀ q ∈ ClosedGradientGraph P,ρ*LawVariance P q.1 ≤ ClosedPhysicalEnergy q := by
    have h := hPI 2 le_rfl
    rw [←hGaussian] at h
    exact h
  obtain ⟨hf,hfgraph⟩ := hone
  have hconst := hfull (hf.toLp (fun _ => (1:ℝ)),0) hfgraph
  have hconstZero : ρ*LawVariance P (hf.toLp (fun _ => (1:ℝ))) ≤ 0 := by
    simpa only [ClosedPhysicalEnergy,Prod.snd,norm_zero,zero_pow (by norm_num : 2 ≠ 0)] using hconst
  exact ⟨ρ,hρ,hprob,hcore,hunique,⟨hf,hfgraph,hconstZero⟩,hfull⟩

end WholeSpaceAcceptedCutoffApplications
