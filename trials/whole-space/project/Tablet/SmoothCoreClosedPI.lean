import Tablet.LpVarianceContinuity
import Tablet.ClosedGradientGraph
import Tablet.ClosedPhysicalEnergy
open MeasureTheory Filter Set
open scoped Topology ContDiff

-- [TABLET NODE: SmoothCoreClosedPI]
theorem SmoothCoreClosedPI {d N : ℕ}
    (P : Measure (ParticleConfig d N)) [IsProbabilityMeasure P] (C : ℝ)
    (hcore : ∀ (g : ParticleConfig d N → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
      MemLp g 2 P → MemLp (EuclideanGradient g) 2 P →
      ProbabilityTheory.variance g P ≤ C * (∫ X, ‖EuclideanGradient g X‖^2 ∂P))
    (f : Lp ℝ 2 P) (v : Lp (ParticleConfig d N) 2 P)
    (hfv : (f,v) ∈ ClosedGradientGraph P) :
    ProbabilityTheory.variance (f : ParticleConfig d N → ℝ) P ≤ C * ‖v‖^2 := by
-- BODY
  have hclosed : IsClosed {p : Lp ℝ 2 P × Lp (ParticleConfig d N) 2 P |
      ProbabilityTheory.variance (p.1 : ParticleConfig d N → ℝ) P ≤ C * ‖p.2‖^2} :=
    isClosed_le ((LpVarianceContinuity P).comp continuous_fst)
      (continuous_const.mul (continuous_snd.norm.pow 2))
  apply (closure_minimal (t := {p : Lp ℝ 2 P × Lp (ParticleConfig d N) 2 P |
    ProbabilityTheory.variance (p.1 : ParticleConfig d N → ℝ) P ≤ C * ‖p.2‖^2}) ?_ hclosed) hfv
  rintro p ⟨g,hgs,hgc,hg,hD,rfl⟩
  change ProbabilityTheory.variance ((hg.toLp g) : ParticleConfig d N → ℝ) P ≤ C * ‖hD.toLp (EuclideanGradient g)‖^2
  rw [ProbabilityTheory.variance_congr hg.coeFn_toLp]
  apply (hcore g hgs hgc hg hD).trans_eq
  congr 1
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp_rw [real_inner_self_eq_norm_sq]
  exact integral_congr_ae (hD.coeFn_toLp.mono (fun X hX => by dsimp only; rw [hX]))

