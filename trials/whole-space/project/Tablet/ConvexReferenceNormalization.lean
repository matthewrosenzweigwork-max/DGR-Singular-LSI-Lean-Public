import Tablet.HessianMinimizer
import Tablet.ReferenceQuadraticNormalization
import Tablet.ReferenceLawProbability

-- [TABLET NODE: ConvexReferenceNormalization]
theorem ConvexReferenceNormalization {d : ℕ} (V b : OneParticle d → ℝ)
    (κ L : ℝ) (hκ : 0 < κ) (hV : PotentialBounds d κ V)
    (hb : BoundedMultiplier d L b) :
    MeasureTheory.Integrable (fun x => b x * Real.exp (-V x)) ∧
    0 < ReferencePartition V b ∧
    MeasureTheory.IsProbabilityMeasure (ReferenceLaw V b) := by
-- BODY
  obtain ⟨C, hC⟩ := (HessianMinimizer V κ hκ hV).1
  have hquad : ∀ x, (κ / 2) / 2 * ‖x‖ ^ 2 + -C ≤ V x := by
    intro x
    nlinarith [hC x]
  obtain ⟨hi, hZ⟩ := ReferenceQuadraticNormalization V b (κ / 2) (-C) L
    (by linarith) hV.regularity.continuous hb hquad
  obtain ⟨m, M, hm, _, _, hbounds⟩ := hb.bounds
  exact ⟨hi, hZ, ReferenceLawProbability V b hi
    (fun x => hm.le.trans (hbounds x).1) hZ⟩
