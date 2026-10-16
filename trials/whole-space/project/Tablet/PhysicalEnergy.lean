import Tablet.ParticleConfig
import Tablet.EuclideanGradient

-- [TABLET NODE: PhysicalEnergy]
noncomputable def PhysicalEnergy {d N : ℕ}
    (P : MeasureTheory.Measure (ParticleConfig d N)) (f : ParticleConfig d N → ℝ) : ℝ :=
-- BODY
  ∫ X, ‖EuclideanGradient f X‖ ^ 2 ∂P
