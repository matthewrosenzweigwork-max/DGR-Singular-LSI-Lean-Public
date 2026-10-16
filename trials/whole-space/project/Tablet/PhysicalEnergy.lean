module

public import Tablet.ParticleConfig
public import Tablet.EuclideanGradient

@[expose] public section

-- [TABLET NODE: PhysicalEnergy]
noncomputable def PhysicalEnergy {d N : ℕ}
    (P : MeasureTheory.Measure (ParticleConfig d N)) (f : ParticleConfig d N → ℝ) : ℝ :=
-- BODY
  ∫ X, ‖EuclideanGradient f X‖ ^ 2 ∂P
