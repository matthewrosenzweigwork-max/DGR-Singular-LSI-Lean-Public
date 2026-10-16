module

public import Tablet.CoordinateGradient

@[expose] public section
-- [TABLET NODE: PhysicalEnergy]
noncomputable def PhysicalEnergy {d N : ℕ}
    (P : MeasureTheory.Measure (Configuration d N))
    (f : Configuration d N → ℝ) : ℝ :=
-- BODY
  ∫ X, ‖CoordinateGradient f X‖ ^ 2 ∂P
