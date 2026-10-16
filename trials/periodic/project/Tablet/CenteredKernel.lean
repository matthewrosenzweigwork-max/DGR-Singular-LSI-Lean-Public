module

public import Tablet.BackgroundPairMean

@[expose] public section
-- [TABLET NODE: CenteredKernel]
noncomputable def CenteredKernel {d : ℕ}
    (g r : UnitAddTorus (Fin d) → ℝ)
    (x y : UnitAddTorus (Fin d)) : ℝ :=
-- BODY
  g (x - y) - BackgroundPotential g r x - BackgroundPotential g r y +
    BackgroundPairMean g r
