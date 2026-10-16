import Tablet.BackgroundPotential
open MeasureTheory
-- [TABLET NODE: BackgroundPairMean]
noncomputable def BackgroundPairMean {d : ℕ}
    (g r : UnitAddTorus (Fin d) → ℝ) : ℝ :=
-- BODY
  ∫ x, BackgroundPotential g r x * r x ∂volume
