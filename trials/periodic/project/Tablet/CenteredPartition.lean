import Tablet.CenteredPairEnergy
import Tablet.ProductDensity
open MeasureTheory
-- [TABLET NODE: CenteredPartition]
noncomputable def CenteredPartition {d N : ℕ}
    (g r : UnitAddTorus (Fin d) → ℝ) (t : ℝ) : ℝ :=
-- BODY
  ∫ X : Configuration d N,
    Real.exp (-t * CenteredPairEnergy g r X) * ProductDensity r X ∂volume
