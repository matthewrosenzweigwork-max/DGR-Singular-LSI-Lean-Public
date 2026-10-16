import Tablet.CenteredPairEnergy
import Tablet.NormalizedTilt
import Tablet.ProductDensity
open MeasureTheory
-- [TABLET NODE: CenteredCanonicalLaw]
noncomputable def CenteredCanonicalLaw {d N : ℕ}
    (g r : UnitAddTorus (Fin d) → ℝ) (β : ℝ) : Measure (Configuration d N) :=
-- BODY
  NormalizedTilt (Measure.pi (fun _ : Fin N =>
    (volume : Measure (UnitAddTorus (Fin d))).withDensity (fun x => ENNReal.ofReal (r x))))
    (fun X => Real.exp (-β * CenteredPairEnergy g r X))
