import Tablet.Preamble
import Mathlib.Analysis.Convolution
open MeasureTheory
-- [TABLET NODE: BackgroundPotential]
noncomputable def BackgroundPotential {d : ℕ}
    (g r : UnitAddTorus (Fin d) → ℝ) (x : UnitAddTorus (Fin d)) : ℝ :=
-- BODY
  MeasureTheory.convolution r g (ContinuousLinearMap.mul ℝ ℝ) volume x
