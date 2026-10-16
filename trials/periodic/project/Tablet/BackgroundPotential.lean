module

public import Tablet.Preamble
public import Mathlib.Analysis.Convolution

@[expose] public section
open MeasureTheory
-- [TABLET NODE: BackgroundPotential]
noncomputable def BackgroundPotential {d : ℕ}
    (g r : UnitAddTorus (Fin d) → ℝ) (x : UnitAddTorus (Fin d)) : ℝ :=
-- BODY
  MeasureTheory.convolution r g (ContinuousLinearMap.mul ℝ ℝ) volume x
