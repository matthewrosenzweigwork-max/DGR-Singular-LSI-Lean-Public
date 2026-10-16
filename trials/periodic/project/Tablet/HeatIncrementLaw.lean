module

public import Tablet.HeatKernelFacts

@[expose] public section
open MeasureTheory
-- [TABLET NODE: HeatIncrementLaw]
noncomputable def HeatIncrementLaw (d : ℕ) (t : ℝ) : Measure (UnitAddTorus (Fin d)) :=
-- BODY
  (volume : Measure (UnitAddTorus (Fin d))).withDensity (fun z=>ENNReal.ofReal (HeatKernel d t z))
