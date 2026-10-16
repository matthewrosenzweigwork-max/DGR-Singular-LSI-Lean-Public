import Tablet.NormalizedTilt
import Mathlib.Probability.Kernel.WithDensity
open MeasureTheory ProbabilityTheory

-- [TABLET NODE: GibbsConditionalKernel]
noncomputable def GibbsConditionalKernel {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (η : Measure Y) [IsProbabilityMeasure η] (U : X × Y → ℝ) : Kernel X Y :=
-- BODY
  Kernel.withDensity (Kernel.const X η) (fun x y =>
    ENNReal.ofReal (Real.exp (-U (x,y)) / (∫ z, Real.exp (-U (x,z)) ∂η)))
