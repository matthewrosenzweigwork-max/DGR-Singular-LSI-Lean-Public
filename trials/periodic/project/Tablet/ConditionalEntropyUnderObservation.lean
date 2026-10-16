module

public import Tablet.Preamble
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

-- [TABLET NODE: ConditionalEntropyUnderObservation]
theorem ConditionalEntropyUnderObservation {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (η : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (κ : Kernel X Y) [IsMarkovKernel κ] (f : X → Z) (hf : Measurable f) :
    klDiv ((μ ⊗ₘ κ).map (Prod.map f id)) ((μ.map f).prod η) ≤
      klDiv (μ ⊗ₘ κ) (μ.prod η) := by
-- BODY
  have h := klDiv_map_le (μ ⊗ₘ κ) (μ.prod η) (hf.prodMap measurable_id)
  have heq : (μ.prod η).map (Prod.map f id) = (μ.map f).prod η := by
    simpa only [Measure.map_id] using
      (Measure.map_prod_map μ η hf measurable_id).symm
  rw [heq] at h
  exact h
