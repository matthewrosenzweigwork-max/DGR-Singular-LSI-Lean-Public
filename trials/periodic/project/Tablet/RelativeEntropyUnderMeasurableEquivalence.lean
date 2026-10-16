module

public import Tablet.EntropyObservationSupermodularity

@[expose] public section
open MeasureTheory InformationTheory

-- [TABLET NODE: RelativeEntropyUnderMeasurableEquivalence]
theorem RelativeEntropyUnderMeasurableEquivalence {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (S ν : Measure X) [IsFiniteMeasure S] [IsFiniteMeasure ν]
    (e : X ≃ᵐ Y) : klDiv (S.map e) (ν.map e) = klDiv S ν := by
-- BODY
  apply le_antisymm (klDiv_map_le S ν e.measurable)
  have hh := klDiv_map_le (S.map e) (ν.map e) e.symm.measurable
  simpa only [MeasurableEquiv.map_symm_map] using hh
