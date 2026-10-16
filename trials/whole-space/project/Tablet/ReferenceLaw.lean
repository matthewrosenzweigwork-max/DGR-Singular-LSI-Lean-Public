module

public import Tablet.ReferencePartition

@[expose] public section

-- [TABLET NODE: ReferenceLaw]
noncomputable def ReferenceLaw {d : ℕ} (V b : OneParticle d → ℝ) :
    MeasureTheory.Measure (OneParticle d) :=
-- BODY
  MeasureTheory.volume.withDensity (fun x =>
    ENNReal.ofReal ((ReferencePartition V b)⁻¹ * (b x * Real.exp (-V x))))
