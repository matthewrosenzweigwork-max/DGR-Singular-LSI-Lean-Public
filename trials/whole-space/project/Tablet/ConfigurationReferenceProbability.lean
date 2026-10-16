module

public import Tablet.ConfigurationReference

@[expose] public section

-- [TABLET NODE: ConfigurationReferenceProbability]
theorem ConfigurationReferenceProbability (d N : ℕ)
    (μ : MeasureTheory.Measure (OneParticle d)) [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (ConfigurationReference d N μ) := by
-- BODY
  unfold ConfigurationReference
  have hflat : Continuous (fun Y : Fin N → OneParticle d =>
      WithLp.toLp 2 (fun ik : Fin N × Fin d => Y ik.1 ik.2)) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin N × Fin d => ℝ)).comp
    apply continuous_pi
    intro ik
    exact (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) ik.2).comp (continuous_apply ik.1)
  exact (MeasureTheory.Measure.isProbabilityMeasure_map_iff
    hflat.measurable.aemeasurable).mpr inferInstance
