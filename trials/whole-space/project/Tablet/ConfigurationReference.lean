module

public import Tablet.ParticleConfig
public import Tablet.ReferenceLaw

@[expose] public section

-- [TABLET NODE: ConfigurationReference]
noncomputable def ConfigurationReference (d N : ℕ)
    (μ : MeasureTheory.Measure (OneParticle d)) :
    MeasureTheory.Measure (ParticleConfig d N) :=
-- BODY
  MeasureTheory.Measure.map
    (fun Y : Fin N → OneParticle d => WithLp.toLp 2 (fun ik : Fin N × Fin d =>
      Y ik.1 ik.2)) (MeasureTheory.Measure.pi (fun _ : Fin N => μ))
