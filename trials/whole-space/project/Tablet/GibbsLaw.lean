import Tablet.GibbsPartition

-- [TABLET NODE: GibbsLaw]
noncomputable def GibbsLaw {d N : ℕ}
    (μ : MeasureTheory.Measure (OneParticle d)) (s coupling ε : ℝ) :
    MeasureTheory.Measure (ParticleConfig d N) :=
-- BODY
  (ConfigurationReference d N μ).withDensity (fun X =>
    ENNReal.ofReal ((GibbsPartition (N := N) μ s coupling ε)⁻¹ * InteractionWeight s coupling ε X))
