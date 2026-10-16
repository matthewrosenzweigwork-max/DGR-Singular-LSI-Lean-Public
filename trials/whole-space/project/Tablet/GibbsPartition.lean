module

public import Tablet.ConfigurationReference
public import Tablet.InteractionWeight

@[expose] public section

-- [TABLET NODE: GibbsPartition]
noncomputable def GibbsPartition {d N : ℕ}
    (μ : MeasureTheory.Measure (OneParticle d)) (s coupling ε : ℝ) : ℝ :=
-- BODY
  ∫ X, InteractionWeight s coupling ε X ∂ConfigurationReference d N μ
