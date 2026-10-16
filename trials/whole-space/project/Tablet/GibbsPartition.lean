import Tablet.ConfigurationReference
import Tablet.InteractionWeight

-- [TABLET NODE: GibbsPartition]
noncomputable def GibbsPartition {d N : ℕ}
    (μ : MeasureTheory.Measure (OneParticle d)) (s coupling ε : ℝ) : ℝ :=
-- BODY
  ∫ X, InteractionWeight s coupling ε X ∂ConfigurationReference d N μ
