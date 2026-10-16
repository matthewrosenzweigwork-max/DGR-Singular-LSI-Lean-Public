import Tablet.ConfigurationTranslation
import Tablet.L2MeasurePullback
set_option autoImplicit false
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped ContDiff ENNReal
noncomputable section

-- [TABLET NODE: ConfigurationGradientPullback]
noncomputable def ConfigurationGradientPullback {d N : ℕ} (a : OneParticle d)
    (P : Measure (ParticleConfig d N)) :
    (Lp ℝ 2 (P.map (ConfigurationTranslation a).toMeasurableEquiv) ×
      Lp (ParticleConfig d N) 2 (P.map (ConfigurationTranslation a).toMeasurableEquiv)) ≃ₜ
      (Lp ℝ 2 P × Lp (ParticleConfig d N) 2 P) :=
-- BODY
  (L2MeasurePullback (F := ℝ) (ConfigurationTranslation a).toMeasurableEquiv P).toHomeomorph.prodCongr
    (L2MeasurePullback (F := ParticleConfig d N) (ConfigurationTranslation a).toMeasurableEquiv P).toHomeomorph
