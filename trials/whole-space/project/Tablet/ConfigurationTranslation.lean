import Tablet.ParticleConfig
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
set_option autoImplicit false
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped ContDiff ENNReal
noncomputable section

-- [TABLET NODE: ConfigurationTranslation]
noncomputable def ConfigurationTranslation {d N : ℕ} (a : OneParticle d) :
    ParticleConfig d N ≃ₜ ParticleConfig d N :=
-- BODY
  Homeomorph.addRight (-(WithLp.toLp 2 (fun ik : Fin N × Fin d => a ik.2) : ParticleConfig d N))
