import Tablet.ParticleConfig

-- [TABLET NODE: ParticlePosition]
noncomputable def ParticlePosition {d N : ℕ} (X : ParticleConfig d N)
    (i : Fin N) : OneParticle d :=
-- BODY
  WithLp.toLp 2 (fun k => X (i, k))
