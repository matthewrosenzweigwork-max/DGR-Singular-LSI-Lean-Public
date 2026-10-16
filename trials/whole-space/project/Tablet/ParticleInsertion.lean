import Tablet.ParticlePosition

-- [TABLET NODE: ParticleInsertion]
noncomputable def ParticleInsertion {d N : ℕ} (X : ParticleConfig d N) (i : Fin N)
    (z : OneParticle d) : ParticleConfig d N :=
-- BODY
  WithLp.toLp 2 (fun jk => if jk.1 = i then z jk.2 else X jk)
