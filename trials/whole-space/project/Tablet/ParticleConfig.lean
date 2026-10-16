import Tablet.OneParticle

-- [TABLET NODE: ParticleConfig]
abbrev ParticleConfig (d N : ℕ) :=
-- BODY
  EuclideanSpace ℝ (Fin N × Fin d)
