module

public import Tablet.OneParticle

@[expose] public section

-- [TABLET NODE: ParticleConfig]
abbrev ParticleConfig (d N : ℕ) :=
-- BODY
  EuclideanSpace ℝ (Fin N × Fin d)
