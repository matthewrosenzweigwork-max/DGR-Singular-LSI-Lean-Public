module

public import Tablet.Preamble

@[expose] public section

-- [TABLET NODE: OneParticle]
abbrev OneParticle (d : ℕ) :=
-- BODY
  EuclideanSpace ℝ (Fin d)
