module

public import Tablet.ParticlePosition

@[expose] public section

-- [TABLET NODE: CollisionSet]
def CollisionSet (d N : ℕ) : Set (ParticleConfig d N) :=
-- BODY
  {X | ∃ i j : Fin N, i < j ∧ ParticlePosition X i = ParticlePosition X j}
