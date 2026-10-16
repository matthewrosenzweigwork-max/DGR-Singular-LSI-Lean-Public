module

public import Tablet.Configuration

@[expose] public section
-- [TABLET NODE: CollisionSet]
def CollisionSet (d N : ℕ) : Set (Configuration d N) :=
-- BODY
  {X | ∃ i j : Fin N, i < j ∧ X i = X j}
