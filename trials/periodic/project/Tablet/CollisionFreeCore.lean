module

public import Tablet.SmoothCore
public import Tablet.CollisionSet

@[expose] public section
-- [TABLET NODE: CollisionFreeCore]
def CollisionFreeCore (d N : ℕ) : Set (Configuration d N → ℝ) :=
-- BODY
  {f | f ∈ SmoothCore d N ∧ Disjoint (tsupport f) (CollisionSet d N)}
