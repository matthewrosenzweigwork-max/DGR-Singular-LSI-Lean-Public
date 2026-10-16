import Tablet.SmoothCore
import Tablet.CollisionSet
-- [TABLET NODE: CollisionFreeCore]
def CollisionFreeCore (d N : ℕ) : Set (Configuration d N → ℝ) :=
-- BODY
  {f | f ∈ SmoothCore d N ∧ Disjoint (tsupport f) (CollisionSet d N)}
