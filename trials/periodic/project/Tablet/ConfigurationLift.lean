module

public import Tablet.Configuration

@[expose] public section
-- [TABLET NODE: ConfigurationLift]
def ConfigurationLift (d N : ℕ)
    (y : EuclideanSpace ℝ (Fin N × Fin d)) : Configuration d N :=
-- BODY
  fun i j => (y (i, j) : AddCircle (1 : ℝ))
