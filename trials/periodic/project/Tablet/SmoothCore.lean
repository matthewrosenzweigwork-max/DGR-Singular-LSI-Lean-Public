import Tablet.ConfigurationLift
open scoped ContDiff
-- [TABLET NODE: SmoothCore]
def SmoothCore (d N : ℕ) : Set (Configuration d N → ℝ) :=
-- BODY
  {f | ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin N × Fin d) =>
    f (ConfigurationLift d N y))}
