import Tablet.TorusLift
open scoped ContDiff
-- [TABLET NODE: TorusSmooth]
def TorusSmooth {d : ℕ} (f : UnitAddTorus (Fin d) → ℝ) : Prop :=
-- BODY
  ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin d) => f (TorusLift d y))
