module

public import Tablet.Preamble

@[expose] public section
-- [TABLET NODE: TorusLift]
def TorusLift (d : ℕ) (y : EuclideanSpace ℝ (Fin d)) : UnitAddTorus (Fin d) :=
-- BODY
  fun j => (y j : AddCircle (1 : ℝ))
