module

public import Tablet.Configuration

@[expose] public section
-- [TABLET NODE: Replacement]
def Replacement {d N : ℕ} (X : Configuration d N) (i : Fin N)
    (z : UnitAddTorus (Fin d)) : Configuration d N :=
-- BODY
  Function.update X i z
