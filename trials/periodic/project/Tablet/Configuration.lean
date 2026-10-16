module

public import Tablet.Preamble

@[expose] public section
-- [TABLET NODE: Configuration]
abbrev Configuration (d N : ℕ) :=
-- BODY
  Fin N → UnitAddTorus (Fin d)
