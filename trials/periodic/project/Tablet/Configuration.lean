import Tablet.Preamble
-- [TABLET NODE: Configuration]
abbrev Configuration (d N : ℕ) :=
-- BODY
  Fin N → UnitAddTorus (Fin d)
