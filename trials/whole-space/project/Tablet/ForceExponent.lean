module

public import Tablet.Preamble

@[expose] public section

-- [TABLET NODE: ForceExponent]
noncomputable def ForceExponent (s : ℝ) : ℝ :=
-- BODY
  2 / (s + 1)
