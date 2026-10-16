import Tablet.Preamble
-- [TABLET NODE: HeatKernel]
noncomputable def HeatKernel (d : ℕ) (t : ℝ) (x : UnitAddTorus (Fin d)) : ℝ :=
-- BODY
  ∑' k : Fin d → ℤ,
    Real.exp (-4 * Real.pi ^ 2 * t * ∑ j, (k j : ℝ) ^ 2) *
      Real.cos (2 * Real.pi * ∑ j,
        (k j : ℝ) * (AddCircle.equivIco (1 : ℝ) 0 (x j) : ℝ))
