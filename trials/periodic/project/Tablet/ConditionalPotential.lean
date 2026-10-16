import Tablet.Configuration
-- [TABLET NODE: ConditionalPotential]
noncomputable def ConditionalPotential {d N : ℕ} (g : UnitAddTorus (Fin d) → ℝ)
    (β : ℝ) (X : Configuration d N) (i : Fin N) (z : UnitAddTorus (Fin d)) : ℝ :=
-- BODY
  β / (N : ℝ) * ∑ j : Fin N, if j = i then 0 else g (z - X j)
