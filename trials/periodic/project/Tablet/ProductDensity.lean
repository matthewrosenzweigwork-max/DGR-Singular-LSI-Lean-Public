import Tablet.Configuration
-- [TABLET NODE: ProductDensity]
noncomputable def ProductDensity {d N : ℕ} (q : UnitAddTorus (Fin d) → ℝ)
    (X : Configuration d N) : ℝ :=
-- BODY
  ∏ i : Fin N, q (X i)
