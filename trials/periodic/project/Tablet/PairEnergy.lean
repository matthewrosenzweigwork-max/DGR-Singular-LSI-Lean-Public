module

public import Tablet.Configuration

@[expose] public section
-- [TABLET NODE: PairEnergy]
noncomputable def PairEnergy {d N : ℕ} (g : UnitAddTorus (Fin d) → ℝ)
    (X : Configuration d N) : ℝ :=
-- BODY
  (N : ℝ)⁻¹ * ∑ i : Fin N, ∑ j : Fin N,
    if i < j then g (X i - X j) else 0
