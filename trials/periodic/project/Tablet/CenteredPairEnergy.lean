module

public import Tablet.CenteredKernel
public import Tablet.Configuration

@[expose] public section
-- [TABLET NODE: CenteredPairEnergy]
noncomputable def CenteredPairEnergy {d N : ℕ}
    (g r : UnitAddTorus (Fin d) → ℝ) (X : Configuration d N) : ℝ :=
-- BODY
  (N : ℝ)⁻¹ * ∑ i : Fin N, ∑ j : Fin N,
    if i < j then CenteredKernel g r (X i) (X j) else 0
