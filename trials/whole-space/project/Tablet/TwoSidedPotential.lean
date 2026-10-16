module

public import Tablet.PotentialBounds

@[expose] public section

-- [TABLET NODE: TwoSidedPotential]
structure TwoSidedPotential (d : ℕ) (κ K : ℝ)
    (V : OneParticle d → ℝ) : Prop extends PotentialBounds d κ V where
-- BODY
  upper : ∀ x u, EuclideanHessian V x u u ≤ K * ‖u‖ ^ 2
