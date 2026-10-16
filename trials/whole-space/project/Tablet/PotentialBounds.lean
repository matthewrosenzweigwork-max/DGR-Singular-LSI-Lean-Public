import Tablet.OneParticle
import Tablet.EuclideanLaplacian

-- [TABLET NODE: PotentialBounds]
structure PotentialBounds (d : ℕ) (κ : ℝ) (V : OneParticle d → ℝ) : Prop where
-- BODY
  regularity : ContDiff ℝ 2 V
  lower : ∀ x u, κ * ‖u‖ ^ 2 ≤ EuclideanHessian V x u u
