import Tablet.ParticleConfig
import Mathlib.Analysis.InnerProductSpace.PiL2
set_option autoImplicit false
noncomputable section
-- [TABLET NODE: ConfigurationFlatten]
def ConfigurationFlatten (N d : ℕ) :
    ParticleConfig d N ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (N*d)) :=
-- BODY
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finProdFinEquiv
