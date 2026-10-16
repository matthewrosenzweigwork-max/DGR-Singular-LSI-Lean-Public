module

public import Tablet.ParticleConfig
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section
set_option autoImplicit false
noncomputable section
-- [TABLET NODE: ConfigurationFlatten]
def ConfigurationFlatten (N d : ℕ) :
    ParticleConfig d N ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (N*d)) :=
-- BODY
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finProdFinEquiv
