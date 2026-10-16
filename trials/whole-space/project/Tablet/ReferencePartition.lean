import Tablet.OneParticle

-- [TABLET NODE: ReferencePartition]
noncomputable def ReferencePartition {d : ℕ} (V b : OneParticle d → ℝ) : ℝ :=
-- BODY
  ∫ x, b x * Real.exp (-V x)
