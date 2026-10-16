import Tablet.OneParticle

-- [TABLET NODE: BoundedMultiplier]
structure BoundedMultiplier (d : ℕ) (L : ℝ) (b : OneParticle d → ℝ) : Prop where
-- BODY
  measurable : Measurable b
  bounds : ∃ bmin bmax : ℝ, 0 < bmin ∧ bmin ≤ bmax ∧
    bmax / bmin ≤ L ∧ ∀ x, bmin ≤ b x ∧ b x ≤ bmax
