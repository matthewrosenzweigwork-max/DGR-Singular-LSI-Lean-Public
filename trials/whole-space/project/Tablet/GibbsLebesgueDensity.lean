module

public import Tablet.GibbsLaw

@[expose] public section
open scoped BigOperators

-- [TABLET NODE: GibbsLebesgueDensity]
noncomputable def GibbsLebesgueDensity {d N : ℕ}
    (V b : OneParticle d → ℝ) (s coupling ε : ℝ) (X : ParticleConfig d N) : ℝ :=
-- BODY
  ((ReferencePartition V b) ^ N * GibbsPartition (N := N) (ReferenceLaw V b) s coupling ε)⁻¹ *
    (∏ i : Fin N, b (ParticlePosition X i)) *
    Real.exp (-(∑ i : Fin N, V (ParticlePosition X i))) * InteractionWeight s coupling ε X
