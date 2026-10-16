module

public import Tablet.RieszKernel
public import Tablet.ParticlePosition

@[expose] public section

-- [TABLET NODE: PairInteraction]
noncomputable def PairInteraction {d N : ℕ} (s coupling ε : ℝ)
    (X : ParticleConfig d N) : ℝ :=
-- BODY
  (coupling / (N : ℝ)) * ∑ i : Fin N, ∑ j : Fin N,
    if i < j then RieszKernel s ε (ParticlePosition X i - ParticlePosition X j) else 0
