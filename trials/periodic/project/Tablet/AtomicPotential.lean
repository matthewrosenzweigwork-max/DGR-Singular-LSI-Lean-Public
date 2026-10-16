module

public import Tablet.Preamble

@[expose] public section
-- [TABLET NODE: AtomicPotential]
def AtomicPotential {d n : ℕ} (g : UnitAddTorus (Fin d) → ℝ)
    (w : Fin n → ℝ) (y : Fin n → UnitAddTorus (Fin d))
    (x : UnitAddTorus (Fin d)) : ℝ :=
-- BODY
  ∑ j : Fin n, w j * g (x - y j)
