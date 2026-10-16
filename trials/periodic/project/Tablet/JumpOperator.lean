module

public import Tablet.ConditionalPotential
public import Tablet.Replacement

@[expose] public section
-- [TABLET NODE: JumpOperator]
noncomputable def JumpOperator {d N : ℕ} (G q : UnitAddTorus (Fin d) → ℝ)
    (β : ℝ) (f : Configuration d N → ℝ) (X : Configuration d N) : ℝ :=
-- BODY
  ∑ i : Fin N, ∫ z, Real.exp (-ConditionalPotential G β X i z) *
    (f (Replacement X i z) - f X) * q z
