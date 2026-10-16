module

public import Tablet.PairEnergy
public import Tablet.ProductDensity
public import Tablet.RieszKernel

@[expose] public section
-- [TABLET NODE: GibbsWeight]
noncomputable def GibbsWeight {d N : ℕ} (g q : UnitAddTorus (Fin d) → ℝ)
    (β : ℝ) (X : Configuration d N) : ℝ :=
-- BODY
  Real.exp (-β * PairEnergy g X) * ProductDensity q X
