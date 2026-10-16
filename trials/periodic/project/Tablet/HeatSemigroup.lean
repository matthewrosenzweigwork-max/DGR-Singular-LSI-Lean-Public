module

public import Tablet.HeatKernel

@[expose] public section
-- [TABLET NODE: HeatSemigroup]
noncomputable def HeatSemigroup (d : ℕ) (t : ℝ)
    (f : UnitAddTorus (Fin d) → ℝ) (x : UnitAddTorus (Fin d)) : ℝ :=
-- BODY
  ∫ y, HeatKernel d t y * f (x - y) ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d)))
