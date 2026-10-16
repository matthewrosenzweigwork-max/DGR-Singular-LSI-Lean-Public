import Tablet.HeatKernel
-- [TABLET NODE: HeatSourceDensity]
noncomputable def HeatSourceDensity (d : ℕ) (ε : ℝ)
    (μ : MeasureTheory.Measure (UnitAddTorus (Fin d)))
    (x : UnitAddTorus (Fin d)) : ℝ :=
-- BODY
  ∫ y, HeatKernel d ε (x - y) ∂μ
