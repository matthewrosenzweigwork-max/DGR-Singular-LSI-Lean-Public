import Tablet.GradientGraphClosure
-- [TABLET NODE: ClosedGradientEnergy]
noncomputable def ClosedGradientEnergy {d N : ℕ}
    {P : MeasureTheory.Measure (Configuration d N)}
    (v : MeasureTheory.Lp (EuclideanSpace ℝ (Fin N × Fin d)) 2 P) : ℝ :=
-- BODY
  ‖v‖ ^ 2
