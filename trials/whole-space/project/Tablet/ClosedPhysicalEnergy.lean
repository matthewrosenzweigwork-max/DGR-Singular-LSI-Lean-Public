module

public import Tablet.ClosedGradientGraph

@[expose] public section

-- [TABLET NODE: ClosedPhysicalEnergy]
noncomputable def ClosedPhysicalEnergy {d N : ℕ}
    {P : MeasureTheory.Measure (ParticleConfig d N)}
    (q : MeasureTheory.Lp ℝ 2 P × MeasureTheory.Lp (ParticleConfig d N) 2 P) : ℝ :=
-- BODY
  ‖q.2‖ ^ 2
