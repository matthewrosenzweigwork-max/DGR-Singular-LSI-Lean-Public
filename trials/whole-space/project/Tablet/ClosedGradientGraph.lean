module

public import Tablet.SmoothGradientCore

@[expose] public section

-- [TABLET NODE: ClosedGradientGraph]
def ClosedGradientGraph {d N : ℕ}
    (P : MeasureTheory.Measure (ParticleConfig d N)) :
    Set (MeasureTheory.Lp ℝ 2 P × MeasureTheory.Lp (ParticleConfig d N) 2 P) :=
-- BODY
  closure (SmoothGradientCore P)
