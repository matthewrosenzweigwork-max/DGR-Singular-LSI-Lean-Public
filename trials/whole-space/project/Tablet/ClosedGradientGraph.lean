import Tablet.SmoothGradientCore

-- [TABLET NODE: ClosedGradientGraph]
def ClosedGradientGraph {d N : ℕ}
    (P : MeasureTheory.Measure (ParticleConfig d N)) :
    Set (MeasureTheory.Lp ℝ 2 P × MeasureTheory.Lp (ParticleConfig d N) 2 P) :=
-- BODY
  closure (SmoothGradientCore P)
