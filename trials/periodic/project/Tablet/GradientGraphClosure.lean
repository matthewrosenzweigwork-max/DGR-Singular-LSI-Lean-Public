module

public import Tablet.CoordinateGradient
public import Tablet.CollisionFreeCore

@[expose] public section
-- [TABLET NODE: GradientGraphClosure]
noncomputable def GradientGraphClosure {d N : ℕ}
    (P : MeasureTheory.Measure (Configuration d N)) (collisionFree : Bool) :
    Set (MeasureTheory.Lp ℝ 2 P ×
      MeasureTheory.Lp (EuclideanSpace ℝ (Fin N × Fin d)) 2 P) :=
-- BODY
  closure {v | ∃ (f : Configuration d N → ℝ)
    (hf : MeasureTheory.MemLp f 2 P)
    (hD : MeasureTheory.MemLp (CoordinateGradient f) 2 P),
    f ∈ (if collisionFree then CollisionFreeCore d N else SmoothCore d N) ∧
    v = (hf.toLp f, hD.toLp (CoordinateGradient f))}
