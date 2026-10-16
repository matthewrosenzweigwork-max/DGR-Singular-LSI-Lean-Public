module

public import Tablet.GradientGraphClosure

@[expose] public section
-- [TABLET NODE: GradientFormDomain]
noncomputable def GradientFormDomain {d N : ℕ}
    (P : MeasureTheory.Measure (Configuration d N)) (collisionFree : Bool) :
    Set (MeasureTheory.Lp ℝ 2 P) :=
-- BODY
  {f | ∃ v, (f, v) ∈ GradientGraphClosure P collisionFree}
