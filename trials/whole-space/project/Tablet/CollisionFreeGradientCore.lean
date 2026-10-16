module

public import Tablet.SmoothGradientCore
public import Tablet.CollisionSet

@[expose] public section
open scoped ContDiff

-- [TABLET NODE: CollisionFreeGradientCore]
def CollisionFreeGradientCore {d N : ℕ}
    (P : MeasureTheory.Measure (ParticleConfig d N)) :
    Set (MeasureTheory.Lp ℝ 2 P × MeasureTheory.Lp (ParticleConfig d N) 2 P) :=
-- BODY
  {q | ∃ f : ParticleConfig d N → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    Disjoint (tsupport f) (CollisionSet d N) ∧
    ∃ hf : MeasureTheory.MemLp f 2 P,
    ∃ hg : MeasureTheory.MemLp (EuclideanGradient f) 2 P,
      q = (hf.toLp f, hg.toLp (EuclideanGradient f))}
