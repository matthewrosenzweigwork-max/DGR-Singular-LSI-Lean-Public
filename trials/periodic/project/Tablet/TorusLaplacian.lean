module

public import Tablet.TorusLift

@[expose] public section
-- [TABLET NODE: TorusLaplacian]
noncomputable def TorusLaplacian {d : ℕ} (f : UnitAddTorus (Fin d) → ℝ)
    (x : UnitAddTorus (Fin d)) : ℝ :=
-- BODY
  let y : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2
    (fun j => (AddCircle.equivIco (1 : ℝ) 0 (x j) : ℝ))
  ∑ j : Fin d, fderiv ℝ
    (fun z : EuclideanSpace ℝ (Fin d) =>
      fderiv ℝ (fun w => f (TorusLift d w)) z (EuclideanSpace.single j 1))
    y (EuclideanSpace.single j 1)
