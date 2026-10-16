module

public import Tablet.TorusLift
public import Tablet.TorusLaplacian

@[expose] public section
-- [TABLET NODE: TorusGradient]
noncomputable def TorusGradient {d : ℕ} (f : UnitAddTorus (Fin d) → ℝ)
    (x : UnitAddTorus (Fin d)) : EuclideanSpace ℝ (Fin d) :=
-- BODY
  let y : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2
    (fun j => (AddCircle.equivIco (1 : ℝ) 0 (x j) : ℝ))
  WithLp.toLp 2 (fun j =>
    fderiv ℝ (fun z => f (TorusLift d z)) y (EuclideanSpace.single j 1))
