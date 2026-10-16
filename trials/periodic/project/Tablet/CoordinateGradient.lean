import Tablet.ConfigurationLift
-- [TABLET NODE: CoordinateGradient]
noncomputable def CoordinateGradient {d N : ℕ}
    (f : Configuration d N → ℝ) (X : Configuration d N) :
    EuclideanSpace ℝ (Fin N × Fin d) :=
-- BODY
  let y : EuclideanSpace ℝ (Fin N × Fin d) := WithLp.toLp 2
    (fun ij => (AddCircle.equivIco (1 : ℝ) 0 (X ij.1 ij.2) : ℝ))
  WithLp.toLp 2 (fun ij =>
    fderiv ℝ (fun z => f (ConfigurationLift d N z)) y
      (EuclideanSpace.single ij 1))
