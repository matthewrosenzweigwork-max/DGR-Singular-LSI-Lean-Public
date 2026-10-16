module

public import Tablet.HeatKernel

@[expose] public section
open MeasureTheory
-- [TABLET NODE: DGRGaussianPhysicalNear]
noncomputable def DGRGaussianPhysicalNear (d : ℕ) (s a η : ℝ)
    (x : UnitAddTorus (Fin d)) : ℝ :=
-- BODY
  (2*a/Real.Gamma (((d:ℝ)-s)/2)) *
    ∫ ρ in Set.Ioc (0:ℝ) η, ρ^((d:ℝ)-s-1)*HeatKernel d (ρ^2) x
