module

public import Tablet.HeatKernel

@[expose] public section
open MeasureTheory
-- [TABLET NODE: DGRGaussianPhysicalLong]
noncomputable def DGRGaussianPhysicalLong (d : ℕ) (s a η : ℝ)
    (x : UnitAddTorus (Fin d)) : ℝ :=
-- BODY
  (2*a/Real.Gamma (((d:ℝ)-s)/2)) *
    ∫ ρ in Set.Ioi η, ρ^((d:ℝ)-s-1)*(HeatKernel d (ρ^2) x-1)
