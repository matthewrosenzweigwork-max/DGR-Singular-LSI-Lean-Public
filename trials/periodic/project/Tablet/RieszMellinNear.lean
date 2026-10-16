module

public import Tablet.RieszKernel

@[expose] public section
open MeasureTheory
-- [TABLET NODE: RieszMellinNear]
noncomputable def RieszMellinNear (d:ℕ) (s a δ ε:ℝ) (x:UnitAddTorus (Fin d)) : ℝ :=
-- BODY
  a / Real.Gamma (((d:ℝ)-s)/2) *
    ∫t in Set.Ioc (0:ℝ) δ,t^(((d:ℝ)-s)/2-1)*HeatKernel d (t+ε) x
