module

public import Tablet.RieszKernel

@[expose] public section
open MeasureTheory
-- [TABLET NODE: RieszMellinLong]
noncomputable def RieszMellinLong (d:ℕ) (s a δ ε:ℝ) (x:UnitAddTorus (Fin d)) : ℝ :=
-- BODY
  a / Real.Gamma (((d:ℝ)-s)/2) *
    ∫t in Set.Ioi δ,t^(((d:ℝ)-s)/2-1)*(HeatKernel d (t+ε) x-1)
