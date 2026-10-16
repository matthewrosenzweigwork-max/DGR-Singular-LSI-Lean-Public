import Tablet.HeatKernel
-- [TABLET NODE: RieszKernel]
noncomputable def RieszKernel (d : ℕ) (s a ε : ℝ) (x : UnitAddTorus (Fin d)) : ℝ :=
-- BODY
  if ε = 0 ∧ x = 0 then 0 else
    a / Real.Gamma (((d : ℝ) - s) / 2) *
      ∫ t in Set.Ioi (0 : ℝ),
        Real.rpow t (((d : ℝ) - s) / 2 - 1) * (HeatKernel d (t + ε) x - 1)
