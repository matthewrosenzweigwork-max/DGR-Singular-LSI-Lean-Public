import Tablet.RieszKernel
open MeasureTheory
-- [TABLET NODE: RieszMellinCoefficient]
noncomputable def RieszMellinCoefficient (d:ℕ) (s a δ ε:ℝ) (k:Fin d→ℤ):ℝ:=
-- BODY
  if k=0 then 0 else a/Real.Gamma (((d:ℝ)-s)/2)*
    ∫t in Set.Ioi δ,t^(((d:ℝ)-s)/2-1)*
      Real.exp (-4*Real.pi^2*(t+ε)*∑j,(k j:ℝ)^2)
