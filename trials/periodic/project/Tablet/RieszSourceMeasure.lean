module

public import Tablet.RieszKernel

@[expose] public section
-- [TABLET NODE: RieszSourceMeasure]
noncomputable def RieszSourceMeasure (d : ℕ) (s a a₂ M : ℝ) :
    MeasureTheory.Measure (UnitAddTorus (Fin d)) :=
-- BODY
  if s < (d : ℝ) - 2 then
    (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d))).withDensity
      (fun x => ENNReal.ofReal ((a / a₂) * RieszKernel d (s + 2) a₂ 0 x + M))
  else ENNReal.ofReal a • MeasureTheory.Measure.dirac 0
