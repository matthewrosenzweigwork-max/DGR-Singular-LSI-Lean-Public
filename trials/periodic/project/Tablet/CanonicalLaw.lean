module

public import Tablet.GibbsWeight
public import Tablet.NormalizedTilt
public import Tablet.Configuration

@[expose] public section
-- [TABLET NODE: CanonicalLaw]
noncomputable def CanonicalLaw {d N : ℕ} (g q : UnitAddTorus (Fin d) → ℝ)
    (β : ℝ) : MeasureTheory.Measure (Configuration d N) :=
-- BODY
  NormalizedTilt (MeasureTheory.volume : MeasureTheory.Measure (Configuration d N)) (GibbsWeight g q β)
