module

public import Tablet.Preamble

@[expose] public section
-- [TABLET NODE: BoundedBackground]
structure BoundedBackground (d : ℕ) (lower upper : ℝ) where
-- BODY
  density : UnitAddTorus (Fin d) → ℝ
  measurable : Measurable density
  lower_pos : 0 < lower
  lower_le_one : lower ≤ 1
  one_le_upper : 1 ≤ upper
  bounds : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d))), lower ≤ density x ∧ density x ≤ upper
  mass : ∫ x, density x ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d))) = 1
