import Tablet.Preamble
import Mathlib.MeasureTheory.Constructions.Pi
open MeasureTheory

-- [TABLET NODE: ProductRestrictionLaw]
theorem ProductRestrictionLaw {I Ω : Type*} [Fintype I] [MeasurableSpace Ω]
    (μ : I → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] (s : Finset I) :
    (Measure.pi μ).map (fun x : I → Ω => fun i : s => x i) =
      Measure.pi (fun i : s => μ i) := by
-- BODY
  classical
  have hp := measurePreserving_piEquivPiSubtypeProd (α := fun _ : I => Ω) μ (fun i => i ∈ s)
  have hh := congrArg (fun ν => ν.map Prod.fst) hp.map_eq
  rw [Measure.map_map measurable_fst hp.measurable, Measure.map_fst_prod, measure_univ, one_smul] at hh
  convert! hh using 1
  congr 1
  exact Subsingleton.elim _ _
