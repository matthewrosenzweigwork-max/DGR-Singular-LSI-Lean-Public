import Tablet.HeatIncrementLaw
import Tablet.HeatOperatorBounds
import Mathlib.MeasureTheory.Group.Integral
open MeasureTheory
-- [TABLET NODE: HeatIncrementAveraging]
theorem HeatIncrementAveraging (d : ℕ) (t : ℝ) (ht : 0<t) :
    IsProbabilityMeasure (HeatIncrementLaw d t) ∧
    ∀ (f : UnitAddTorus (Fin d)→ℝ), Integrable f volume → ∀x,
      (Integrable (fun z=>f (x+z)) (HeatIncrementLaw d t) ∧
       (∫z,f (x+z)∂HeatIncrementLaw d t)=HeatSemigroup d t f x) ∧
      (Integrable (fun z=>f (x-z)) (HeatIncrementLaw d t) ∧
       (∫z,f (x-z)∂HeatIncrementLaw d t)=HeatSemigroup d t f x) := by
-- BODY
  have hK := HeatKernelFacts d t ht
  have hpn := hK.2.1
  have hpe := hK.2.2.1
  have hpm := hK.2.2.2.1
  have hdm := hK.1.measurable.ennreal_ofReal
  have hdf : ∀ᵐ z∂(volume : Measure (UnitAddTorus (Fin d))), ENNReal.ofReal (HeatKernel d t z)<⊤ := Filter.Eventually.of_forall (fun z : UnitAddTorus (Fin d)=>ENNReal.ofReal_lt_top (r:=HeatKernel d t z))
  obtain ⟨C,hC⟩ := (isCompact_univ : IsCompact (Set.univ : Set (UnitAddTorus (Fin d)))).exists_bound_of_continuousOn hK.1.continuousOn
  have hpbound : ∀ᵐ z∂(volume : Measure (UnitAddTorus (Fin d))),‖HeatKernel d t z‖≤C :=
    Filter.Eventually.of_forall fun z=>hC z (Set.mem_univ z)
  have hpi : Integrable (HeatKernel d t) volume := Integrable.of_bound hK.1.measurable.aestronglyMeasurable C hpbound
  constructor
  · apply isProbabilityMeasure_iff.mpr
    unfold HeatIncrementLaw
    rw [withDensity_apply _ MeasurableSet.univ]
    simp only [Measure.restrict_univ]
    rw [←ofReal_integral_eq_lintegral_ofReal hpi (Filter.Eventually.of_forall hpn),hpm]
    simp
  · intro f hf x
    have hfi : Integrable (fun z=>HeatKernel d t z*f (x+z)) volume :=
      (hf.comp_add_left x).bdd_mul hK.1.measurable.aestronglyMeasurable hpbound
    have hsmuli : Integrable (fun z=>(ENNReal.ofReal (HeatKernel d t z)).toReal • f (x+z)) volume := by
      simpa only [ENNReal.toReal_ofReal (hpn _),smul_eq_mul] using hfi
    have hplus : Integrable (fun z=>f (x+z)) (HeatIncrementLaw d t) ∧
        (∫z,f (x+z)∂HeatIncrementLaw d t)=HeatSemigroup d t f x := by
      refine ⟨(integrable_withDensity_iff_integrable_smul' hdm hdf).mpr hsmuli,?_⟩
      unfold HeatIncrementLaw
      rw [integral_withDensity_eq_integral_toReal_smul hdm hdf]
      simp only [ENNReal.toReal_ofReal (hpn _),smul_eq_mul]
      have hh := integral_neg_eq_self (fun z:UnitAddTorus (Fin d)=>HeatKernel d t z*f (x+z)) volume
      rw [←hh]
      simp only [hpe,←sub_eq_add_neg]
      rfl
    have hminusMul : Integrable (fun z=>HeatKernel d t z*f (x-z)) volume :=
      (hf.comp_sub_left x).bdd_mul hK.1.measurable.aestronglyMeasurable hpbound
    have hminusSmul : Integrable
        (fun z=>(ENNReal.ofReal (HeatKernel d t z)).toReal • f (x-z)) volume := by
      simpa only [ENNReal.toReal_ofReal (hpn _),smul_eq_mul] using hminusMul
    refine ⟨hplus,(integrable_withDensity_iff_integrable_smul' hdm hdf).mpr hminusSmul,?_⟩
    unfold HeatIncrementLaw
    rw [integral_withDensity_eq_integral_toReal_smul hdm hdf]
    simp only [ENNReal.toReal_ofReal (hpn _),smul_eq_mul]
    rfl
