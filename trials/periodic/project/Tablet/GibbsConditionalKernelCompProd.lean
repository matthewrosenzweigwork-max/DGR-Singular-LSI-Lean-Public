module

public import Tablet.GibbsConditionalKernelProbability
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

@[expose] public section
open MeasureTheory ProbabilityTheory

-- [TABLET NODE: GibbsConditionalKernelCompProd]
theorem GibbsConditionalKernelCompProd {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (η : Measure Y) [IsProbabilityMeasure η]
    (U : X × Y → ℝ) (hm : Measurable U)
    (hi : ∀ x, Integrable (fun y => Real.exp (-U (x,y))) η) :
    μ ⊗ₘ GibbsConditionalKernel η U = (μ.prod η).withDensity (fun p =>
      ENNReal.ofReal (Real.exp (-U p) / (∫ z, Real.exp (-U (p.1,z)) ∂η))) := by
-- BODY
  have hz : Measurable (fun x => ∫ y,Real.exp (-U (x,y))∂η) :=
    hm.neg.exp.stronglyMeasurable.integral_prod_right'.measurable
  let f := fun x y => ENNReal.ofReal (Real.exp (-U (x,y)) / (∫ z,Real.exp (-U (x,z))∂η))
  have hd : Measurable (Function.uncurry f) :=
    (hm.neg.exp.div (hz.comp measurable_fst)).ennreal_ofReal
  haveI : IsMarkovKernel (GibbsConditionalKernel η U) := (GibbsConditionalKernelProbability η U hm hi).1
  ext s hs
  rw [Measure.compProd_apply hs, withDensity_apply _ hs]
  have hx (x : X) : MeasurableSet ((Prod.mk x) ⁻¹' s) := (measurable_const.prodMk measurable_id) hs
  simp_rw [(GibbsConditionalKernelProbability η U hm hi).2, NormalizedTilt,
    withDensity_apply _ (hx _)]
  rw [← lintegral_indicator hs]
  have hd' : Measurable (fun p : X × Y => ENNReal.ofReal (Real.exp (-U p) / (∫ z, Real.exp (-U (p.1,z)) ∂η))) := hd
  rw [lintegral_prod _ (hd'.indicator hs).aemeasurable]
  apply lintegral_congr
  intro x
  rw [← lintegral_indicator (hx x)]
  apply lintegral_congr
  intro y
  by_cases hp : (x,y) ∈ s <;> simp [Set.indicator, hp]
