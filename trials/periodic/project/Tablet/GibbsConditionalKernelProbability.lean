module

public import Tablet.GibbsConditionalKernel
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Tilted

@[expose] public section
open MeasureTheory ProbabilityTheory

-- [TABLET NODE: GibbsConditionalKernelProbability]
theorem GibbsConditionalKernelProbability {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (η : Measure Y) [IsProbabilityMeasure η] (U : X × Y → ℝ) (hm : Measurable U)
    (hi : ∀ x, Integrable (fun y => Real.exp (-U (x,y))) η) :
    IsMarkovKernel (GibbsConditionalKernel η U) ∧
      ∀ x, GibbsConditionalKernel η U x = NormalizedTilt η (fun y => Real.exp (-U (x,y))) := by
-- BODY
  have hz : Measurable (fun x => ∫ y,Real.exp (-U (x,y))∂η) :=
    hm.neg.exp.stronglyMeasurable.integral_prod_right'.measurable
  have hd : Measurable (Function.uncurry (fun x y =>
      ENNReal.ofReal (Real.exp (-U (x,y)) / (∫ z,Real.exp (-U (x,z))∂η)))) :=
    (hm.neg.exp.div (hz.comp measurable_fst)).ennreal_ofReal
  have he (x : X) : GibbsConditionalKernel η U x = NormalizedTilt η (fun y => Real.exp (-U (x,y))) := by
    unfold GibbsConditionalKernel
    rw [Kernel.withDensity_apply _ hd]
    rfl
  refine ⟨⟨fun x => ?_⟩,he⟩
  rw [he x]
  exact isProbabilityMeasure_tilted (hi x)
