module

public import Tablet.Preamble
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.MeasurableIntegral
public import Mathlib.MeasureTheory.Measure.WithDensity

@[expose] public section
universe u
open MeasureTheory ProbabilityTheory
-- [TABLET NODE: KernelWeightedFirstMarginal]
theorem KernelWeightedFirstMarginal {X Y:Type u}[MeasurableSpace X][MeasurableSpace Y]
    (μ:Measure X)[IsProbabilityMeasure μ](κ:Kernel X Y)[IsMarkovKernel κ]
    (w:X×Y→ℝ)(hw:Measurable w)(M:ℝ)(hb:∀p,0≤w p∧w p≤M) :
    ((μ⊗ₘκ).withDensity (fun p=>ENNReal.ofReal (w p))).fst=
      μ.withDensity (fun x=>ENNReal.ofReal (∫y,w (x,y)∂κ x)) := by
-- BODY
  ext A hA
  rw[Measure.fst_apply hA,←Set.prod_univ,withDensity_apply _ (hA.prod MeasurableSet.univ),
    withDensity_apply _ hA]
  rw[Measure.setLIntegral_compProd hw.ennreal_ofReal hA MeasurableSet.univ]
  simp only[Measure.restrict_univ]
  apply lintegral_congr
  intro x
  have hwi:Integrable (fun y=>w (x,y)) (κ x):=by
    apply (integrable_const M).mono' (hw.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun y=>by
      change ‖w (x,y)‖≤M
      rw[Real.norm_eq_abs,abs_of_nonneg (hb (x,y)).1]
      exact (hb (x,y)).2
  exact (ofReal_integral_eq_lintegral_ofReal hwi (Filter.Eventually.of_forall fun y=>(hb (x,y)).1)).symm
