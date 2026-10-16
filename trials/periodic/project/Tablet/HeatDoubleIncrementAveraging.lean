import Tablet.HeatIncrementAveraging
import Tablet.HeatSemigroupComposition
import Mathlib.MeasureTheory.Integral.Prod
open MeasureTheory
-- [TABLET NODE: HeatDoubleIncrementAveraging]
theorem HeatDoubleIncrementAveraging (d : ℕ) (t : ℝ) (ht : 0<t)
    (f : UnitAddTorus (Fin d)→ℝ) (hf : Measurable f) (hi : Integrable f volume) :
    ∀x y, Integrable (fun p:UnitAddTorus (Fin d)×UnitAddTorus (Fin d)=>f ((x+p.1)-(y+p.2)))
      ((HeatIncrementLaw d t).prod (HeatIncrementLaw d t)) ∧
    (∫p,f ((x+p.1)-(y+p.2))∂(HeatIncrementLaw d t).prod (HeatIncrementLaw d t))=
      HeatSemigroup d (t+t) f (x-y) := by
-- BODY
  have sub_average (f : UnitAddTorus (Fin d) → ℝ) (hf : Integrable f volume)
      (x : UnitAddTorus (Fin d)) := ((HeatIncrementAveraging d t ht).2 f hf x).2
  let T:=UnitAddTorus (Fin d)
  let ν:=HeatIncrementLaw d t
  haveI : IsProbabilityMeasure ν := (HeatIncrementAveraging d t ht).1
  have hK:=HeatKernelFacts d t ht
  obtain ⟨C,hC⟩ := (isCompact_univ : IsCompact (Set.univ : Set T)).exists_bound_of_continuousOn hK.1.continuousOn
  have hpbound : ∀ᵐz∂(volume : Measure T),‖HeatKernel d t z‖≤C :=
    Filter.Eventually.of_forall fun z=>hC z (Set.mem_univ z)
  have hnorm (a:T) : (∫w,‖f (a-w)‖∂ν)≤C*(∫z,‖f z‖∂volume) :=by
    rw [(sub_average _ hi.norm a).2]
    change (∫w,HeatKernel d t w*‖f (a-w)‖∂volume)≤_
    have hmul := (hi.norm.comp_sub_left a).bdd_mul hK.1.measurable.aestronglyMeasurable hpbound
    have hle : (∫w,HeatKernel d t w*‖f (a-w)‖∂volume)≤∫w,C*‖f (a-w)‖∂volume :=by
      apply integral_mono_ae hmul ((hi.norm.comp_sub_left a).const_mul C)
      exact Filter.Eventually.of_forall fun w=>mul_le_mul_of_nonneg_right
        ((le_abs_self _).trans (hC w (Set.mem_univ w))) (norm_nonneg _)
    rw [integral_const_mul] at hle
    rw [integral_sub_left_eq_self (fun z=>‖f z‖) volume a] at hle
    exact hle
  intro x y
  have he (z w:T) : (x+z)-(y+w)=(x+z-y)-w :=by abel
  have hsection (z:T) : Integrable (fun w=>f ((x+z)-(y+w))) ν :=by
    simpa only [he] using (sub_average f hi (x+z-y)).1
  have houter : Integrable (fun z=>∫w,‖f ((x+z)-(y+w))‖∂ν) ν :=by
    have hm : Measurable (fun p:T×T=>‖f ((x+p.1)-(y+p.2))‖):=by fun_prop
    apply Integrable.of_bound hm.stronglyMeasurable.integral_prod_right.aestronglyMeasurable
      (C*(∫w,‖f w‖∂volume))
    exact Filter.Eventually.of_forall fun z=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg fun _=>norm_nonneg _)]
      simpa only [he] using hnorm (x+z-y)
  have hj : Measurable (fun p:T×T=>f ((x+p.1)-(y+p.2))):=by fun_prop
  have hprod : Integrable (fun p:T×T=>f ((x+p.1)-(y+p.2))) (ν.prod ν) :=
    (integrable_prod_iff hj.aestronglyMeasurable).mpr ⟨Filter.Eventually.of_forall hsection,houter⟩
  refine ⟨hprod,?_⟩
  rw [integral_prod _ hprod]
  have hinner : (fun z:T=>∫w,f ((x+z)-(y+w))∂ν)=fun z=>HeatSemigroup d t f ((x-y)+z) :=by
    funext z
    simpa only [he,show x+z-y=(x-y)+z by abel] using
      (sub_average f hi (x+z-y)).2
  rw [hinner]
  have hPi := (HeatOperatorBounds d t ht f hf hi).2.1
  rw [((HeatIncrementAveraging d t ht).2 _ hPi (x-y)).1.2]
  exact HeatSemigroupComposition d t t ht ht f hi (x-y)
