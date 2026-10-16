module

public import Tablet.ProductRestrictionLaw
public import Mathlib.Probability.Independence.Basic

@[expose] public section
open MeasureTheory ProbabilityTheory

-- [TABLET NODE: ProductDisjointBlockLaw]
theorem ProductDisjointBlockLaw {I Ω : Type*} [Fintype I] [MeasurableSpace Ω]
    (μ : I → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (s t : Finset I) (hst : Disjoint s t) :
    (Measure.pi μ).map (fun x : I → Ω => ((fun i : s => x i), (fun i : t => x i))) =
      (Measure.pi (fun i : s => μ i)).prod (Measure.pi (fun i : t => μ i)) := by
-- BODY
  classical
  have hi : iIndepFun (fun i (x : I → Ω) => x i) (Measure.pi μ) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have h := iIndepFun.indepFun_finset s t hst hi (fun i => measurable_pi_apply i)
  have hs : Measurable (fun x : I → Ω => fun i : s => x i) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply i.val
  have ht : Measurable (fun x : I → Ω => fun i : t => x i) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply i.val
  simpa only [ProductRestrictionLaw] using h.map_prod_eq_prod_map_map hs.aemeasurable ht.aemeasurable
