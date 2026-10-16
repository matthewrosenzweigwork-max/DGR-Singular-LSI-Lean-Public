import Tablet.ProductDisjointBlockLaw
import Tablet.RelativeEntropyUnderMeasurableEquivalence
open MeasureTheory InformationTheory

-- [TABLET NODE: DisjointBlockMarginalEntropy]
theorem DisjointBlockMarginalEntropy {I Ω : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Ω]
    (μ : I → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (S : Measure (I → Ω)) [IsProbabilityMeasure S]
    (s t : Finset I) (hst : Disjoint s t) :
    klDiv (S.map (fun x : I → Ω => ((fun i : s => x i), (fun i : t => x i))))
      ((Measure.pi (fun i : s => μ i)).prod (Measure.pi (fun i : t => μ i))) =
    klDiv (S.map (fun x : I → Ω => fun i : ↥(s ∪ t) => x i))
      (Measure.pi (fun i : ↥(s ∪ t) => μ i)) := by
-- BODY
  classical
  let F : (I → Ω) → (s → Ω) × (t → Ω) := fun x => ((fun i => x i), (fun i => x i))
  let R : (I → Ω) → (↥(s ∪ t) → Ω) := fun x i => x i
  let e : ((s → Ω) × (t → Ω)) ≃ᵐ (↥(s ∪ t) → Ω) :=
    MeasurableEquiv.piFinsetUnion (π := fun _ : I => Ω) hst
  have hm : Measurable F :=
    (measurable_pi_lambda _ fun i => measurable_pi_apply i.val).prodMk
      (measurable_pi_lambda _ fun i => measurable_pi_apply i.val)
  have he : e ∘ F = R := by
    funext x i
    change Equiv.piFinsetUnion (fun _ : I => Ω) hst (F x) i = x i
    by_cases hi : i.val ∈ s
    · exact Equiv.piFinsetUnion_left (fun _ : I => Ω) hst hi i.property
    · exact Equiv.piFinsetUnion_right (fun _ : I => Ω) hst
        ((Finset.mem_union.mp i.property).resolve_left hi) i.property
  have hP : (Measure.pi μ).map F =
      (Measure.pi (fun i : s => μ i)).prod (Measure.pi (fun i : t => μ i)) :=
    ProductDisjointBlockLaw μ s t hst
  have hRef : ((Measure.pi (fun i : s => μ i)).prod (Measure.pi (fun i : t => μ i))).map e =
      Measure.pi (fun i : ↥(s ∪ t) => μ i) := by
    rw [← hP, Measure.map_map e.measurable hm, he]
    exact ProductRestrictionLaw μ (s ∪ t)
  have hh := RelativeEntropyUnderMeasurableEquivalence (S.map F)
    ((Measure.pi (fun i : s => μ i)).prod (Measure.pi (fun i : t => μ i))) e
  rw [Measure.map_map e.measurable hm, he, hRef] at hh
  exact hh.symm
