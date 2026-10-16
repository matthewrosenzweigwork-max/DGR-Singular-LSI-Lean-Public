import Tablet.ProductConditionalEntropyTensorization
import Tablet.ConditionalGibbsRelativeEntropy
import Tablet.ThermalNormalizerJensen
open MeasureTheory InformationTheory

-- [TABLET NODE: CenteredInteractionEntropyLower]
theorem CenteredInteractionEntropyLower {I Ω : Type*}
    [Fintype I] [DecidableEq I] [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    (μ : I → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (S : Measure (I → Ω)) [IsProbabilityMeasure S] (hS : klDiv S (Measure.pi μ) ≠ ⊤)
    (V : (I → Ω) → ℝ) (hmV : Measurable V) (D : ℝ) (hD : ∀ x, |V x| ≤ D)
    (U : (i : I) → (((Finset.univ : Finset I).erase i → Ω) × (({i} : Finset I) → Ω)) → ℝ)
    (hmU : ∀ i, Measurable (U i)) (C : ℝ) (hC : ∀ i p, |U i p| ≤ C)
    (hcenter : ∀ i x, (∫ y, U i (x,y) ∂Measure.pi (fun j : ({i} : Finset I) => μ j)) = 0)
    (hpair : ∀ x : I → Ω, (∑ i : I, U i ((fun j => x j), (fun j => x j))) = 2 * V x) :
    let T := fun i : I => S.map (fun x : I → Ω =>
      ((fun j : (Finset.univ : Finset I).erase i => x j), (fun j : ({i} : Finset I) => x j)))
    let z := fun (i : I) x => ∫ y, Real.exp (-U i (x,y)) ∂Measure.pi (fun j : ({i} : Finset I) => μ j)
    let R := fun i : I => ((T i).fst.prod (Measure.pi (fun j : ({i} : Finset I) => μ j))).withDensity
      (fun p => ENNReal.ofReal (Real.exp (-U i p) / z i p.1))
    let P := NormalizedTilt (Measure.pi μ) (fun x => Real.exp (-V x))
    (klDiv S P).toReal ≤ 2 * (∑ i : I, (klDiv (T i) (R i)).toReal) +
      Real.log (∫ x, Real.exp (-V x) ∂Measure.pi μ) +
      Real.log (∫ x, Real.exp (-(3 * V x)) ∂Measure.pi μ) := by
-- BODY
  classical
  let F := fun (i : I) (x : I → Ω) =>
    ((fun j : (Finset.univ : Finset I).erase i => x j), (fun j : ({i} : Finset I) => x j))
  have hmF (i : I) : Measurable (F i) :=
    (measurable_pi_lambda _ fun j => measurable_pi_apply j.val).prodMk
      (measurable_pi_lambda _ fun j => measurable_pi_apply j.val)
  let T := fun i => S.map (F i)
  have hpT (i : I) : IsProbabilityMeasure (T i) := Measure.isProbabilityMeasure_map (hmF i).aemeasurable
  let η := fun i => Measure.pi (fun j : ({i} : Finset I) => μ j)
  let z := fun (i : I) x => ∫ y, Real.exp (-U i (x,y)) ∂η i
  let R := fun i => ((T i).fst.prod (η i)).withDensity
    (fun p => ENNReal.ofReal (Real.exp (-U i p) / z i p.1))
  let H := (klDiv S (Measure.pi μ)).toReal
  let A := ∫ x, V x ∂S
  let L := fun i => (klDiv (T i) ((T i).fst.prod (η i))).toReal
  have ht (i : I) : (T i).fst = S.map (fun x : I → Ω => fun j : (Finset.univ : Finset I).erase i => x j) := by
    rw [Measure.fst, Measure.map_map measurable_fst (hmF i)]
    rfl
  have hfin (i : I) : klDiv (T i) ((T i).fst.prod (η i)) ≠ ⊤ := by
    have hh := ProductDeletionConditionalEntropy μ S i
    change klDiv S (Measure.pi μ) =
      klDiv (S.map (fun x : I → Ω => fun j : (Finset.univ : Finset I).erase i => x j))
        (Measure.pi (fun j : (Finset.univ : Finset I).erase i => μ j)) +
      klDiv (T i) ((S.map (fun x : I → Ω => fun j : (Finset.univ : Finset I).erase i => x j)).prod (η i)) at hh
    rw [← ht i] at hh
    exact (ENNReal.add_ne_top.mp (hh ▸ hS)).2
  have hbound (i : I) : L i + ∫ p, U i p ∂T i ≤ (klDiv (T i) (R i)).toReal := by
    haveI := hpT i
    obtain ⟨hb,_,_,he⟩ := ConditionalGibbsRelativeEntropy (T i) (η i) (U i) (hmU i) C (hC i) (hfin i)
    have hz (x) : 1 ≤ z i x := by
      have hm : Measurable (fun y => U i (x,y)) := (hmU i).comp (measurable_const.prodMk measurable_id)
      have hi : Integrable (fun y => U i (x,y)) (η i) := by
        apply (integrable_const C).mono' hm.aestronglyMeasurable
        exact Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hC i (x,y)
      have he : Integrable (fun y => Real.exp (-U i (x,y))) (η i) := by
        apply (integrable_const (Real.exp C)).mono' hm.neg.exp.aestronglyMeasurable
        exact Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          apply Real.exp_le_exp.mpr
          change -U i (x,y) ≤ C
          have hh := (abs_le.mp (hC i (x,y))).1
          linarith
      have hh := ThermalNormalizerJensen (η i) (fun _ => 1) (fun y => U i (x,y)) 1
        (Filter.Eventually.of_forall fun _ => zero_le_one) (integrable_const 1)
        (by simp) (by simpa only [one_mul] using hi)
        (by simpa only [one_mul, neg_mul] using he)
      have hz0 : (∫ y, U i (x,y) ∂η i) = 0 := hcenter i x
      simpa only [one_mul, integral_const, probReal_univ, smul_eq_mul, hz0, mul_zero,
        neg_zero, neg_one_mul, Real.exp_zero] using hh
    have hl : 0 ≤ ∫ p, Real.log (z i p.1) ∂T i :=
      integral_nonneg fun p => Real.log_nonneg (hz p.1)
    change (klDiv (T i) (R i)).toReal = L i + (∫ p,U i p∂T i) + (∫ p,Real.log (z i p.1)∂T i) at he
    linarith
  have hu (i : I) : Integrable (fun x => U i (F i x)) S := by
    apply (integrable_const C).mono' ((hmU i).comp (hmF i)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs, Function.comp_apply] using hC i (F i x)
  have hsumU : (∑ i : I, ∫ p,U i p∂T i) = 2*A := by
    have hh (i : I) : (∫ p,U i p∂T i) = ∫ x,U i (F i x)∂S := by
      exact integral_map (hmF i).aemeasurable (hmU i).aestronglyMeasurable
    simp_rw [hh]
    rw [← integral_finset_sum _ (fun i _ => hu i)]
    simp_rw [show ∀ x, (∑ i : I, U i (F i x)) = 2*V x from hpair]
    exact integral_const_mul 2 V
  have hb := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) => hbound i)
  rw [Finset.sum_add_distrib, hsumU] at hb
  have hlower : H+2*A ≤ ∑ i : I,(klDiv (T i) (R i)).toReal := by
    have hs' : H ≤ ∑ i : I,L i := by
      simpa only [L, T, F, η, ht] using ProductConditionalEntropyTensorization μ S hS
    linarith
  obtain ⟨_,_,_,h1⟩ := BoundedGibbsRelativeEntropy (Measure.pi μ) S V hmV D hD hS
  have h3b : ∀ x, |3*V x| ≤ 3*D := fun x => by simpa [abs_mul] using mul_le_mul_of_nonneg_left (hD x) (by norm_num : (0:ℝ)≤3)
  obtain ⟨_,_,_,h3⟩ := BoundedGibbsRelativeEntropy (Measure.pi μ) S (fun x => 3*V x)
    (measurable_const.mul hmV) (3*D) h3b hS
  have h3n := ENNReal.toReal_nonneg (a := klDiv S (NormalizedTilt (Measure.pi μ) (fun x => Real.exp (-(3*V x)))))
  rw [h3, integral_const_mul] at h3n
  dsimp only
  change (klDiv S (NormalizedTilt (Measure.pi μ) (fun x => Real.exp (-V x)))).toReal ≤ _
  rw [h1]
  change H+A+_ ≤ 2*(∑ i : I,(klDiv (T i) (R i)).toReal)+_+_
  linarith
