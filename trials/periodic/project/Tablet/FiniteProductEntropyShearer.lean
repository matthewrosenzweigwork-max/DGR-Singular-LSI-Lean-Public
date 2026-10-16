import Tablet.DisjointBlockMarginalEntropy
import Tablet.EntropyObservationSupermodularity
open MeasureTheory InformationTheory

-- [TABLET NODE: FiniteProductEntropyShearer]
theorem FiniteProductEntropyShearer {I Ω : Type*}
    [Fintype I] [DecidableEq I] [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    (μ : I → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (S : Measure (I → Ω)) [IsProbabilityMeasure S]
    (hS : klDiv S (Measure.pi μ) ≠ ⊤) (s : Finset I) :
    (∑ i ∈ s, (klDiv (S.map (fun x : I → Ω => fun j : s.erase i => x j))
      (Measure.pi (fun j : s.erase i => μ j))).toReal) ≤
    ((s.card : ℝ)-1) * (klDiv (S.map (fun x : I → Ω => fun j : s => x j))
      (Measure.pi (fun j : s => μ j))).toReal := by
-- BODY
  have union_law_local    
      (μ : I → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
      (s t : Finset I) (hst : Disjoint s t) :
      let e := MeasurableEquiv.piFinsetUnion (π := fun _ : I => Ω) hst
      (∀ x : I → Ω, e ((fun i : s => x i), (fun i : t => x i)) = fun i : ↥(s ∪ t) => x i) ∧
      ((Measure.pi (fun i : ↥(s ∪ t) => μ i)).map e.symm =
        (Measure.pi (fun i : s => μ i)).prod (Measure.pi (fun i : t => μ i))) := by

    classical
    let e : ((s → Ω) × (t → Ω)) ≃ᵐ (↥(s ∪ t) → Ω) :=
      MeasurableEquiv.piFinsetUnion (π := fun _ : I => Ω) hst
    let F : (I → Ω) → (s → Ω) × (t → Ω) := fun x => ((fun i => x i), (fun i => x i))
    let R : (I → Ω) → (↥(s ∪ t) → Ω) := fun x i => x i
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
    refine ⟨fun x => congrFun he x, ?_⟩
    have hP : (Measure.pi μ).map F =
        (Measure.pi (fun i : s => μ i)).prod (Measure.pi (fun i : t => μ i)) :=
      ProductDisjointBlockLaw μ s t hst
    have hRef : ((Measure.pi (fun i : s => μ i)).prod (Measure.pi (fun i : t => μ i))).map e =
        Measure.pi (fun i : ↥(s ∪ t) => μ i) := by
      rw [← hP, Measure.map_map e.measurable hm, he]
      exact ProductRestrictionLaw μ (s ∪ t)
    rw [← hRef, MeasurableEquiv.map_symm_map]
  have three_observation_local (s t u : Finset I)
      (S : Measure (((s → Ω) × (t → Ω)) × (u → Ω))) (μ : Measure (s → Ω)) (ν : Measure (t → Ω)) (η : Measure (u → Ω))
      [IsProbabilityMeasure S] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure η] :
      klDiv S.fst (μ.prod ν) + klDiv (S.map (fun p => (p.1.1,p.2))) (μ.prod η) ≤
        klDiv S ((μ.prod ν).prod η) + klDiv S.fst.fst μ := by

    have hh := EntropyObservationSupermodularity S (μ.prod ν) η Prod.fst measurable_fst
    simp only [Measure.map_fst_prod, measure_univ, one_smul] at hh
    convert! hh using 1
  have triple_entropy_local    
      (μ : I → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
      (S : Measure (I → Ω)) [IsProbabilityMeasure S]
      (s t u : Finset I) (hst : Disjoint s t) (hstu : Disjoint (s ∪ t) u) :
      klDiv (S.map (fun x : I → Ω => (((fun i : s => x i), (fun i : t => x i)), (fun i : u => x i))))
        (((Measure.pi (fun i : s => μ i)).prod (Measure.pi (fun i : t => μ i))).prod
          (Measure.pi (fun i : u => μ i))) =
      klDiv (S.map (fun x : I → Ω => fun i : ↥((s ∪ t) ∪ u) => x i))
        (Measure.pi (fun i : ↥((s ∪ t) ∪ u) => μ i)) := by

    classical
    let e := MeasurableEquiv.piFinsetUnion (π := fun _ : I => Ω) hst
    let E := MeasurableEquiv.prodCongr e.symm (MeasurableEquiv.refl (u → Ω))
    let F : (I → Ω) → (↥(s ∪ t) → Ω) × (u → Ω) := fun x => ((fun i => x i), (fun i => x i))
    have hm : Measurable F :=
      (measurable_pi_lambda _ fun i => measurable_pi_apply i.val).prodMk
        (measurable_pi_lambda _ fun i => measurable_pi_apply i.val)
    have hp := union_law_local μ s t hst
    have he : E ∘ F = fun x : I → Ω => (((fun i : s => x i), (fun i : t => x i)), (fun i : u => x i)) := by
      funext x
      apply Prod.ext
      · change e.symm (fun i : ↥(s ∪ t) => x i) = ((fun i : s => x i), (fun i : t => x i))
        rw [← hp.1 x]
        exact e.symm_apply_apply _
      · rfl
    have hr : (((Measure.pi (fun i : ↥(s ∪ t) => μ i)).prod (Measure.pi (fun i : u => μ i))).map E) =
        ((Measure.pi (fun i : s => μ i)).prod (Measure.pi (fun i : t => μ i))).prod
          (Measure.pi (fun i : u => μ i)) := by
      change (((Measure.pi (fun i : ↥(s ∪ t) => μ i)).prod (Measure.pi (fun i : u => μ i))).map (Prod.map e.symm id)) = _
      rw [← Measure.map_prod_map _ _ e.symm.measurable measurable_id, hp.2, Measure.map_id]
    have hh := RelativeEntropyUnderMeasurableEquivalence (S.map F)
      ((Measure.pi (fun i : ↥(s ∪ t) => μ i)).prod (Measure.pi (fun i : u => μ i))) E
    rw [Measure.map_map E.measurable hm, he, hr] at hh
    exact hh.trans (DisjointBlockMarginalEntropy μ S (s ∪ t) u hstu)
  have coordinate_supermod_local 
          
      (μ : I → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
      (S : Measure (I → Ω)) [IsProbabilityMeasure S]
      (s t u : Finset I) (hst : Disjoint s t) (hstu : Disjoint (s ∪ t) u) :
      let H := fun v : Finset I => klDiv (S.map (fun x : I → Ω => fun i : v => x i)) (Measure.pi (fun i : v => μ i))
      H (s ∪ t) + H (s ∪ u) ≤ H ((s ∪ t) ∪ u) + H s := by

    classical
    let F : (I → Ω) → ((s → Ω) × (t → Ω)) × (u → Ω) :=
      fun x => (((fun i => x i), (fun i => x i)), (fun i => x i))
    have hm : Measurable F :=
      ((measurable_pi_lambda _ fun i => measurable_pi_apply i.val).prodMk
        (measurable_pi_lambda _ fun i => measurable_pi_apply i.val)).prodMk
        (measurable_pi_lambda _ fun i => measurable_pi_apply i.val)
    let T := S.map F
    haveI : IsProbabilityMeasure T := Measure.isProbabilityMeasure_map hm.aemeasurable
    have hh := three_observation_local s t u T (Measure.pi (fun i : s => μ i))
      (Measure.pi (fun i : t => μ i)) (Measure.pi (fun i : u => μ i))
    have hfst : T.fst = S.map (fun x : I → Ω => ((fun i : s => x i), (fun i : t => x i))) := by
      rw [Measure.fst, Measure.map_map measurable_fst hm]
      rfl
    have hxz : T.map (fun p => (p.1.1,p.2)) = S.map (fun x : I → Ω => ((fun i : s => x i), (fun i : u => x i))) := by
      rw [Measure.map_map (measurable_fst.fst.prodMk measurable_snd) hm]
      rfl
    have hsf : T.fst.fst = S.map (fun x : I → Ω => fun i : s => x i) := by
      rw [hfst, Measure.fst, Measure.map_map measurable_fst
        ((measurable_pi_lambda _ fun i => measurable_pi_apply i.val).prodMk
          (measurable_pi_lambda _ fun i => measurable_pi_apply i.val))]
      rfl
    have hsu : Disjoint s u := (Finset.disjoint_union_left.mp hstu).1
    rw [hsf, hfst, hxz, DisjointBlockMarginalEntropy μ S s t hst,
      DisjointBlockMarginalEntropy μ S s u hsu] at hh
    have hj := triple_entropy_local μ S s t u hst hstu
    change klDiv T _ = _ at hj
    rw [hj] at hh
    exact hh

  classical
  let E := fun v : Finset I => klDiv (S.map (fun x : I → Ω => fun j : v => x j))
    (Measure.pi (fun j : v => μ j))
  let H := fun v : Finset I => (E v).toReal
  have hfin (v : Finset I) : E v ≠ ⊤ := by
    have hm : Measurable (fun x : I → Ω => fun j : v => x j) :=
      measurable_pi_lambda _ fun j => measurable_pi_apply j.val
    have hh := klDiv_map_le S (Measure.pi μ) hm
    rw [ProductRestrictionLaw μ v] at hh
    exact ne_top_of_le_ne_top hS hh
  have hzero : H ∅ = 0 := by
    let z : (∅ : Finset I) → Ω := Classical.choice inferInstance
    have he : (fun x : I → Ω => fun j : (∅ : Finset I) => x j) = fun _ => z :=
      funext fun _ => Subsingleton.elim _ _
    dsimp [H, E]
    rw [← ProductRestrictionLaw μ ∅, he]
    simp [Measure.map_const]
  have hlocal (a : I) (v : Finset I) (ha : a ∉ v) (i : I) (hi : i ∈ v) :
      H (insert a (v.erase i)) ≤ H (insert a v)-H v+H (v.erase i) := by
    have hdi : Disjoint (v.erase i) ({i} : Finset I) := by simp
    have hvi : v.erase i ∪ ({i} : Finset I) = v := by
      rw [Finset.union_singleton, Finset.insert_erase hi]
    have hda : Disjoint (v.erase i ∪ ({i} : Finset I)) ({a} : Finset I) := by
      rw [hvi]
      simpa using ha
    have hh := coordinate_supermod_local μ S (v.erase i) {i} {a} hdi hda
    change E (v.erase i ∪ {i}) + E (v.erase i ∪ {a}) ≤
      E ((v.erase i ∪ {i}) ∪ {a}) + E (v.erase i) at hh
    rw [hvi, Finset.union_singleton, Finset.union_singleton] at hh
    have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin (insert a v), hfin (v.erase i)⟩) hh
    rw [ENNReal.toReal_add (hfin v) (hfin (insert a (v.erase i))),
      ENNReal.toReal_add (hfin (insert a v)) (hfin (v.erase i))] at hr
    change H v + H (insert a (v.erase i)) ≤ H (insert a v)+H (v.erase i) at hr
    linarith
  change (∑ i ∈ s, H (s.erase i)) ≤ ((s.card : ℝ)-1)*H s
  induction s using Finset.induction_on with
  | empty => simp [hzero]
  | @insert a v ha ih =>
    have hsum := Finset.sum_le_sum (fun i hi => hlocal a v ha i hi)
    have hdecomp : (∑ i ∈ insert a v, H ((insert a v).erase i)) =
        H v + ∑ i ∈ v, H (insert a (v.erase i)) := by
      rw [Finset.sum_insert ha, Finset.erase_insert ha]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.erase_insert_of_ne (by intro he; subst i; exact ha hi)]
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
    rw [hdecomp, Finset.card_insert_of_notMem ha]
    push_cast
    nlinarith
