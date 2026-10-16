module

public import Tablet.SplitCoordinateEquivalence
public import Tablet.StationaryKernelDisintegration

@[expose] public section
universe u
open MeasureTheory ProbabilityTheory

-- [TABLET NODE: SplitStationarityTransfer]
theorem SplitStationarityTransfer {I Ω : Type u} [Fintype I] [DecidableEq I]
    [MeasurableSpace Ω] (i : I) (P : Measure (I → Ω)) [IsProbabilityMeasure P]
    (κ : Kernel (((Finset.univ : Finset I).erase i) → Ω) (({i} : Finset I) → Ω))
    [IsMarkovKernel κ] (K : (I → Ω) → Measure Ω)
    (hproj : ∀ x, (κ (fun j => x j)).map
      (MeasurableEquiv.funUnique ({i} : Finset I) Ω) = K x)
    (hrow : ∀ F : (I → Ω) → ℝ, Measurable F → (∃ C : ℝ, ∀ x, |F x| ≤ C) →
      Integrable (fun x => ∫ z, F (Function.update x i z) ∂K x) P ∧
      (∫ x, ∫ z, F (Function.update x i z) ∂K x ∂P) = ∫ x, F x ∂P) :
    let S := P.map (SplitCoordinateEquivalence i)
    S = S.fst ⊗ₘ κ := by
-- BODY
  have replacement_eval_local    
      (x : I → Ω) (i : I) (z : Ω) :
      SplitCoordinateEquivalence i (Function.update x i z) =
        ((fun j : (Finset.univ : Finset I).erase i => x j),(fun _ : ({i} : Finset I) => z)) ∧
      (SplitCoordinateEquivalence i).symm
        ((fun j : (Finset.univ : Finset I).erase i => x j),(fun _ : ({i} : Finset I) => z)) =
        Function.update x i z := by

    classical
    have hf : SplitCoordinateEquivalence i (Function.update x i z) =
        ((fun j : (Finset.univ : Finset I).erase i => x j),(fun _ : ({i} : Finset I) => z)) := by
      change ((fun j : (Finset.univ : Finset I).erase i => Function.update x i z j),
        (fun j : ({i} : Finset I) => Function.update x i z j)) = _
      apply Prod.ext
      · funext j
        exact Function.update_of_ne (Finset.ne_of_mem_erase j.property) z x
      · funext j
        have hj : j.val=i := Finset.mem_singleton.mp j.property
        change Function.update x i z j.val = z
        rw [hj,Function.update_self]
    refine ⟨hf,?_⟩
    apply (SplitCoordinateEquivalence i).injective
    rw [MeasurableEquiv.apply_symm_apply]
    exact hf.symm

  classical
  let e := SplitCoordinateEquivalence (Ω := Ω) i
  let a := MeasurableEquiv.funUnique ({i} : Finset I) Ω
  let S := P.map e
  haveI : IsProbabilityMeasure S := Measure.isProbabilityMeasure_map e.measurable.aemeasurable
  apply StationaryKernelDisintegration S κ
  intro F hmF hbF
  let G := fun x => ∫ y, F (x,y) ∂κ x
  have hmG : Measurable G := hmF.stronglyMeasurable.integral_kernel_prod_right'.measurable
  have hid (x : I → Ω) : G (fun j => x j) = ∫ z, F (e (Function.update x i z)) ∂K x := by
    rw [← hproj x]
    have hm : Measurable (fun z => F (e (Function.update x i z))) := by
      have heq : (fun z => F (e (Function.update x i z))) =
          (fun z => F ((fun j => x j),(fun _ : ({i} : Finset I) => z))) := by
        funext z
        rw [(replacement_eval_local x i z).1]
      rw [heq]
      exact hmF.comp (measurable_const.prodMk (measurable_pi_lambda _ (fun _ => measurable_id)))
    rw [integral_map a.measurable.aemeasurable hm.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [] with y
    have hrepl := (replacement_eval_local x i (a y)).1
    have hconst : (fun _ : ({i} : Finset I) => a y) = y := by
      funext j
      have hj : j = default := Subsingleton.elim _ _
      subst j
      rfl
    rw [hrepl,hconst]
  obtain ⟨hFi,heq⟩ := hrow (fun x => F (e x)) (hmF.comp e.measurable) ⟨hbF.choose,fun x => hbF.choose_spec (e x)⟩
  have hGi : Integrable (fun x => G (e x).1) P := by
    apply hFi.congr
    exact Filter.Eventually.of_forall fun x => (hid x).symm
  have hGiS : Integrable (fun p => G p.1) S := by
    exact (integrable_map_measure (hmG.comp measurable_fst).aestronglyMeasurable e.measurable.aemeasurable).mpr hGi
  refine ⟨hGiS,?_⟩
  have hmGF : Measurable (fun p : ((Finset.univ : Finset I).erase i → Ω) × (({i} : Finset I) → Ω) => G p.1) := hmG.comp measurable_fst
  rw [integral_map e.measurable.aemeasurable hmGF.aestronglyMeasurable,
    integral_map e.measurable.aemeasurable hmF.aestronglyMeasurable]
  change (∫ x, G (e x).1 ∂P) = ∫ x, F (e x) ∂P
  rw [← heq]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => hid x
