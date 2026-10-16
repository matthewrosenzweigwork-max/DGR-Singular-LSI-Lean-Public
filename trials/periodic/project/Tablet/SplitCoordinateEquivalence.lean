module

public import Tablet.Preamble
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section
open MeasureTheory

-- [TABLET NODE: SplitCoordinateEquivalence]
noncomputable def SplitCoordinateEquivalence {I Ω : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace Ω] (i : I) :
    (I → Ω) ≃ᵐ (((Finset.univ : Finset I).erase i → Ω) × (({i} : Finset I) → Ω)) := by
-- BODY
  classical
  exact {
    toEquiv := {
      toFun := fun x => ((fun j => x j), (fun j => x j))
      invFun := fun p k => if hk : k = i then p.2 ⟨i, by simp⟩ else p.1 ⟨k, by simp [hk]⟩
      left_inv := by
        intro x
        funext k
        by_cases hk : k = i
        · subst k; simp
        · simp [hk]
      right_inv := by
        intro p
        apply Prod.ext
        · funext j
          have hj : j.val ≠ i := Finset.ne_of_mem_erase j.property
          simp [hj]
        · funext j
          have hj : j.val = i := Finset.mem_singleton.mp j.property
          simp only [dif_pos hj]
          exact congrArg p.2 (Subtype.ext hj.symm) }
    measurable_toFun := (Measurable.of_eval fun j => measurable_pi_apply j.val).prodMk
      (Measurable.of_eval fun j => measurable_pi_apply j.val)
    measurable_invFun := by
      apply measurable_pi_lambda
      intro k
      change Measurable (fun p : (((Finset.univ : Finset I).erase i → Ω) × (({i} : Finset I) → Ω)) =>
        if hk : k = i then p.2 ⟨i, by simp⟩ else p.1 ⟨k, by simp [hk]⟩)
      by_cases hk : k = i
      · simp only [dif_pos hk]
        exact (measurable_pi_apply (⟨i, by simp⟩ : ({i} : Finset I))).comp measurable_snd
      · simp only [dif_neg hk]
        exact (measurable_pi_apply (⟨k, by simp [hk]⟩ : (Finset.univ : Finset I).erase i)).comp measurable_fst }
