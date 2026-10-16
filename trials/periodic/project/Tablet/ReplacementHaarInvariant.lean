module

public import Tablet.Replacement
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section
open MeasureTheory

-- [TABLET NODE: ReplacementHaarInvariant]
theorem ReplacementHaarInvariant (d N : ℕ)
    (f : Configuration d N → ℝ)
    (hInv : ∀ i : Fin N, ∀ᵐ p ∂((volume : Measure (Configuration d N)).prod
      (volume : Measure (UnitAddTorus (Fin d)))),
        f (Replacement p.1 i p.2) = f p.1) :
    ∃ c : ℝ, ∀ᵐ X ∂(volume : Measure (Configuration d N)), f X = c := by
-- BODY
  classical
  haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simpa using (inferInstance : IsProbabilityMeasure AddCircle.haarAddCircle)
  haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin d =>
      (volume : Measure (AddCircle (1 : ℝ))))))
  let T := UnitAddTorus (Fin d)
  let C := Configuration d N
  let m := (volume : Measure C)
  let mix := fun (s : Finset (Fin N)) (X Y : C) (j : Fin N) =>
    if j ∈ s then Y j else X j
  let S := fun s (v : C × C) => (mix s v.1 v.2, mix s v.2 v.1)
  have mp (s : Finset (Fin N)) : MeasurePreserving (S s) (m.prod m) (m.prod m) := by
    let swap : Fin N ⊕ Fin N → Fin N ⊕ Fin N := fun j => match j with
      | Sum.inl i => if i ∈ s then Sum.inr i else Sum.inl i
      | Sum.inr i => if i ∈ s then Sum.inl i else Sum.inr i
    have hinvol : Function.Involutive swap := by
      intro j
      cases j with
      | inl i => by_cases h : i ∈ s <;> simp [swap, h]
      | inr i => by_cases h : i ∈ s <;> simp [swap, h]
    let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin N ⊕ Fin N => T)
    let a := MeasurableEquiv.piCongrLeft (fun _ : Fin N ⊕ Fin N => T)
      (hinvol.toPerm swap)
    have he : MeasurePreserving e.symm (m.prod m)
        (volume : Measure (Fin N ⊕ Fin N → T)) :=
      volume_measurePreserving_sumPiEquivProdPi_symm _
    have ha : MeasurePreserving a volume volume := volume_measurePreserving_piCongrLeft _ _
    have h := ((MeasurePreserving.symm e.symm he).comp ha).comp he
    convert h using 1
    funext v
    apply Prod.ext <;> funext j
    · change mix s v.1 v.2 j = a (e.symm v) (Sum.inl j)
      rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
      by_cases hjs : j ∈ s <;> simp [mix, swap, Function.Involutive.toPerm, e, hjs] <;> rfl
    · change mix s v.2 v.1 j = a (e.symm v) (Sum.inr j)
      rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
      by_cases hjs : j ∈ s <;> simp [mix, swap, Function.Involutive.toPerm, e, hjs] <;> rfl
  have hmix (s : Finset (Fin N)) : ∀ᵐ v ∂m.prod m,
      f (mix s v.1 v.2) = f v.1 := by
    induction s using Finset.induction_on with
    | empty => exact Filter.Eventually.of_forall (fun v => by simp [mix])
    | @insert i s hi ih =>
      have heval : MeasurePreserving (fun v : C × C => (v.1, v.2 i))
          (m.prod m) (m.prod (volume : Measure T)) := by
        exact (MeasurePreserving.id m).prod (measurePreserving_eval (fun _ : Fin N =>
          (volume : Measure T)) i)
      have hj := ((heval.comp (mp s)).quasiMeasurePreserving.ae (hInv i))
      filter_upwards [ih, hj] with v h hstep
      change f (Replacement (mix s v.1 v.2) i (mix s v.2 v.1 i)) =
        f (mix s v.1 v.2) at hstep
      have hu : Replacement (mix s v.1 v.2) i (mix s v.2 v.1 i) =
          mix (insert i s) v.1 v.2 := by
        funext j
        by_cases hj : j = i
        · subst j
          simp [Replacement, mix, hi]
        · simp [Replacement, mix, hj]
      rw [hu] at hstep
      exact hstep.trans h
  have hpair : ∀ᵐ v ∂m.prod m, f v.2 = f v.1 := by
    simpa [mix] using hmix Finset.univ
  obtain ⟨X, hX⟩ := (Measure.ae_ae_of_ae_prod hpair).exists
  exact ⟨f X, hX⟩

