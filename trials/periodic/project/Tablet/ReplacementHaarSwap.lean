module

public import Tablet.Replacement

@[expose] public section
-- [TABLET NODE: ReplacementHaarSwap]
theorem ReplacementHaarSwap (d N : ℕ) (i : Fin N) :
    let mX : MeasureTheory.Measure (Configuration d N) := MeasureTheory.volume
    let mz : MeasureTheory.Measure (UnitAddTorus (Fin d)) := MeasureTheory.volume
    let S := fun v : Configuration d N × UnitAddTorus (Fin d) =>
      (Replacement v.1 i v.2, v.1 i)
    MeasureTheory.MeasurePreserving S (mX.prod mz) (mX.prod mz) ∧
    ∀ F : Configuration d N × UnitAddTorus (Fin d) → ℝ,
      (∫ v, F (S v) ∂mX.prod mz) = ∫ v, F v ∂mX.prod mz := by
-- BODY
  classical
  dsimp only
  let T := UnitAddTorus (Fin d)
  let e := MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin N) => T)
  let a := MeasurableEquiv.piCongrLeft (fun _ : Option (Fin N) => T) (Equiv.swap none (some i))
  let s := e.symm.trans (a.trans e)
  have he : MeasureTheory.MeasurePreserving e.symm
      ((MeasureTheory.volume : MeasureTheory.Measure (Configuration d N)).prod MeasureTheory.volume)
      (MeasureTheory.volume : MeasureTheory.Measure (Option (Fin N) → T)) := by
    exact ⟨e.symm.measurable, MeasureTheory.Measure.pi_map_piOptionEquivProd (fun _ => MeasureTheory.volume)⟩
  have ha : MeasureTheory.MeasurePreserving a
      (MeasureTheory.volume : MeasureTheory.Measure (Option (Fin N) → T))
      (MeasureTheory.volume : MeasureTheory.Measure (Option (Fin N) → T)) :=
    MeasureTheory.volume_measurePreserving_piCongrLeft _ _
  have hs : MeasureTheory.MeasurePreserving s
      ((MeasureTheory.volume : MeasureTheory.Measure (Configuration d N)).prod MeasureTheory.volume)
      ((MeasureTheory.volume : MeasureTheory.Measure (Configuration d N)).prod MeasureTheory.volume) :=
    ((MeasureTheory.MeasurePreserving.symm e.symm he).comp ha).comp he
  have hea (w : Option (Fin N) → T) : e w = (fun j => w (some j), w none) := rfl
  have hei0 (v : Configuration d N × T) : e.symm v none = v.2 := rfl
  have hei1 (v : Configuration d N × T) (j : Fin N) : e.symm v (some j) = v.1 j := rfl
  have haa (w : Option (Fin N) → T) (j : Option (Fin N)) :
      a w j = w ((Equiv.swap none (some i)) j) := by
    dsimp only [a]
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
    simp
  have hsa : ∀ v : Configuration d N × T, s v = (Replacement v.1 i v.2, v.1 i) := by
    intro v
    change e (a (e.symm v)) = _
    rw [hea]
    apply Prod.ext
    · funext j
      change a (e.symm v) (some j) = Replacement v.1 i v.2 j
      rw [haa]
      by_cases hj : j = i
      · subst j
        simp only [Equiv.swap_apply_right, hei0, Replacement, Function.update_self]
      · have hsome : (some j : Option (Fin N)) ≠ some i := fun h => hj (Option.some.inj h)
        rw [Equiv.swap_apply_of_ne_of_ne (Option.some_ne_none j) hsome, hei1]
        simp only [Replacement, Function.update_of_ne hj]
    · change a (e.symm v) none = v.1 i
      rw [haa, Equiv.swap_apply_left, hei1]
  constructor
  · convert hs using 1
    funext v
    exact (hsa v).symm
  · intro F
    simpa only [hsa] using hs.integral_comp' F
