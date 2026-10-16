module

public import Tablet.CenteredPotentialDerivatives
public import Tablet.GrowthClassPotential
public import Tablet.HessianMinimizer

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter Metric
open scoped ContDiff ENNReal NNReal
noncomputable section

-- [TABLET NODE: GrowthClassNormalization]
theorem GrowthClassNormalization {d : ℕ} (V : OneParticle d → ℝ)
    (s κ : ℝ) (M Ca : ℝ → ℝ) (hκ : 0 < κ)
    (hV : GrowthClassPotential d s κ M Ca V) :
    ∃ a : OneParticle d, (∀ x, V a ≤ V x) ∧
      (∀ z, (∀ x, V z ≤ V x) → z=a) ∧
      (ShiftedReference V (fun _ => 1) a).1 0 = 0 ∧
      (∀ x, (ShiftedReference V (fun _ => 1) a).1 0 ≤ (ShiftedReference V (fun _ => 1) a).1 x) ∧
      GrowthClassPotential d s κ M Ca (ShiftedReference V (fun _ => 1) a).1 := by
-- BODY
  obtain ⟨a,ha,hlocal⟩ := hV.localData
  obtain ⟨m,hm,hunique,hzero,hquad,hdrift⟩ := (HessianMinimizer V κ hκ hV.toPotentialBounds).2
  have huniqueA : ∀ z, (∀ x, V z ≤ V x) → z=a := by
    intro z hz
    exact (hunique z hz).trans (hunique a ha).symm
  let W := (ShiftedReference V (fun _ => 1) a).1
  obtain ⟨hz,hgrad,hhess,hlap,hreg,hb⟩ := CenteredPotentialDerivatives V (fun _ => 1) a
  have hzW : W 0 = 0 := hz
  have hmin : ∀ x, W 0 ≤ W x := by
    intro x
    rw [hzW]
    exact sub_nonneg.mpr (ha (x+a))
  refine ⟨a,ha,huniqueA,hz,hmin,?_⟩
  refine ⟨⟨hreg hV.regularity, ?_⟩, ⟨0,hmin,?_⟩, ?_⟩
  · intro x u
    rw [hhess]
    exact hV.lower (x+a) u
  · intro R hR x hx
    change W (x+0)-W 0 ≤ M R
    rw [add_zero,hzW,sub_zero]
    exact hlocal R hR x hx
  · intro δ hδ x
    rw [hlap,hgrad]
    exact hV.growth δ hδ (x+a)
