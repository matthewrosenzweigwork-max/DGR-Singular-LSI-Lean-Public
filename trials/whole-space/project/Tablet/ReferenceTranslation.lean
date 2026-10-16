import Tablet.ReferenceLaw
import Tablet.ShiftedReference
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.Tactic.Ring
open MeasureTheory
open scoped ENNReal

-- [TABLET NODE: ReferenceTranslation]
theorem ReferenceTranslation {d : ℕ} (V b : OneParticle d → ℝ) (a : OneParticle d) :
    ReferencePartition (ShiftedReference V b a).1 (ShiftedReference V b a).2 =
      Real.exp (V a) * ReferencePartition V b ∧
    (ReferenceLaw V b).map (fun x => x - a) =
      ReferenceLaw (ShiftedReference V b a).1 (ShiftedReference V b a).2 := by
-- BODY
  have hfactor (x : OneParticle d) :
      Real.exp (-(ShiftedReference V b a).1 x) =
        Real.exp (V a) * Real.exp (-V (x + a)) := by
    change Real.exp (-(V (x + a) - V a)) = _
    rw [neg_sub, sub_eq_add_neg, Real.exp_add]
  have hZ : ReferencePartition (ShiftedReference V b a).1 (ShiftedReference V b a).2 =
      Real.exp (V a) * ReferencePartition V b := by
    unfold ReferencePartition
    calc
      _ = ∫ x, Real.exp (V a) * (b (x + a) * Real.exp (-V (x + a))) := by
        congr 1
        funext x
        rw [hfactor]
        change b (x + a) * (Real.exp (V a) * Real.exp (-V (x + a))) = _
        ring
      _ = Real.exp (V a) * ∫ x, b (x + a) * Real.exp (-V (x + a)) :=
        integral_const_mul _ _
      _ = Real.exp (V a) * ∫ x, b x * Real.exp (-V x) := by
        rw [integral_add_right_eq_self (fun y => b y * Real.exp (-V y)) a]
  have hdensity (x : OneParticle d) :
      (ReferencePartition (ShiftedReference V b a).1 (ShiftedReference V b a).2)⁻¹ *
        ((ShiftedReference V b a).2 x * Real.exp (-(ShiftedReference V b a).1 x)) =
      (ReferencePartition V b)⁻¹ * (b (x + a) * Real.exp (-V (x + a))) := by
    rw [hZ, hfactor, mul_inv_rev]
    change (ReferencePartition V b)⁻¹ * (Real.exp (V a))⁻¹ *
      (b (x + a) * (Real.exp (V a) * Real.exp (-V (x + a)))) = _
    rw [show (ReferencePartition V b)⁻¹ * (Real.exp (V a))⁻¹ *
        (b (x + a) * (Real.exp (V a) * Real.exp (-V (x + a)))) =
        (ReferencePartition V b)⁻¹ * (b (x + a) * Real.exp (-V (x + a))) *
        ((Real.exp (V a))⁻¹ * Real.exp (V a)) by ring]
    simp [Real.exp_ne_zero]
  have hmap (q : OneParticle d → ℝ≥0∞) :
      (volume.withDensity q).map (fun x : OneParticle d => x - a) =
        volume.withDensity (fun y : OneParticle d => q (y + a)) := by
    apply Measure.ext
    intro S hS
    have hT : Measurable (fun x : OneParticle d => x - a) :=
      (continuous_id.sub continuous_const).measurable
    have hp : MeasurableSet ((fun x : OneParticle d => x - a) ⁻¹' S) := hT hS
    rw [Measure.map_apply hT hS, withDensity_apply _ hp, withDensity_apply _ hS]
    rw [← lintegral_indicator hp, ← lintegral_indicator hS]
    calc
      _ = ∫⁻ x : OneParticle d,
          (S.indicator (fun y : OneParticle d => q (y + a))) (x - a) := by
        apply lintegral_congr
        intro x
        by_cases hx : x - a ∈ S
        · simp [Set.indicator_apply, hx]
        · simp [Set.indicator_apply, hx]
      _ = ∫⁻ x : OneParticle d, S.indicator (fun y : OneParticle d => q (y + a)) x := by
        simpa only [sub_eq_add_neg] using lintegral_add_right_eq_self
          (S.indicator (fun y : OneParticle d => q (y + a))) (-a)
  refine ⟨hZ, ?_⟩
  unfold ReferenceLaw
  rw [hmap]
  congr 1
  funext x
  rw [hdensity]
