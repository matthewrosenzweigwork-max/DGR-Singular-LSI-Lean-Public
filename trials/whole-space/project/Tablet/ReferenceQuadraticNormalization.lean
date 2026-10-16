module

public import Tablet.ReferencePartition
public import Tablet.BoundedMultiplier
public import Tablet.GaussianConfinementIntegral
public import Mathlib.Tactic.Linarith

@[expose] public section

-- [TABLET NODE: ReferenceQuadraticNormalization]
theorem ReferenceQuadraticNormalization {d : ℕ} (V b : OneParticle d → ℝ)
    (κ C L : ℝ) (hκ : 0 < κ) (hV : Continuous V)
    (hb : BoundedMultiplier d L b)
    (hquad : ∀ x, (κ / 2) * ‖x‖ ^ 2 + C ≤ V x) :
    MeasureTheory.Integrable (fun x => b x * Real.exp (-V x)) ∧
    0 < ReferencePartition V b := by
-- BODY
  obtain ⟨bmin, bmax, hmin, horder, _, hbounds⟩ := hb.bounds
  have hpos : ∀ x, 0 < b x * Real.exp (-V x) := fun x =>
    mul_pos (hmin.trans_le (hbounds x).1) (Real.exp_pos _)
  have hbound : ∀ x, b x * Real.exp (-V x) ≤
      (bmax * Real.exp (-C)) * Real.exp (-(κ / 2) * ‖x‖ ^ 2) := by
    intro x
    have hExp : Real.exp (-V x) ≤
        Real.exp (-C) * Real.exp (-(κ / 2) * ‖x‖ ^ 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith [hquad x]
    calc
      b x * Real.exp (-V x) ≤ bmax * Real.exp (-V x) :=
        mul_le_mul_of_nonneg_right (hbounds x).2 (Real.exp_pos _).le
      _ ≤ bmax * (Real.exp (-C) * Real.exp (-(κ / 2) * ‖x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hExp (hmin.le.trans horder)
      _ = _ := by rw [mul_assoc]
  have hi : MeasureTheory.Integrable (fun x => b x * Real.exp (-V x)) := by
    apply ((GaussianConfinementIntegral (ι := Fin d) κ hκ).2.1.const_mul
      (bmax * Real.exp (-C))).mono_nonneg
    · exact (hb.measurable.mul (Real.continuous_exp.comp hV.neg).measurable).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun x => (hpos x).le)
    · exact Filter.Eventually.of_forall hbound
  refine ⟨hi, ?_⟩
  unfold ReferencePartition
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg (fun x => (hpos x).le) hi]
  have hsupp : Function.support (fun x => b x * Real.exp (-V x)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact ne_of_gt (hpos x)
  rw [hsupp]
  exact MeasureTheory.Measure.measure_univ_pos.mpr (NeZero.ne _)
