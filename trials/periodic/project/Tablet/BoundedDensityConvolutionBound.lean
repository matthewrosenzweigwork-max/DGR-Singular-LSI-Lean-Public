import Tablet.Preamble
import Mathlib.MeasureTheory.Group.Integral
open MeasureTheory UnitAddTorus

-- [TABLET NODE: BoundedDensityConvolutionBound]
theorem BoundedDensityConvolutionBound (d : ℕ)
    (g r : UnitAddTorus (Fin d) → ℝ) (hg : Measurable g) (hgi : Integrable g volume)
    (hr : Measurable r) (M : ℝ)
    (hrb : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), 0 ≤ r x ∧ r x ≤ M) :
    ∀ x, Integrable (fun y => g (x-y)*r y) volume ∧
      |∫ y, g (x-y)*r y| ≤ M*(∫ y, |g y|) := by
-- BODY
  have hrnorm : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), ‖r x‖ ≤ M :=
    hrb.mono fun _ hx => by simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2
  have hi (x : UnitAddTorus (Fin d)) : Integrable (fun y => g (x-y)*r y) volume :=
    (hgi.comp_sub_left x).mul_bdd hr.aestronglyMeasurable hrnorm
  intro x
  refine ⟨hi x, ?_⟩
  calc
    _ ≤ ∫ y, ‖g (x-y)*r y‖ := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y => g (x-y)*r y)
    _ ≤ ∫ y, M*|g (x-y)| := by
      apply integral_mono_ae (hi x).norm ((hgi.abs.comp_sub_left x).const_mul M)
      filter_upwards [hrb] with y hy
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hy.1]
      nlinarith [abs_nonneg (g (x-y))]
    _ = _ := by rw [integral_const_mul, integral_sub_left_eq_self (fun y => |g y|) volume x]
