module

public import Tablet.Preamble

@[expose] public section

open MeasureTheory

-- [TABLET NODE: ThermalNormalizerJensen]
theorem ThermalNormalizerJensen {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (q h : Ω → ℝ) (β : ℝ)
    (hq : ∀ᵐ x ∂μ, 0 ≤ q x) (hqi : Integrable q μ)
    (hqone : ∫ x, q x ∂μ = 1)
    (hqh : Integrable (fun x => q x * h x) μ)
    (hw : Integrable (fun x => q x * Real.exp (-β * h x)) μ) :
    Real.exp (-β * (∫ x, q x * h x ∂μ)) ≤
      ∫ x, q x * Real.exp (-β * h x) ∂μ := by
-- BODY
  let a : ℝ := -β * (∫ x, q x * h x ∂μ)
  have htan (z : ℝ) : Real.exp a * (1 + z - a) ≤ Real.exp z := by
    have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (z - a))
      (Real.exp_pos a).le
    rw [← Real.exp_add] at hh
    convert hh using 1 <;> congr 1 <;> ring
  have hlin : Integrable (fun x => q x * (Real.exp a * (1 + (-β * h x) - a))) μ := by
    have hh := (hqi.mul_const (Real.exp a * (1 - a))).sub
      (hqh.mul_const (Real.exp a * β))
    convert hh using 1
    ext x
    change q x * (Real.exp a * (1 + (-β * h x) - a)) =
      q x * (Real.exp a * (1 - a)) - q x * h x * (Real.exp a * β)
    ring
  have hle := integral_mono_ae hlin hw (hq.mono fun x hx =>
    mul_le_mul_of_nonneg_left (htan (-β * h x)) hx)
  have heq : (∫ x, q x * (Real.exp a * (1 + (-β * h x) - a)) ∂μ) =
      Real.exp a := by
    have he : (fun x => q x * (Real.exp a * (1 + (-β * h x) - a))) =
        (fun x => q x * (Real.exp a * (1 - a)) -
          (q x * h x) * (Real.exp a * β)) := by
      funext x
      ring
    rw [he, integral_sub (hqi.mul_const _) (hqh.mul_const _),
      integral_mul_const, integral_mul_const, hqone]
    dsimp [a]
    ring
  rw [heq] at hle
  exact hle
