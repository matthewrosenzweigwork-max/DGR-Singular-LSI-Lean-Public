module

public import Tablet.Preamble
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Filter
set_option autoImplicit false
universe u

-- [TABLET NODE: WeightedIntegralCauchySchwarz]
theorem WeightedIntegralCauchySchwarz {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (K f : Ω → ℝ)
    (hK : ∀ᵐ x ∂μ, 0 ≤ K x) (hKi : Integrable K μ)
    (hKfi : Integrable (fun x => K x * f x) μ)
    (hKf2i : Integrable (fun x => K x * (f x)^2) μ) :
    (∫ x, K x*f x ∂μ)^2 ≤ (∫ x, K x ∂μ)*(∫ x, K x*(f x)^2 ∂μ) := by
-- BODY
  let A := ∫ x, K x ∂μ
  let B := ∫ x, K x*f x ∂μ
  let D := ∫ x, K x*(f x)^2 ∂μ
  have hA : 0 ≤ A := integral_nonneg_of_ae hK
  by_cases hA0 : A = 0
  · have hz := (integral_eq_zero_iff_of_nonneg_ae hK hKi).mp hA0
    have hB0 : B = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hz] with x hx
      simp [hx]
    change B^2 ≤ A*D
    simp [hA0, hB0]
  · have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
    let c := B/A
    let F := fun x => K x*(f x)^2 - (2*c)*(K x*f x) + c^2*K x
    have hFi : Integrable F μ := (hKf2i.sub (hKfi.const_mul (2*c))).add (hKi.const_mul (c^2))
    have hFn : ∀ᵐ x ∂μ, 0 ≤ F x := by
      filter_upwards [hK] with x hx
      have h := mul_nonneg hx (sq_nonneg (f x-c))
      dsimp [F]
      nlinarith only [h]
    have hp := integral_nonneg_of_ae hFn
    have he : (∫ x, F x ∂μ) = D-2*c*B+c^2*A := by
      have hadd := integral_add (hKf2i.sub (hKfi.const_mul (2*c))) (hKi.const_mul (c^2))
      have hsub := integral_sub hKf2i (hKfi.const_mul (2*c))
      simp only [Pi.sub_apply] at hadd hsub
      dsimp only [F]
      rw [hadd, hsub, integral_const_mul, integral_const_mul]
    rw [he] at hp
    have hid : D-2*c*B+c^2*A = (A*D-B^2)/A := by
      dsimp [c]
      field_simp
      ring
    rw [hid] at hp
    have hn : 0 ≤ A*D-B^2 := by simpa only [zero_mul] using (le_div_iff₀ hAp).mp hp
    change B^2 ≤ A*D
    linarith
