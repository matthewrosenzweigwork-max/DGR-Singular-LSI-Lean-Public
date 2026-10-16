import Tablet.Preamble
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory
-- [TABLET NODE: MomentFromExponential]
theorem MomentFromExponential {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hf : Measurable f)
    (ℓ : ℝ) (hℓ : 0 < ℓ) (n : ℕ)
    (hp : Integrable (fun x => Real.exp (ℓ*f x)) μ)
    (hn : Integrable (fun x => Real.exp (-ℓ*f x)) μ) :
    Integrable (fun x => |f x|^n) μ ∧
      (∫ x,|f x|^n ∂μ) ≤ (n.factorial : ℝ)/ℓ^n *
        ((∫ x,Real.exp (ℓ*f x) ∂μ)+(∫ x,Real.exp (-ℓ*f x) ∂μ)) := by
-- BODY
  let C := (n.factorial : ℝ)/ℓ^n
  have hfac : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hpow : 0 < ℓ^n := pow_pos hℓ n
  have hC : 0 ≤ C := le_of_lt (div_pos hfac hpow)
  have hpoint (x : Ω) : |f x|^n ≤ C*(Real.exp (ℓ*f x)+Real.exp (-ℓ*f x)) := by
    have hseries := Real.pow_div_factorial_le_exp (ℓ*|f x|) (mul_nonneg (le_of_lt hℓ) (abs_nonneg (f x))) n
    have hseries' : ℓ^n*|f x|^n ≤ (n.factorial : ℝ)*Real.exp (ℓ*|f x|) := by
      rw [mul_pow] at hseries
      simpa only [mul_comm] using (div_le_iff₀ hfac).mp hseries
    have hexp : Real.exp (ℓ*|f x|) ≤ Real.exp (ℓ*f x)+Real.exp (-ℓ*f x) := by
      by_cases h : 0≤f x
      · rw [abs_of_nonneg h]
        exact le_add_of_nonneg_right (Real.exp_nonneg _)
      · rw [abs_of_neg (lt_of_not_ge h)]
        have hh : ℓ*(-f x)= -ℓ*f x := by ring
        rw [hh]
        exact le_add_of_nonneg_left (Real.exp_nonneg _)
    dsimp [C]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hpow).mpr
    calc
      _ ≤ (n.factorial : ℝ)*Real.exp (ℓ*|f x|) := by simpa only [mul_comm] using hseries'
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp (le_of_lt hfac)
  have hboundi : Integrable (fun x => C*(Real.exp (ℓ*f x)+Real.exp (-ℓ*f x))) μ :=
    (hp.add hn).const_mul C
  have hmoment : Integrable (fun x => |f x|^n) μ := by
    apply hboundi.mono' ((continuous_abs.measurable.comp hf).pow_const n).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      change ‖|f x|^n‖ ≤ C*(Real.exp (ℓ*f x)+Real.exp (-ℓ*f x))
      rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (abs_nonneg (f x)) n)]
      exact hpoint x
  refine ⟨hmoment,?_⟩
  calc
    _ ≤ ∫ x,C*(Real.exp (ℓ*f x)+Real.exp (-ℓ*f x)) ∂μ :=
      integral_mono_ae hmoment hboundi (Filter.Eventually.of_forall hpoint)
    _ = _ := by rw [integral_const_mul,integral_add hp hn]
