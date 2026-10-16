import Tablet.Preamble
import Mathlib.Tactic
set_option maxHeartbeats 1600000
open MeasureTheory
namespace UniformTraceAbsorption

private theorem power_le_square_add_one {t θ : ℝ} (ht : 0 ≤ t)
    (hθ : 0 ≤ θ) (hθ2 : θ ≤ 2) : t ^ θ ≤ t ^ 2 + 1 := by
  by_cases ht1 : t ≤ 1
  · have h := Real.rpow_le_one ht ht1 hθ
    nlinarith [sq_nonneg t]
  · have h := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge ht1) hθ2
    rw [Real.rpow_two] at h
    linarith

private theorem power_sum_bound {x y θ : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hθ : 0 ≤ θ) : (x + y) ^ θ ≤ (2 : ℝ) ^ θ * (x ^ θ + y ^ θ) := by
  have htwo : 0 ≤ (2 : ℝ) ^ θ := Real.rpow_nonneg (by norm_num) _
  rcases le_total x y with hxy | hyx
  · have h := Real.rpow_le_rpow (by positivity : 0 ≤ x + y)
      (by linarith : x + y ≤ 2 * y) hθ
    rw [Real.mul_rpow (by norm_num) hy] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (by linarith [Real.rpow_nonneg hx θ]) htwo)
  · have h := Real.rpow_le_rpow (by positivity : 0 ≤ x + y)
      (by linarith : x + y ≤ 2 * x) hθ
    rw [Real.mul_rpow (by norm_num) hx] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (by linarith [Real.rpow_nonneg hy θ]) htwo)

private theorem confinement_force_power_bound {E : Type*} [NormedAddCommGroup E]
    (v F : E) {θ : ℝ} (hθ : 0 ≤ θ) (hθ2 : θ ≤ 2) :
    ‖v‖ ^ θ ≤ (2 : ℝ) ^ θ * (‖v + F‖ ^ 2 + 1 + ‖F‖ ^ θ) := by
  have hnorm : ‖v‖ ≤ ‖v + F‖ + ‖F‖ := by
    calc ‖v‖ = ‖(v + F) - F‖ := by congr 1; abel
      _ ≤ ‖v + F‖ + ‖F‖ := norm_sub_le _ _
  have hp := Real.rpow_le_rpow (norm_nonneg v) hnorm hθ
  have hsum := power_sum_bound (norm_nonneg (v + F)) (norm_nonneg F) hθ
  have hsq := power_le_square_add_one (norm_nonneg (v + F)) hθ hθ2
  have htwo := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) θ
  exact hp.trans (hsum.trans (mul_le_mul_of_nonneg_left (by linarith) htwo))

end UniformTraceAbsorption
open UniformTraceAbsorption
-- [TABLET NODE: UniformTraceAbsorption]
theorem UniformTraceAbsorption {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (μ : Measure Ω)
    (ψ Δ : Ω → ℝ) (v F : Ω → E) (θ H G S energy C : ℝ)
    (hθ : 0 < θ) (hθ2 : θ < 2) (hH : 0 ≤ H) (hG : 0 ≤ G)
    (hmass : Integrable (fun x => ψ x ^ 2) μ)
    (hdelta : Integrable (fun x => Δ x * ψ x ^ 2) μ)
    (htotal : Integrable (fun x => ‖v x + F x‖ ^ 2 * ψ x ^ 2) μ)
    (hforce : Integrable (fun x => ‖F x‖ ^ θ * ψ x ^ 2) μ)
    (hform : (∫ x, ‖F x‖ ^ θ * ψ x ^ 2 ∂μ) ≤ H * G)
    (hground : G + (∫ x, ‖v x + F x‖ ^ 2 * ψ x ^ 2 ∂μ) / 4 + S / 2 =
      energy + (∫ x, Δ x * ψ x ^ 2 ∂μ) / 2)
    (hgrowth : ∀ x, Δ x ≤ (1 / (4 * (2 : ℝ) ^ θ * (1 + H))) * ‖v x‖ ^ θ + C) :
    G / 2 + (∫ x, ‖v x + F x‖ ^ 2 * ψ x ^ 2 ∂μ) / 8 + S / 2 ≤
      energy + (C + (1 / (4 * (2 : ℝ) ^ θ * (1 + H))) * (2 : ℝ) ^ θ) / 2 *
        (∫ x, ψ x ^ 2 ∂μ) := by
-- BODY
  let c : ℝ := (2 : ℝ) ^ θ
  have hc : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  let a : ℝ := 1 / (4 * c * (1 + H))
  have hden : 0 < 4 * c * (1 + H) := by positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hC := hgrowth
  have hac : a * c ≤ 1 / 4 := by
    dsimp [a]
    rw [div_mul_eq_mul_div, one_mul]
    apply (div_le_iff₀ hden).2
    nlinarith
  have hacH : a * c * H ≤ 1 := by
    dsimp [a]
    have hh : 1 / (4 * c * (1 + H)) * c * H =
        (c * H) / (4 * c * (1 + H)) := by ring
    rw [hh]
    apply (div_le_iff₀ hden).2
    nlinarith
  let T := ∫ x, ‖v x + F x‖ ^ 2 * ψ x ^ 2 ∂μ
  let M := ∫ x, ψ x ^ 2 ∂μ
  let Q := ∫ x, Δ x * ψ x ^ 2 ∂μ
  have hT : 0 ≤ T := integral_nonneg fun x => by positivity
  have hM : 0 ≤ M := integral_nonneg fun x => by positivity
  have hcomp : Q ≤ a * c * T + a * c *
      (∫ x, ‖F x‖ ^ θ * ψ x ^ 2 ∂μ) + (C + a * c) * M := by
    have hi := (htotal.const_mul (a * c)).add
      ((hforce.const_mul (a * c)).add (hmass.const_mul (C + a * c)))
    have hh := integral_mono hdelta hi (fun x => ?_)
    · simp only [Pi.add_apply] at hh
      have hij : Integrable (fun x => a * c * (‖F x‖ ^ θ * ψ x ^ 2) +
          (C + a * c) * ψ x ^ 2) μ :=
        (hforce.const_mul (a * c)).add (hmass.const_mul (C + a * c))
      rw [integral_add (htotal.const_mul (a * c)) hij,
        integral_add (hforce.const_mul (a * c)) (hmass.const_mul (C + a * c)),
        integral_const_mul, integral_const_mul, integral_const_mul] at hh
      exact hh.trans_eq (by dsimp [T, Q, M]; ring)
    · have hp := confinement_force_power_bound (v x) (F x) hθ.le hθ2.le
      have hgrow := hC x
      have hm := sq_nonneg (ψ x)
      have hap := mul_le_mul_of_nonneg_left hp ha.le
      have hpoint : Δ x ≤ a * c * ‖v x + F x‖ ^ 2 +
          a * c * ‖F x‖ ^ θ + (C + a * c) := by
        dsimp [c] at *
        nlinarith
      have hh := mul_le_mul_of_nonneg_right hpoint hm
      change Δ x * ψ x ^ 2 ≤ a * c * (‖v x + F x‖ ^ 2 * ψ x ^ 2) +
        (a * c * (‖F x‖ ^ θ * ψ x ^ 2) + (C + a * c) * ψ x ^ 2)
      exact hh.trans_eq (by ring)
  have hforce_scaled := mul_le_mul_of_nonneg_left hform (by positivity : 0 ≤ a * c)
  have hdelta_bound : Q / 2 ≤ T / 8 + G / 2 + (C + a * c) / 2 * M := by
    have ht := mul_le_mul_of_nonneg_right hac hT
    have hg := mul_le_mul_of_nonneg_right hacH hG
    nlinarith
  dsimp [T, Q, M] at *
  linarith
