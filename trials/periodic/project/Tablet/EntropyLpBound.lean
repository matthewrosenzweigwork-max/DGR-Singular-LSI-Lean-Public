import Tablet.EntropyVariational
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
open MeasureTheory
open scoped ENNReal
-- [TABLET NODE: EntropyLpBound]
theorem EntropyLpBound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (u : Ω → ℝ)
    (hu : Measurable u) (hn : ∀ᵐ x ∂μ, 0 ≤ u x)
    (hi : Integrable u μ) (hlog : Integrable (fun x => u x * Real.log (u x)) μ)
    (q : ℝ) (hq : 1 < q) (hp : Integrable (fun x => Real.rpow (u x) q) μ) :
    Entropy μ u ≤ q/(q-1)*Real.rpow (∫ x, Real.rpow (u x) q ∂μ) (1/q) := by
-- BODY
  have entropy_power_scalar (z t q : ℝ) (hz : 0 ≤ z) (ht : 0 < t) (hq : 1 < q) :
    z * Real.log (z / t) - z + t ≤
      (Real.rpow z q / Real.rpow t (q - 1) - q * z) / (q - 1) + t := by
    by_cases hz0 : z = 0
    · simp [hz0, Real.zero_rpow (by linarith : q ≠ 0)]
    have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
    have hr : 0 < q - 1 := by linarith
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos (div_pos hzpos ht) (q-1))
    rw [Real.log_rpow (div_pos hzpos ht)] at h
    have hh := mul_le_mul_of_nonneg_left h hz
    have hid : z * Real.rpow (z / t) (q-1) = Real.rpow z q / Real.rpow t (q-1) := by
      change z * (z/t)^(q-1) = z^q/t^(q-1)
      rw [Real.div_rpow hz ht.le (q-1)]
      have hprod : z * z^(q-1) = z^q := by
        calc
          z * z^(q-1) = z^(1:ℝ) * z^(q-1) := by rw [Real.rpow_one]
          _ = z^((1:ℝ)+(q-1)) := (Real.rpow_add hzpos _ _).symm
          _ = z^q := by congr 1; ring
      rw [← mul_div_assoc, hprod]
    have hh' : (q-1)*(z*Real.log (z/t)) ≤ Real.rpow z q / Real.rpow t (q-1)-z := by
      calc
        (q-1)*(z*Real.log (z/t)) = z*((q-1)*Real.log (z/t)) := by ring
        _ ≤ z*(Real.rpow (z/t) (q-1)-1) := hh
        _ = Real.rpow z q / Real.rpow t (q-1)-z := by rw [mul_sub, hid]; ring
    have hh2 : z * Real.log (z/t) - z ≤
        (Real.rpow z q / Real.rpow t (q-1)-q*z)/(q-1) := by
      apply (le_div_iff₀ hr).mpr
      nlinarith
    linarith

  have entropy_power_control
    (μ : Measure Ω) [IsProbabilityMeasure μ] (u : Ω → ℝ)
    (hu : Measurable u) (hn : ∀ᵐ x ∂μ, 0 ≤ u x)
    (hi : Integrable u μ) (hlog : Integrable (fun x => u x * Real.log (u x)) μ)
    (q : ℝ) (hq : 1 < q) (hp : Integrable (fun x => Real.rpow (u x) q) μ)
    (t : ℝ) (ht : 0 < t) :
    Entropy μ u ≤ ((∫ x, Real.rpow (u x) q ∂μ) / Real.rpow t (q-1)
      - q*(∫ x, u x ∂μ))/(q-1)+t := by
    have hv := (EntropyVariational μ u hu hn hi hlog).1 t ht
    have hiR : Integrable (fun x =>
        (Real.rpow (u x) q / Real.rpow t (q-1) - q*u x)/(q-1)+t) μ :=
      ((hp.div_const _).sub (hi.const_mul q)).div_const (q-1) |>.add (integrable_const t)
    have h := integral_mono_ae hv.2.1 hiR (hn.mono fun x hx => entropy_power_scalar (u x) t q hx ht hq)
    have heq : (∫ x, (Real.rpow (u x) q / Real.rpow t (q-1) - q*u x)/(q-1)+t ∂μ) =
        ((∫ x, Real.rpow (u x) q ∂μ) / Real.rpow t (q-1)
          - q*(∫ x, u x ∂μ))/(q-1)+t := by
      have hpart : Integrable (fun x => (Real.rpow (u x) q / Real.rpow t (q-1) - q*u x)/(q-1)) μ :=
        ((hp.div_const _).sub (hi.const_mul q)).div_const _
      rw [integral_add hpart (integrable_const t),
        integral_div, integral_sub (hp.div_const _) (hi.const_mul q), integral_div, integral_const_mul]
      simp
    exact hv.2.2.trans (heq ▸ h)

  have entropy_power_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ] (u : Ω → ℝ)
    (hu : Measurable u) (hn : ∀ᵐ x ∂μ, 0 ≤ u x)
    (hi : Integrable u μ) (hlog : Integrable (fun x => u x * Real.log (u x)) μ)
    (q : ℝ) (hq : 1 < q) (hp : Integrable (fun x => Real.rpow (u x) q) μ)
    (t : ℝ) (ht : 0 < t) (hpt : (∫ x, Real.rpow (u x) q ∂μ) ≤ Real.rpow t q) :
    Entropy μ u ≤ q/(q-1)*t := by
    have hr : 0 < q-1 := by linarith
    have hm : 0 ≤ ∫ x, u x ∂μ := integral_nonneg_of_ae hn
    have h := entropy_power_control μ u hu hn hi hlog q hq hp t ht
    have htd : 0 < Real.rpow t (q-1) := Real.rpow_pos_of_pos ht _
    have hpdiv : (∫ x, Real.rpow (u x) q ∂μ)/Real.rpow t (q-1) ≤ t := by
      apply (div_le_iff₀ htd).mpr
      have hprod : t * Real.rpow t (q-1) = Real.rpow t q := by
        change t*t^(q-1)=t^q
        rw [Real.rpow_sub_one ht.ne']
        field_simp
      rwa [hprod]
    have hdiv := (div_le_div_iff_of_pos_right hr).mpr
      (show (∫ x, Real.rpow (u x) q ∂μ)/Real.rpow t (q-1)-q*(∫ x,u x∂μ) ≤ t by nlinarith)
    calc
      Entropy μ u ≤ ((∫ x, Real.rpow (u x) q ∂μ)/Real.rpow t (q-1)-q*(∫ x,u x∂μ))/(q-1)+t := h
      _ ≤ t/(q-1)+t := by linarith
      _ = q/(q-1)*t := by field_simp; ring

  let A := ∫ x, Real.rpow (u x) q ∂μ
  have hqn : q ≠ 0 := by linarith
  have hAn : 0 ≤ A := integral_nonneg_of_ae (hn.mono fun x hx => Real.rpow_nonneg hx _)
  by_cases hA : A = 0
  · have huz : ∀ᵐ x ∂μ, u x = 0 := by
      have hpz := (integral_eq_zero_iff_of_nonneg_ae
        (hn.mono fun x hx => Real.rpow_nonneg hx q) hp).mp hA
      filter_upwards [hn, hpz] with x hx hxz
      exact (Real.rpow_eq_zero hx hqn).mp hxz
    have hm : ∫ x, u x ∂μ = 0 := by
      calc (∫ x,u x∂μ) = ∫ _,(0:ℝ)∂μ := integral_congr_ae huz
           _ = 0 := by simp
    have hent := (EntropyVariational μ u hu hn hi hlog).2.2 hm
    rw [hent]
    change 0 ≤ q/(q-1)*Real.rpow A (1/q)
    exact mul_nonneg (div_nonneg (by linarith) (by linarith)) (Real.rpow_nonneg hAn _)
  · have hAp : 0 < A := lt_of_le_of_ne hAn (Ne.symm hA)
    have ht : 0 < Real.rpow A (1/q) := Real.rpow_pos_of_pos hAp _
    have htq : Real.rpow (Real.rpow A (1/q)) q = A := by
      change (A^(1/q))^q=A
      rw [← Real.rpow_mul hAn, one_div_mul_cancel hqn, Real.rpow_one]
    exact entropy_power_bound μ u hu hn hi hlog q hq hp _ ht (by rw [htq])
