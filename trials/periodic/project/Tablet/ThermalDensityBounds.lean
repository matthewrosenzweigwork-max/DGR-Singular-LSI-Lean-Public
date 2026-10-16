import Tablet.ThermalNormalizerJensen

open MeasureTheory

-- [TABLET NODE: ThermalDensityBounds]
theorem ThermalDensityBounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (q h : Ω → ℝ) (β B c qlo qhi G H : ℝ)
    (hβ : 0 ≤ β) (hβB : β ≤ B) (hc : 0 ≤ c)
    (hqlo : 0 < qlo) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hq : ∀ᵐ x ∂μ, qlo ≤ q x ∧ q x ≤ qhi)
    (hh : ∀ᵐ x ∂μ, -c ≤ h x)
    (hhH : ∀ᵐ x ∂μ, |h x| ≤ H)
    (hqi : Integrable q μ) (hqone : ∫ x, q x ∂μ = 1)
    (hqh : Integrable (fun x => q x * h x) μ)
    (hmean : (∫ x, q x * h x ∂μ) ≤ qhi * G)
    (hw : Integrable (fun x => q x * Real.exp (-β * h x)) μ) :
    0 < (∫ x, q x * Real.exp (-β * h x) ∂μ) ∧
    Real.exp (-B * qhi * G) ≤ (∫ x, q x * Real.exp (-β * h x) ∂μ) ∧
    (∫ x, q x * Real.exp (-β * h x) ∂μ) ≤ Real.exp (B * H) ∧
    (∀ᵐ x ∂μ,
      qlo * Real.exp (-2 * B * H) ≤
        q x * Real.exp (-β * h x) / (∫ y, q y * Real.exp (-β * h y) ∂μ) ∧
      q x * Real.exp (-β * h x) / (∫ y, q y * Real.exp (-β * h y) ∂μ) ≤
        qhi * Real.exp (B * (c + qhi * G))) := by
-- BODY
  have hqn : ∀ᵐ x ∂μ, 0 ≤ q x := hq.mono fun _ hx => hqlo.le.trans hx.1
  have hqhi : 0 ≤ qhi := by
    have h0 : 0 ≤ qhi := by
      by_contra hn
      have hneg : qhi < 0 := lt_of_not_ge hn
      -- No probability hypothesis is needed: positivity of the normalized q integral suffices.
      have hz := integral_nonpos_of_ae (hqn.and (hq.mono fun _ hx => hx.2) |>.mono
        fun _ hx => hx.2.trans hneg.le)
      rw [hqone] at hz
      norm_num at hz
    exact h0
  have hB : 0 ≤ B := hβ.trans hβB
  have hj := ThermalNormalizerJensen μ q h β hqn hqi hqone hqh hw
  have hbmean : β * (∫ x, q x * h x ∂μ) ≤ B * qhi * G := by
    calc
      _ ≤ β * (qhi * G) := mul_le_mul_of_nonneg_left hmean hβ
      _ ≤ B * (qhi * G) := mul_le_mul_of_nonneg_right hβB (mul_nonneg hqhi hG)
      _ = _ := by ring
  have hzlo : Real.exp (-B * qhi * G) ≤ ∫ x, q x * Real.exp (-β * h x) ∂μ :=
    (Real.exp_le_exp.mpr (by linarith)).trans hj
  have hz : 0 < ∫ x, q x * Real.exp (-β * h x) ∂μ :=
    (Real.exp_pos _).trans_le hzlo
  have hexpH : ∀ᵐ x ∂μ, Real.exp (-β * h x) ≤ Real.exp (B * H) := by
    filter_upwards [hhH] with x hx
    apply Real.exp_le_exp.mpr
    have hxl := (abs_le.mp hx).1
    nlinarith [mul_le_mul_of_nonneg_right hβB hH]
  have hzhi : (∫ x, q x * Real.exp (-β * h x) ∂μ) ≤ Real.exp (B * H) := by
    have he := integral_mono_ae hw (hqi.mul_const (Real.exp (B * H))) (by
      filter_upwards [hqn, hexpH] with x hqx hex
      exact mul_le_mul_of_nonneg_left hex hqx)
    simpa only [integral_mul_const, hqone, one_mul] using he
  refine ⟨hz, hzlo, hzhi, ?_⟩
  filter_upwards [hq, hh, hhH] with x hqx hhx hHx
  have hnx : 0 ≤ q x * Real.exp (-β * h x) :=
    mul_nonneg (hqlo.le.trans hqx.1) (Real.exp_pos _).le
  constructor
  · have hexlo : Real.exp (-B * H) ≤ Real.exp (-β * h x) := by
      apply Real.exp_le_exp.mpr
      have hxu := (abs_le.mp hHx).2
      nlinarith [mul_le_mul_of_nonneg_right hβB hH]
    have hnlo : qlo * Real.exp (-B * H) ≤ q x * Real.exp (-β * h x) :=
      mul_le_mul hqx.1 hexlo (Real.exp_pos _).le (hqlo.le.trans hqx.1)
    calc
      qlo * Real.exp (-2 * B * H) =
          (qlo * Real.exp (-B * H)) / Real.exp (B * H) := by
        rw [div_eq_mul_inv, ← Real.exp_neg, mul_assoc qlo, ← Real.exp_add]
        congr 1
        congr 1
        ring
      _ ≤ (q x * Real.exp (-β * h x)) / Real.exp (B * H) :=
        div_le_div_of_nonneg_right hnlo (Real.exp_pos _).le
      _ ≤ _ := div_le_div_of_nonneg_left hnx hz hzhi
  · have hexc : Real.exp (-β * h x) ≤ Real.exp (B * c) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hβB hc]
    have hnhi : q x * Real.exp (-β * h x) ≤ qhi * Real.exp (B * c) :=
      mul_le_mul hqx.2 hexc (Real.exp_pos _).le hqhi
    calc
      _ ≤ (q x * Real.exp (-β * h x)) / Real.exp (-B * qhi * G) :=
        div_le_div_of_nonneg_left hnx (Real.exp_pos _) hzlo
      _ ≤ (qhi * Real.exp (B * c)) / Real.exp (-B * qhi * G) :=
        div_le_div_of_nonneg_right hnhi (Real.exp_pos _).le
      _ = _ := by
        rw [div_eq_mul_inv, ← Real.exp_neg, mul_assoc qhi, ← Real.exp_add]
        congr 1
        congr 1
        ring
