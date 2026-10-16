module

public import Tablet.Entropy

@[expose] public section
-- [TABLET NODE: EntropyVariational]
theorem EntropyVariational {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (u : Ω → ℝ) (hu : Measurable u) (hn : ∀ᵐ x ∂μ, 0 ≤ u x)
    (hi : MeasureTheory.Integrable u μ)
    (hlog : MeasureTheory.Integrable (fun x => u x * Real.log (u x)) μ) :
    (∀ t : ℝ, 0 < t →
      (∀ᵐ x ∂μ, 0 ≤ u x * Real.log (u x / t) - u x + t) ∧
      MeasureTheory.Integrable (fun x => u x * Real.log (u x / t) - u x + t) μ ∧
      Entropy μ u ≤ ∫ x, (u x * Real.log (u x / t) - u x + t) ∂μ) ∧
    (0 < ∫ x, u x ∂μ → Entropy μ u =
      ∫ x, (u x * Real.log (u x / (∫ y, u y ∂μ)) - u x +
        (∫ y, u y ∂μ)) ∂μ) ∧
    ((∫ x, u x ∂μ) = 0 → Entropy μ u = 0) := by
-- BODY
  have log_identity (z t : ℝ) (ht : 0 < t) :
      z * Real.log (z / t) = z * Real.log z - z * Real.log t := by
    by_cases hz : z = 0
    · simp [hz]
    · rw [Real.log_div hz ht.ne']
      ring
  have scalar_nonneg (z t : ℝ) (hz : 0 ≤ z) (ht : 0 < t) :
      0 ≤ z * Real.log (z / t) - z + t := by
    by_cases hz0 : z = 0
    · simp [hz0, ht.le]
    · have hzp : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
      have h := mul_le_mul_of_nonneg_left
        (Real.log_le_sub_one_of_pos (div_pos ht hzp)) hz
      rw [Real.log_div ht.ne' hz0] at h
      have hdiv : z * (t / z) = t := by field_simp
      rw [log_identity z t ht]
      nlinarith
  have mean_nonneg : 0 ≤ ∫ x, u x ∂μ := MeasureTheory.integral_nonneg_of_ae hn
  have phi_integrable (t : ℝ) (ht : 0 < t) :
      MeasureTheory.Integrable (fun x => u x * Real.log (u x / t) - u x + t) μ := by
    have h := ((hlog.sub (hi.mul_const (Real.log t))).sub hi).add
      (MeasureTheory.integrable_const t)
    exact h.congr (Filter.Eventually.of_forall fun x => by
      change u x * Real.log (u x) - u x * Real.log t - u x + t =
        u x * Real.log (u x / t) - u x + t
      rw [log_identity (u x) t ht])
  have phi_integral (t : ℝ) (ht : 0 < t) :
      (∫ x, (u x * Real.log (u x / t) - u x + t) ∂μ) =
        (∫ x, u x * Real.log (u x) ∂μ) -
          (∫ x, u x ∂μ) * Real.log t - (∫ x, u x ∂μ) + t := by
    have hid : (fun x => u x * Real.log (u x / t) - u x + t) =
        (fun x => (u x * Real.log (u x) - u x * Real.log t) - u x + t) := by
      funext x
      rw [log_identity (u x) t ht]
    have h₁ : MeasureTheory.Integrable
        (fun x => u x * Real.log (u x) - u x * Real.log t) μ :=
      hlog.sub (hi.mul_const (Real.log t))
    have h₂ : MeasureTheory.Integrable
        (fun x => u x * Real.log (u x) - u x * Real.log t - u x) μ := h₁.sub hi
    rw [hid, MeasureTheory.integral_add h₂ (MeasureTheory.integrable_const t),
      MeasureTheory.integral_sub h₁ hi,
      MeasureTheory.integral_sub hlog (hi.mul_const (Real.log t)),
      MeasureTheory.integral_mul_const]
    simp
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    refine ⟨hn.mono fun x hx => scalar_nonneg (u x) t hx ht, phi_integrable t ht, ?_⟩
    rw [phi_integral t ht]
    unfold Entropy
    have h := scalar_nonneg (∫ x, u x ∂μ) t mean_nonneg ht
    rw [log_identity (∫ x, u x ∂μ) t ht] at h
    linarith
  · intro hb
    rw [phi_integral (∫ x, u x ∂μ) hb]
    unfold Entropy
    ring
  · intro hb
    have hu0 : u =ᵐ[μ] 0 :=
      (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hn hi).mp hb
    have hulog : (fun x => u x * Real.log (u x)) =ᵐ[μ] 0 := by
      filter_upwards [hu0] with x hx
      simp [hx]
    unfold Entropy
    rw [hb, MeasureTheory.integral_congr_ae hulog]
    simp
