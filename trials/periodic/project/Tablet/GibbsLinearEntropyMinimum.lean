module

public import Tablet.GibbsEntropyVariational

@[expose] public section

open MeasureTheory

-- [TABLET NODE: GibbsLinearEntropyMinimum]
theorem GibbsLinearEntropyMinimum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hAm : AEStronglyMeasurable A μ)
    (hAb : ∀ᵐ x ∂μ, |A x| ≤ K) :
    let Z := ∫ x, Real.exp (-A x) ∂μ
    0 < Z ∧ ∃ ν : Lp ℝ 2 μ,
      (∀ᵐ x ∂μ, ν x = Real.exp (-A x) / Z) ∧
      (∀ᵐ x ∂μ, 0 < ν x ∧ ν x ≤ Real.exp (2 * K)) ∧
      (∫ x, ν x ∂μ) = 1 ∧
      ((∫ x, ν x * Real.log (ν x) ∂μ) + (∫ x, ν x * A x ∂μ) = -Real.log Z) ∧
      ∀ M : ℝ, 0 < M → Real.exp (2 * K) ≤ M →
      ∀ f : Lp ℝ 2 μ, (∀ᵐ x ∂μ, f x ∈ Set.Icc 0 M) → (∫ x, f x ∂μ) = 1 →
      (∫ x, ν x * Real.log (ν x) ∂μ) + (∫ x, ν x * A x ∂μ) ≤
      (∫ x, f x * Real.log (f x) ∂μ) + (∫ x, f x * A x ∂μ) := by
-- BODY
  let Z := ∫ x, Real.exp (-A x) ∂μ
  let w : Ω → ℝ := fun x => Real.exp (-A x) / Z
  have hem : AEStronglyMeasurable (fun x => Real.exp (-A x)) μ :=
    Real.continuous_exp.comp_aestronglyMeasurable hAm.neg
  have heb : ∀ᵐ x ∂μ, ‖Real.exp (-A x)‖ ≤ Real.exp K := by
    filter_upwards [hAb] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp hx).1])
  have hei : Integrable (fun x => Real.exp (-A x)) μ :=
    (integrable_const (Real.exp K)).mono' hem heb
  have hzlo : Real.exp (-K) ≤ Z := by
    have hh := integral_mono_ae (integrable_const (Real.exp (-K))) hei (by
      filter_upwards [hAb] with x hx
      exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp hx).2]))
    simpa [Z] using hh
  have hZ : 0 < Z := (Real.exp_pos _).trans_le hzlo
  have hwm : AEStronglyMeasurable w μ := (continuous_id.div_const Z).comp_aestronglyMeasurable hem
  have hwb : ∀ᵐ x ∂μ, 0 < w x ∧ w x ≤ Real.exp (2 * K) := by
    filter_upwards [hAb] with x hx
    have hehi : Real.exp (-A x) ≤ Real.exp K :=
      Real.exp_le_exp.mpr (by linarith [(abs_le.mp hx).1])
    refine ⟨div_pos (Real.exp_pos _) hZ, ?_⟩
    change Real.exp (-A x) / Z ≤ _
    calc
      _ ≤ Real.exp K / Z := div_le_div_of_nonneg_right hehi hZ.le
      _ ≤ Real.exp K / Real.exp (-K) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) hzlo
      _ = Real.exp (2 * K) := by rw [← Real.exp_sub]; congr 1; ring
  have hwp : MemLp w 2 μ := MemLp.of_bound hwm (Real.exp (2 * K)) (by
    filter_upwards [hwb] with x hx
    simpa only [Real.norm_eq_abs, abs_of_pos hx.1] using hx.2)
  let ν : Lp ℝ 2 μ := hwp.toLp w
  have hνeq : ∀ᵐ x ∂μ, ν x = w x := MemLp.coeFn_toLp hwp
  have hνb : ∀ᵐ x ∂μ, 0 < ν x ∧ ν x ≤ Real.exp (2 * K) := by
    filter_upwards [hνeq, hwb] with x hx hb
    simpa only [hx] using hb
  have hwi : Integrable w μ := hei.div_const Z
  have hwone : ∫ x, w x ∂μ = 1 := by
    dsimp [w]; rw [integral_div]; exact div_self hZ.ne'
  have hνone : ∫ x, ν x ∂μ = 1 := by
    rw [integral_congr_ae hνeq]; exact hwone
  have entropy_integrable (f : Ω → ℝ) (M : ℝ)
      (hfm : AEStronglyMeasurable f μ) (hfb : ∀ᵐ x ∂μ, f x ∈ Set.Icc 0 M) :
      Integrable (fun x => f x * Real.log (f x)) μ := by
    obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) M)).exists_bound_of_continuousOn
      Real.continuous_mul_log.continuousOn
    apply (integrable_const C).mono'
      (Real.continuous_mul_log.comp_aestronglyMeasurable hfm)
    exact hfb.mono fun x hx => hC (f x) hx
  have product_integrable (f : Ω → ℝ) (M : ℝ) (hM : 0 ≤ M)
      (hfm : AEStronglyMeasurable f μ) (hfb : ∀ᵐ x ∂μ, f x ∈ Set.Icc 0 M) :
      Integrable (fun x => f x * A x) μ := by
    apply (integrable_const (M * K)).mono' (hfm.mul hAm)
    filter_upwards [hfb, hAb] with x hx ha
    change ‖f x * A x‖ ≤ M * K
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hx.1]
    exact mul_le_mul hx.2 ha (abs_nonneg _) hM
  have hνbox : ∀ᵐ x ∂μ, ν x ∈ Set.Icc 0 (Real.exp (2 * K)) :=
    hνb.mono fun x hx => ⟨hx.1.le, hx.2⟩
  have hνi : Integrable (fun x => ν x) μ := hwi.congr (Filter.EventuallyEq.symm hνeq)
  have hνlog := entropy_integrable ν _ (Lp.aestronglyMeasurable ν) hνbox
  have hνA := product_integrable ν _ (Real.exp_pos _).le (Lp.aestronglyMeasurable ν) hνbox
  have hid : ∀ᵐ x ∂μ, ν x * Real.log (ν x) + ν x * A x = -Real.log Z * ν x := by
    filter_upwards [hνeq] with x hx
    rw [hx]
    have hwlog : Real.log (w x) = -A x - Real.log Z := by
      dsimp [w]; rw [Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]
    rw [hwlog]; ring
  have hvalue : (∫ x, ν x * Real.log (ν x) ∂μ) + (∫ x, ν x * A x ∂μ) = -Real.log Z := by
    rw [← integral_add hνlog hνA, integral_congr_ae hid, integral_const_mul, hνone, mul_one]
  refine ⟨hZ, ν, hνeq, hνb, hνone, hvalue, ?_⟩
  intro M hM hcap f hfb hfone
  have hfi : Integrable (fun x => f x) μ := by
    apply (integrable_const M).mono' (Lp.aestronglyMeasurable f)
    exact hfb.mono fun x hx => by simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2
  have hflog := entropy_integrable f M (Lp.aestronglyMeasurable f) hfb
  have hfA := product_integrable f M hM.le (Lp.aestronglyMeasurable f) hfb
  rw [hvalue]
  simpa only [neg_mul, one_mul] using
    GibbsEntropyVariational μ f A 1 (hfb.mono fun x hx => hx.1) hfi hfone hflog hfA
      (by simpa only [neg_mul, one_mul] using hei) (by simpa only [neg_mul, one_mul] using hZ)
