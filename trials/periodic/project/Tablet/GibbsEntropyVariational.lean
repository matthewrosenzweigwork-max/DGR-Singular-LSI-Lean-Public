module

public import Tablet.Preamble

@[expose] public section

open MeasureTheory

-- [TABLET NODE: GibbsEntropyVariational]
theorem GibbsEntropyVariational {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (u A : Ω → ℝ) (t : ℝ)
    (hun : ∀ᵐ x ∂μ, 0 ≤ u x) (hui : Integrable u μ)
    (huone : ∫ x, u x ∂μ = 1)
    (hulog : Integrable (fun x => u x * Real.log (u x)) μ)
    (huA : Integrable (fun x => u x * A x) μ)
    (hw : Integrable (fun x => Real.exp (-t * A x)) μ)
    (hZ : 0 < ∫ x, Real.exp (-t * A x) ∂μ) :
    -(Real.log (∫ x, Real.exp (-t * A x) ∂μ)) ≤
      (∫ x, u x * Real.log (u x) ∂μ) + t * (∫ x, u x * A x ∂μ) := by
-- BODY
  let Z : ℝ := ∫ x, Real.exp (-t * A x) ∂μ
  let w : Ω → ℝ := fun x => Real.exp (-t * A x) / Z
  have hwp (x : Ω) : 0 < w x := div_pos (Real.exp_pos _) hZ
  have hwi : Integrable w μ := hw.div_const Z
  have hwone : ∫ x, w x ∂μ = 1 := by
    dsimp [w]
    rw [integral_div]
    exact div_self hZ.ne'
  have hwlog (x : Ω) : Real.log (w x) = -t * A x - Real.log Z := by
    dsimp [w]
    rw [Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]
  have hident (x : Ω) :
      u x * Real.log (u x / w x) - u x + w x =
      u x * Real.log (u x) + t * (u x * A x) + Real.log Z * u x - u x + w x := by
    by_cases hu0 : u x = 0
    · simp [hu0]
    · rw [Real.log_div hu0 (hwp x).ne', hwlog]
      ring
  have hscalar (z v : ℝ) (hz : 0 ≤ z) (hv : 0 < v) :
      0 ≤ z * Real.log (z / v) - z + v := by
    by_cases hz0 : z = 0
    · simp [hz0, hv.le]
    · have hzp : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
      have hh := mul_le_mul_of_nonneg_left
        (Real.log_le_sub_one_of_pos (div_pos hv hzp)) hz
      rw [Real.log_div hv.ne' hz0, Real.log_div hz0 hv.ne'] at *
      have hd : z * (v / z) = v := by field_simp
      nlinarith
  have hi : Integrable (fun x => u x * Real.log (u x / w x) - u x + w x) μ := by
    have hh := (((hulog.add (huA.const_mul t)).add (hui.const_mul (Real.log Z))).sub hui).add hwi
    apply hh.congr
    exact Filter.Eventually.of_forall fun x => (hident x).symm
  have hnonneg : 0 ≤ ∫ x, (u x * Real.log (u x / w x) - u x + w x) ∂μ :=
    integral_nonneg_of_ae (hun.mono fun x hx => hscalar (u x) (w x) hx (hwp x))
  have heq : (∫ x, (u x * Real.log (u x / w x) - u x + w x) ∂μ) =
      (∫ x, u x * Real.log (u x) ∂μ) + t * (∫ x, u x * A x ∂μ) + Real.log Z := by
    have h1 : Integrable (fun x => u x * Real.log (u x) + t * (u x * A x)) μ :=
      hulog.add (huA.const_mul t)
    have h2 : Integrable (fun x => u x * Real.log (u x) + t * (u x * A x) + Real.log Z * u x) μ :=
      h1.add (hui.const_mul (Real.log Z))
    have h3 : Integrable (fun x => u x * Real.log (u x) + t * (u x * A x) + Real.log Z * u x - u x) μ :=
      h2.sub hui
    rw [integral_congr_ae (Filter.Eventually.of_forall hident),
      integral_add h3 hwi, integral_sub h2 hui,
      integral_add h1 (hui.const_mul (Real.log Z)),
      integral_add hulog (huA.const_mul t),
      integral_const_mul, integral_const_mul, huone, hwone]
    ring
  rw [heq] at hnonneg
  change -Real.log Z ≤ _
  linarith
