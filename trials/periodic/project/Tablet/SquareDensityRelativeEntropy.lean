import Tablet.BoundedProbabilityDensityEntropy
open MeasureTheory InformationTheory

-- [TABLET NODE: SquareDensityRelativeEntropy]
theorem SquareDensityRelativeEntropy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Measurable f) (R : ℝ) (hR : ∀ x, |f x| ≤ R)
    (ha : 0 < ∫ x, f x ^ 2 ∂μ) :
    let a := ∫ x, f x ^ 2 ∂μ
    let S := μ.withDensity (fun x => ENNReal.ofReal (f x ^ 2 / a))
    IsProbabilityMeasure S ∧ klDiv S μ ≠ ⊤ ∧
      a * (klDiv S μ).toReal = Entropy μ (fun x => f x ^ 2) := by
-- BODY
  let a := ∫ x, f x ^ 2 ∂μ
  let u := fun x => f x ^ 2 / a
  have ha' : 0 < a := ha
  have hb : ∀ x, 0 ≤ u x ∧ u x ≤ R ^ 2 / a := by
    intro x
    refine ⟨div_nonneg (sq_nonneg _) ha'.le, div_le_div_of_nonneg_right ?_ ha'.le⟩
    exact sq_le_sq.mpr ((hR x).trans (le_abs_self R))
  have hmass : (∫ x, u x ∂μ) = 1 := by
    dsimp [u]
    rw [integral_div]
    exact div_self ha'.ne'
  obtain ⟨hp, hfin, he⟩ := BoundedProbabilityDensityEntropy μ u (R^2/a)
    ((hf.pow_const 2).div_const a) hb hmass
  refine ⟨hp, hfin, ?_⟩
  rw [he]
  have hu : Integrable u μ := by
    apply (integrable_const (R^2/a)).mono' ((hf.pow_const 2).div_const a).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hb x).1]
      exact (hb x).2
  obtain ⟨K,hK⟩ := (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) (R^2/a))).exists_bound_of_continuousOn
    Real.continuous_mul_log.continuousOn
  have hul : Integrable (fun x => u x * Real.log (u x)) μ := by
    apply (integrable_const K).mono'
      (Real.continuous_mul_log.measurable.comp ((hf.pow_const 2).div_const a)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => hK (u x) (hb x)
  have hpoint (x : Ω) : f x ^ 2 * Real.log (f x ^ 2) =
      a * (u x * Real.log (u x)) + Real.log a * (f x ^ 2) := by
    by_cases hx : f x = 0
    · simp [u, hx]
    · have hl : Real.log (u x) = Real.log (f x ^ 2) - Real.log a := by
        exact Real.log_div (pow_ne_zero 2 hx) ha'.ne'
      rw [hl]
      dsimp [u]
      field_simp
      <;> ring
  have heq : (∫ x, f x^2 * Real.log (f x^2) ∂μ) =
      a * (∫ x, u x * Real.log (u x) ∂μ) + Real.log a * a := by
    simp_rw [hpoint]
    rw [integral_add (hul.const_mul a) (show Integrable (fun x => Real.log a * f x^2) μ from
      (hu.mul_const a).congr (Filter.Eventually.of_forall fun x => by dsimp [u]; field_simp) |>.const_mul (Real.log a))]
    rw [integral_const_mul, integral_const_mul]
  change a * Entropy μ u = Entropy μ (fun x => f x^2)
  dsimp only [Entropy]
  rw [hmass, heq]
  change a * ((∫ x,u x*Real.log (u x)∂μ)-1*Real.log 1) =
    a*(∫ x,u x*Real.log (u x)∂μ)+Real.log a*a-a*Real.log a
  rw [Real.log_one]
  ring
