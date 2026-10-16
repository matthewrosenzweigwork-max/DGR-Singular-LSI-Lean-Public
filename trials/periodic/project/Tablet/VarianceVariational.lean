import Tablet.Preamble
-- [TABLET NODE: VarianceVariational]
theorem VarianceVariational {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : MeasureTheory.MemLp f 2 μ) :
    ∀ t : ℝ,
      (∫ x, (f x - t) ^ 2 ∂μ) =
        ProbabilityTheory.variance f μ + ((∫ x, f x ∂μ) - t) ^ 2 ∧
      ProbabilityTheory.variance f μ ≤ (∫ x, (f x - t) ^ 2 ∂μ) := by
-- BODY
  intro t
  have hi : MeasureTheory.Integrable f μ := hf.integrable (by norm_num)
  have hm : (∫ x, f x - t ∂μ) = (∫ x, f x ∂μ) - t := by
    rw [MeasureTheory.integral_sub hi (MeasureTheory.integrable_const t)]
    simp
  have hv := ProbabilityTheory.variance_eq_sub
    (hf.sub (MeasureTheory.memLp_const t))
  change ProbabilityTheory.variance (fun x => f x - t) μ =
    (∫ x, (f x - t) ^ 2 ∂μ) - (∫ x, f x - t ∂μ) ^ 2 at hv
  rw [ProbabilityTheory.variance_sub_const hf.aestronglyMeasurable t, hm] at hv
  have hidentity : (∫ x, (f x - t) ^ 2 ∂μ) =
      ProbabilityTheory.variance f μ + ((∫ x, f x ∂μ) - t) ^ 2 := by
    simpa only [Pi.pow_apply, Pi.sub_apply] using (eq_add_of_sub_eq hv.symm)
  refine ⟨hidentity, ?_⟩
  rw [hidentity]
  exact le_add_of_nonneg_right (sq_nonneg _)
