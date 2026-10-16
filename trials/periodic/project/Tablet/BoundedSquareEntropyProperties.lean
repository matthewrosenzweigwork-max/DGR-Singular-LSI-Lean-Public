module

public import Tablet.EntropyVariational

@[expose] public section
open MeasureTheory

-- [TABLET NODE: BoundedSquareEntropyProperties]
theorem BoundedSquareEntropyProperties {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (R : ℝ) (hR : ∀ x, |f x| ≤ R) :
    Integrable (fun x => f x^2) μ ∧
    Integrable (fun x => f x^2 * Real.log (f x^2)) μ ∧
    0 ≤ Entropy μ (fun x => f x^2) ∧
    ((∫ x,f x^2 ∂μ)=0 → Entropy μ (fun x => f x^2)=0) := by
-- BODY
  have hb (x : Ω) : 0 ≤ f x^2 ∧ f x^2 ≤ R^2 := by
    refine ⟨sq_nonneg _,?_⟩
    exact sq_le_sq.mpr ((hR x).trans (le_abs_self R))
  have hi : Integrable (fun x => f x^2) μ := by
    apply (integrable_const (R^2)).mono' (hf.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hb x).1]
      exact (hb x).2
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) (R^2))).exists_bound_of_continuousOn
    Real.continuous_mul_log.continuousOn
  have hlog : Integrable (fun x => f x^2 * Real.log (f x^2)) μ := by
    apply (integrable_const C).mono'
      (Real.continuous_mul_log.measurable.comp (hf.pow_const 2)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => hC (f x^2) (hb x)
  have hn : ∀ᵐ x ∂μ,0≤f x^2 := Filter.Eventually.of_forall fun x => sq_nonneg _
  have hv := EntropyVariational μ (fun x => f x^2) (hf.pow_const 2) hn hi hlog
  refine ⟨hi,hlog,?_,hv.2.2⟩
  have hm : 0 ≤ ∫ x,f x^2 ∂μ := integral_nonneg fun x => sq_nonneg _
  rcases hm.eq_or_lt with h|h
  · rw [hv.2.2 h.symm]
  · rw [hv.2.1 h]
    exact integral_nonneg_of_ae (hv.1 _ h).1
