import Tablet.Entropy
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
open MeasureTheory InformationTheory

-- [TABLET NODE: BoundedProbabilityDensityEntropy]
theorem BoundedProbabilityDensityEntropy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (u : Ω → ℝ) (M : ℝ)
    (hu : Measurable u) (hb : ∀ x, 0 ≤ u x ∧ u x ≤ M)
    (hm : (∫ x, u x ∂μ) = 1) :
    let S := μ.withDensity (fun x => ENNReal.ofReal (u x))
    IsProbabilityMeasure S ∧ klDiv S μ ≠ ⊤ ∧ (klDiv S μ).toReal = Entropy μ u := by
-- BODY
  let S := μ.withDensity (fun x => ENNReal.ofReal (u x))
  have hi : Integrable u μ := by
    apply (integrable_const M).mono' hu.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hb x).1]
      exact (hb x).2
  have hp : IsProbabilityMeasure S := by
    apply isProbabilityMeasure_iff.mpr
    dsimp [S]
    rw [withDensity_apply _ MeasurableSet.univ]
    simp only [setLIntegral_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x => (hb x).1), hm]
    norm_num
  haveI := hp
  have hac : S ≪ μ := withDensity_absolutelyContinuous _ _
  have hrn : ∀ᵐ x ∂μ, (S.rnDeriv μ x).toReal = u x := by
    filter_upwards [Measure.rnDeriv_withDensity μ (ENNReal.measurable_ofReal.comp hu)] with x hx
    change ((μ.withDensity (ENNReal.ofReal ∘ u)).rnDeriv μ x).toReal = u x
    rw [hx]
    exact ENNReal.toReal_ofReal (hb x).1
  obtain ⟨K, hK⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) M)).exists_bound_of_continuousOn
    Real.continuous_mul_log.continuousOn
  have hlog : Integrable (fun x => u x * Real.log (u x)) μ := by
    apply (integrable_const K).mono' (Real.continuous_mul_log.measurable.comp hu).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => hK (u x) (hb x)
  have hk : Integrable (fun x => klFun (u x)) μ := by
    have hh := (hlog.add (integrable_const (1 : ℝ))).sub hi
    change Integrable (fun x => u x * Real.log (u x) + 1 - u x) μ at hh
    exact hh
  have he : (fun x => klFun (S.rnDeriv μ x).toReal) =ᵐ[μ] (fun x => klFun (u x)) := by
    filter_upwards [hrn] with x hx
    rw [hx]
  have hkrn : Integrable (fun x => klFun (S.rnDeriv μ x).toReal) μ :=
    hk.congr he.symm
  have hllr := (integrable_klFun_rnDeriv_iff hac).mp hkrn
  refine ⟨hp, klDiv_ne_top hac hllr, ?_⟩
  rw [toReal_klDiv_eq_integral_klFun hac, integral_congr_ae he]
  simp only [klFun_apply, Entropy]
  rw [integral_sub (show Integrable (fun x => u x * Real.log (u x) + 1) μ from hlog.add (integrable_const (1 : ℝ))) hi,
    integral_add hlog (integrable_const (1 : ℝ)), hm]
  simp
