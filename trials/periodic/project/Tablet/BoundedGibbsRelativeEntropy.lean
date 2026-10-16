module

public import Tablet.NormalizedTilt
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio

@[expose] public section
open MeasureTheory InformationTheory

-- [TABLET NODE: BoundedGibbsRelativeEntropy]
theorem BoundedGibbsRelativeEntropy {Ω : Type*} [MeasurableSpace Ω]
    (μ S : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure S]
    (V : Ω → ℝ) (hV : Measurable V) (C : ℝ) (hC : ∀ x, |V x| ≤ C)
    (hS : klDiv S μ ≠ ⊤) :
    let Z := ∫ x, Real.exp (-V x) ∂μ
    let P := NormalizedTilt μ (fun x => Real.exp (-V x))
    0 < Z ∧ IsProbabilityMeasure P ∧ klDiv S P ≠ ⊤ ∧
      (klDiv S P).toReal = (klDiv S μ).toReal + (∫ x, V x ∂S) + Real.log Z := by
-- BODY
  have hi (ν : Measure Ω) [IsProbabilityMeasure ν] : Integrable V ν := by
    apply (integrable_const C).mono' hV.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hC x
  have he : Integrable (fun x => Real.exp (-V x)) μ := by
    apply (integrable_const (Real.exp C)).mono' hV.neg.exp.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      change -V x ≤ C
      have hh := (abs_le.mp (hC x)).1
      linarith
  have hZ : 0 < ∫ x, Real.exp (-V x) ∂μ := integral_exp_pos he
  have hp : IsProbabilityMeasure (μ.tilted (fun x => -V x)) := isProbabilityMeasure_tilted he
  haveI := hp
  obtain ⟨hac, hllr⟩ := klDiv_ne_top_iff.mp hS
  have hacP : S ≪ μ.tilted (fun x => -V x) := hac.trans (absolutelyContinuous_tilted he)
  have hllrP := integrable_llr_tilted_right (f := fun x => -V x) hac (hi S).neg hllr he
  refine ⟨hZ, hp, klDiv_ne_top hacP hllrP, ?_⟩
  change (klDiv S (μ.tilted (fun x => -V x))).toReal = _
  rw [toReal_klDiv_of_measure_eq hacP (by simp),
    integral_llr_tilted_right (f := fun x => -V x) hac (hi S).neg he hllr,
    ← toReal_klDiv_of_measure_eq hac (by simp), integral_neg]
  ring
