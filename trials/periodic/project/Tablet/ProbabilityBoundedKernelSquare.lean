module

public import Tablet.Preamble
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic

@[expose] public section
open MeasureTheory Filter
-- [TABLET NODE: ProbabilityBoundedKernelSquare]
theorem ProbabilityBoundedKernelSquare {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (q : Ω→Ω→ℝ) (A B : ℝ)
    (hqm : Measurable (fun p : Ω×Ω => q p.1 p.2))
    (hqb : ∀x y,|q x y|≤A) (hrow : ∀x,(∫y,(q x y)^2∂μ)≤B) :
    (∫x,∫y,(q x y)^2∂μ∂μ)≤B ∧
    Integrable (fun p : Ω×Ω => (q p.1 p.2)^2) (μ.prod μ) := by
-- BODY
  constructor
  · have hh := integral_mono_of_nonneg (μ:=μ)
      (Eventually.of_forall fun x => integral_nonneg (fun y => sq_nonneg _))
      (integrable_const B) (Eventually.of_forall hrow)
    simpa using hh
  · have hi : Integrable (fun p : Ω×Ω => q p.1 p.2*q p.1 p.2) (μ.prod μ) :=
      Integrable.of_bound (hqm.mul hqm).aestronglyMeasurable (A^2)
        (Eventually.of_forall fun p => by
          rw [←pow_two,norm_pow,Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hqb p.1 p.2) 2)
    simpa only [pow_two] using hi
