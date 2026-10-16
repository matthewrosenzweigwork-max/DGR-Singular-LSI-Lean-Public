module

public import Tablet.Preamble
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Sequences

@[expose] public section

open MeasureTheory Filter
open scoped Topology

-- [TABLET NODE: L2BoxContinuousIntegral]
theorem L2BoxContinuousIntegral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (M : ℝ)
    (φ : ℝ → ℝ) (hφ : Continuous φ) :
    Continuous (fun f : {f : Lp ℝ 2 μ // ∀ᵐ x ∂μ, f x ∈ Set.Icc 0 M} =>
      ∫ x, φ (f.val x) ∂μ) := by
-- BODY
  apply SeqContinuous.continuous
  intro u r hur
  have hLp : Tendsto (fun n => (u n).val) atTop (𝓝 r.val) :=
    continuous_subtype_val.tendsto r |>.comp hur
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) M)).exists_bound_of_continuousOn
    hφ.continuousOn
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms, _, hmae⟩ := (tendstoInMeasure_of_tendsto_Lp (hLp.comp hns)).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω => C)
  · intro n
    exact hφ.comp_aestronglyMeasurable (Lp.aestronglyMeasurable (u (ns (ms n))).val)
  · exact integrable_const C
  · intro n
    exact (u (ns (ms n))).property.mono fun x hx => hC ((u (ns (ms n))).val x) hx
  · exact hmae.mono fun x hx => (hφ.tendsto (r.val x)).comp hx
