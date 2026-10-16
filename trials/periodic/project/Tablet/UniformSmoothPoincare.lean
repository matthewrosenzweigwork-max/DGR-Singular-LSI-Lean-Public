import Tablet.UniformRegularizedPoincare
import Tablet.CanonicalCutoffConvergence
import Mathlib.Probability.Moments.Variance
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
-- [TABLET NODE: UniformSmoothPoincare]
theorem UniformSmoothPoincare (d : ℕ) (hd : 2 ≤ d)
    (s a B l u : ℝ) (hs : 0 ≤ s) (hsd : s ≤ (d : ℝ) - 2)
    (ha : 0 < a) (hB : 0 ≤ B) (hl : 0 < l) (hl1 : l ≤ 1) (hu : 1 ≤ u) :
    ∃ rate : ℝ, 0 < rate ∧ ∀ (N : ℕ), 2 ≤ N →
      ∀ (β : ℝ), 0 ≤ β → β ≤ B → ∀ (q : BoundedBackground d l u),
      ∀ (ε : ℝ), 0 ≤ ε → ∀ (f : Configuration d N → ℝ),
      f ∈ SmoothCore d N →
        ProbabilityTheory.variance f
          (CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β) ≤
        rate⁻¹ * PhysicalEnergy
          (CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β) f := by
-- BODY
  have smooth_cutoff_variance_energy (d N : ℕ)
      (P : ℝ → Measure (Configuration d N))
      (hP : ∀ ε : ℝ, 0 ≤ ε → IsProbabilityMeasure (P ε))
      (hweak : ∀ h : Configuration d N → ℝ, Measurable h →
        (∃ C : ℝ, ∀ X, |h X| ≤ C) →
        Tendsto (fun ε => ∫ X, h X ∂P ε) (𝓝[>] 0) (𝓝 (∫ X, h X ∂P 0)))
      (f : Configuration d N → ℝ) (hf : f ∈ SmoothCore d N) :
      Tendsto (fun ε => variance f (P ε)) (𝓝[>] 0) (𝓝 (variance f (P 0))) ∧
      Tendsto (fun ε => PhysicalEnergy (P ε) f) (𝓝[>] 0)
        (𝓝 (PhysicalEnergy (P 0) f)) := by
    have hc := (ConfigurationCalculus d N).2.2.2 f hf
    obtain ⟨C,hC⟩ := hc.2.2.1
    have hC2 : ∃D : ℝ, ∀X, |f X ^ 2| ≤ D := by
      refine ⟨C^2,fun X => ?_⟩
      rw [abs_of_nonneg (sq_nonneg (f X))]
      simpa only [sq_abs] using
        pow_le_pow_left₀ (abs_nonneg (f X)) (hC X) 2
    have hlim := (hweak (fun X => f X ^ 2) (hc.2.1.pow_const 2) hC2).sub
      ((hweak f hc.2.1 ⟨C,hC⟩).pow 2)
    have hmem (ε : ℝ) (hε : 0 ≤ ε) : MemLp f 2 (P ε) := by
      letI := hP ε hε
      exact MemLp.of_bound hc.2.1.aestronglyMeasurable C
        (Eventually.of_forall fun X => by simpa only [Real.norm_eq_abs] using hC X)
    letI := hP 0 (le_refl 0)
    have hV0 := variance_eq_sub (hmem 0 (le_refl 0))
    change variance f (P 0) = (∫ X, f X ^ 2 ∂P 0) - (∫ X, f X ∂P 0)^2 at hV0
    rw [←hV0] at hlim
    refine ⟨hlim.congr' ?_, ?_⟩
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      letI := hP ε (le_of_lt hε)
      exact (variance_eq_sub (hmem ε (le_of_lt hε))).symm
    · obtain ⟨D,hD⟩ := hc.2.2.2.2.1
      exact hweak (fun X => ‖CoordinateGradient f X‖^2) hc.2.2.2.1
        ⟨D,fun X => by simpa only [abs_of_nonneg (sq_nonneg ‖CoordinateGradient f X‖)] using hD X⟩
  
  have smooth_cutoff_poincare_passage (d N : ℕ)
      (P : ℝ → Measure (Configuration d N))
      (hP : ∀ ε : ℝ, 0 ≤ ε → IsProbabilityMeasure (P ε))
      (hweak : ∀ h : Configuration d N → ℝ, Measurable h →
        (∃ C : ℝ, ∀ X, |h X| ≤ C) →
        Tendsto (fun ε => ∫ X, h X ∂P ε) (𝓝[>] 0) (𝓝 (∫ X, h X ∂P 0)))
      (rate : ℝ)
      (hPI : ∀ ε : ℝ, 0 < ε → ∀ f : Configuration d N → ℝ,
        f ∈ SmoothCore d N → variance f (P ε) ≤ rate⁻¹ * PhysicalEnergy (P ε) f)
      (f : Configuration d N → ℝ) (hf : f ∈ SmoothCore d N) :
      variance f (P 0) ≤ rate⁻¹ * PhysicalEnergy (P 0) f := by
    obtain ⟨hV,hE⟩ := smooth_cutoff_variance_energy d N P hP hweak f hf
    apply le_of_tendsto_of_tendsto hV (hE.const_mul rate⁻¹)
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hPI ε hε f hf
  obtain ⟨rate, hrate, hPI⟩ := UniformRegularizedPoincare d hd s a B l u hs hsd ha hB hl hl1 hu
  refine ⟨rate, hrate, ?_⟩
  intro N hN β hβ hβB q ε hε f hf
  by_cases hε0 : ε = 0
  · subst ε
    have hsd' : s < (d : ℝ) := by linarith
    have hlaw := CanonicalCutoffConvergence d N hd hN s a l u β hs hsd' ha q hβ
    exact smooth_cutoff_poincare_passage d N
      (fun ε => CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β)
      hlaw.1 hlaw.2.2.2 rate (hPI N hN β hβ hβB q) f hf
  · exact hPI N hN β hβ hβB q ε (lt_of_le_of_ne hε (Ne.symm hε0)) f hf
