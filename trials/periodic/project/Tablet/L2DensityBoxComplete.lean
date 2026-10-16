import Tablet.Preamble
import Mathlib.MeasureTheory.Function.LpOrder

open MeasureTheory
open scoped Topology

-- [TABLET NODE: L2DensityBoxComplete]
theorem L2DensityBoxComplete {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (M : ℝ) (hM : 1 ≤ M) :
    IsClosed {f : Lp ℝ 2 μ | (∀ᵐ x ∂μ, f x ∈ Set.Icc 0 M) ∧ (∫ x, f x ∂μ) = 1} ∧
    IsComplete {f : Lp ℝ 2 μ | (∀ᵐ x ∂μ, f x ∈ Set.Icc 0 M) ∧ (∫ x, f x ∂μ) = 1} ∧
    Set.Nonempty {f : Lp ℝ 2 μ | (∀ᵐ x ∂μ, f x ∈ Set.Icc 0 M) ∧ (∫ x, f x ∂μ) = 1} := by
-- BODY
  classical
  let one : Lp ℝ 2 μ := (memLp_const (1 : ℝ)).toLp (fun _ : Ω => 1)
  let cap : Lp ℝ 2 μ := (memLp_const M).toLp (fun _ : Ω => M)
  have hone : ∀ᵐ x ∂μ, one x = 1 := MemLp.coeFn_toLp _
  have hcap : ∀ᵐ x ∂μ, cap x = M := MemLp.coeFn_toLp _
  have hmass : Continuous (fun f : Lp ℝ 2 μ => ∫ x, f x ∂μ) := by
    have h := (continuous_const : Continuous (fun _ : Lp ℝ 2 μ => one)).inner continuous_id (𝕜 := ℝ)
    convert! h using 1
    funext f
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hone] with x hx
    simp [hx]
  have heq : {f : Lp ℝ 2 μ | ∀ᵐ x ∂μ, f x ∈ Set.Icc 0 M} = Set.Icc 0 cap := by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_Icc]
    rw [← Lp.coeFn_nonneg f, ← Lp.coeFn_le f cap]
    constructor
    · intro hf
      refine ⟨hf.mono fun _ hx => hx.1, ?_⟩
      filter_upwards [hf, hcap] with x hx hc
      simpa [hc] using hx.2
    · intro hf
      filter_upwards [hf.1, hf.2, hcap] with x hn hu hc
      exact ⟨hn, by simpa [hc] using hu⟩
  have hclosed : IsClosed {f : Lp ℝ 2 μ |
      (∀ᵐ x ∂μ, f x ∈ Set.Icc 0 M) ∧ (∫ x, f x ∂μ) = 1} := by
    have hbox : IsClosed {f : Lp ℝ 2 μ | ∀ᵐ x ∂μ, f x ∈ Set.Icc 0 M} := by
      rw [heq]
      exact isClosed_Icc
    exact hbox.inter (isClosed_eq hmass continuous_const)
  refine ⟨hclosed, hclosed.isComplete, one, ?_, ?_⟩
  · filter_upwards [hone] with x hx
    simp [hx, hM]
  · rw [integral_congr_ae hone]
    simp
