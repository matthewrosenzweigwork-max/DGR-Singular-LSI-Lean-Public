import Tablet.CompactGradientCalculus
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Analysis.SpecificLimits.Basic
open Filter Set
open scoped Topology ContDiff

-- [TABLET NODE: SpatialCutoffApproximation]
theorem SpatialCutoffApproximation {ι : Type*} [Fintype ι] :
    ∃ (χ : ℕ → EuclideanSpace ℝ ι → ℝ) (C : ℝ), 0 ≤ C ∧
      (∀ n, ContDiff ℝ ∞ (χ n) ∧ HasCompactSupport (χ n)) ∧
      (∀ n X, 0 ≤ χ n X ∧ χ n X ≤ 1) ∧
      (∀ X, Tendsto (fun n => χ n X) atTop (𝓝 (1 : ℝ))) ∧
      (∀ n X, ‖EuclideanGradient (χ n) X‖ ≤ C / ((n : ℝ) + 1)) := by
-- BODY
  let η : ContDiffBump (0 : EuclideanSpace ℝ ι) := ⟨1, 2, by norm_num, by norm_num⟩
  let χ := fun (n : ℕ) (X : EuclideanSpace ℝ ι) => η (((n : ℝ) + 1)⁻¹ • X)
  have hηs : ContDiff ℝ ∞ (η : EuclideanSpace ℝ ι → ℝ) := η.contDiff
  obtain ⟨C, hC⟩ := (CompactGradientCalculus η hηs η.hasCompactSupport).2.1.exists_bound_of_continuous
    (CompactGradientCalculus η hηs η.hasCompactSupport).1
  refine ⟨χ, C, (norm_nonneg (EuclideanGradient η 0)).trans (hC 0), ?_, ?_, ?_, ?_⟩
  · intro n
    have hn : ((n : ℝ) + 1)⁻¹ ≠ 0 := inv_ne_zero (by positivity)
    constructor
    · dsimp [χ]
      fun_prop
    · exact η.hasCompactSupport.comp_homeomorph (Homeomorph.smulOfNeZero _ hn)
  · intro n X
    exact ⟨η.nonneg, η.le_one⟩
  · intro X
    have hi : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) := by
      simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0))
    have hv := hi.smul_const X
    have hzero : η 0 = 1 := by
      apply η.one_of_mem_closedBall
      simp [η]
    convert η.continuous.continuousAt.tendsto.comp hv using 1 <;>
      first | rfl | simp [zero_smul, hzero]
  · intro n X
    rw [show EuclideanGradient (χ n) X = ((n : ℝ) + 1)⁻¹ •
      EuclideanGradient η (((n : ℝ) + 1)⁻¹ • X) from
        (CompactGradientCalculus η hηs η.hasCompactSupport).2.2 _ X]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ((n : ℝ) + 1)⁻¹)]
    exact (mul_le_mul_of_nonneg_left (hC _) (by positivity)).trans_eq (by ring)
