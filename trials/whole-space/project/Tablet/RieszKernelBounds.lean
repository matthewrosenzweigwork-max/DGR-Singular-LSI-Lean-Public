import Tablet.RieszKernel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

-- [TABLET NODE: RieszKernelBounds]
theorem RieszKernelBounds {d : ℕ} (s ε : ℝ) (hs : 0 < s) (_hε : 0 ≤ ε) :
    (∀ x : OneParticle d, 0 ≤ RieszKernel s ε x) ∧
    (∀ x : OneParticle d, x ≠ 0 → RieszKernel s ε x ≤ RieszKernel s 0 x) := by
-- BODY
  constructor
  · intro x
    unfold RieszKernel
    split
    · exact div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hs.le
    · exact div_nonneg (Real.rpow_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) _) hs.le
  · intro x hx
    by_cases hε : ε = 0
    · simp [hε]
    · simp only [RieszKernel, hε, if_false, if_true]
      apply div_le_div_of_nonneg_right _ hs.le
      have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hp : (‖x‖ ^ 2) ^ (-s / 2 : ℝ) = ‖x‖ ^ (-s : ℝ) := by
        rw [← Real.rpow_natCast_mul (norm_nonneg x) 2]
        congr 1
        ring
      rw [← hp]
      exact Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hnorm)
        (le_add_of_nonneg_right (sq_nonneg ε)) (by linarith)
