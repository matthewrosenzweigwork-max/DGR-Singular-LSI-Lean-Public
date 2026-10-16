import Tablet.ForceExponent
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

-- [TABLET NODE: ForceExponentRange]
theorem ForceExponentRange (s : ℝ) (hs : 0 < s) :
    0 < ForceExponent s ∧ ForceExponent s < 2 := by
-- BODY
  unfold ForceExponent
  have hp : 0 < s + 1 := by linarith
  constructor
  · exact div_pos (by norm_num) hp
  · apply (div_lt_iff₀ hp).2
    linarith
