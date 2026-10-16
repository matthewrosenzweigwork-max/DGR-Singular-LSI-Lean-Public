module

public import Tablet.Preamble
public import Mathlib.Tactic.Linarith

@[expose] public section
open scoped NNReal

-- [TABLET NODE: SobolevExponent]
noncomputable def SobolevExponent (n : ℕ) (hn : 3 ≤ n) : ℝ≥0 :=
-- BODY
  ⟨2 * (n : ℝ) / ((n : ℝ) - 2), by
    have h : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hden : 0 < (n : ℝ) - 2 := by linarith
    positivity⟩
