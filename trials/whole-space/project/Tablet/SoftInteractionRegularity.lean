module

public import Tablet.InteractionWeight
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

@[expose] public section

-- [TABLET NODE: SoftInteractionRegularity]
theorem SoftInteractionRegularity {d N : ℕ} (s coupling ε : ℝ)
    (_hs : 0 < s) (_hc : 0 ≤ coupling) (hε : 0 < ε) :
    Continuous (InteractionWeight (d := d) (N := N) s coupling ε) ∧
    ∀ X : ParticleConfig d N, 0 < InteractionWeight s coupling ε X := by
-- BODY
  have hε0 : ε ≠ 0 := ne_of_gt hε
  have hp : ∀ i : Fin N, Continuous (fun X : ParticleConfig d N => ParticlePosition X i) := by
    intro i
    unfold ParticlePosition
    apply (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp
    exact continuous_pi (fun k => PiLp.continuous_apply 2
      (fun _ : Fin N × Fin d => ℝ) (i, k))
  have hk : Continuous (RieszKernel (d := d) s ε) := by
    have heq : RieszKernel (d := d) s ε =
        fun x => (‖x‖ ^ 2 + ε ^ 2) ^ (-s / 2 : ℝ) / s := by
      funext x
      simp [RieszKernel, hε0]
    rw [heq]
    apply Continuous.div_const
    apply Continuous.rpow_const
    · exact continuous_norm.pow 2 |>.add continuous_const
    · intro x
      left
      exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε))
  have hU : Continuous (PairInteraction (d := d) (N := N) s coupling ε) := by
    unfold PairInteraction
    apply Continuous.const_mul
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    by_cases hij : i < j
    · simp only [hij, if_true]
      exact hk.comp ((hp i).sub (hp j))
    · simp only [hij, if_false]
      exact continuous_const
  by_cases hc : coupling = 0
  · have heq : InteractionWeight (d := d) (N := N) s coupling ε =
        fun _ => (1 : ℝ) := by
      funext X
      simp [InteractionWeight, hc]
    rw [heq]
    exact ⟨continuous_const, fun _ => zero_lt_one⟩
  · have heq : InteractionWeight (d := d) (N := N) s coupling ε =
        fun X => Real.exp (-PairInteraction s coupling ε X) := by
      funext X
      simp [InteractionWeight, hc, hε0]
    rw [heq]
    exact ⟨Real.continuous_exp.comp hU.neg, fun _ => Real.exp_pos _⟩
