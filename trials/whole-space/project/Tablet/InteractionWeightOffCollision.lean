import Tablet.InteractionWeight
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
open Set Filter
open scoped BigOperators

-- [TABLET NODE: InteractionWeightOffCollision]
theorem InteractionWeightOffCollision {d N : ℕ} (s coupling ε : ℝ) :
    ContinuousOn (InteractionWeight (d := d) (N := N) s coupling ε) (CollisionSet d N)ᶜ ∧
    ∀ X : ParticleConfig d N, X ∉ CollisionSet d N → 0 < InteractionWeight s coupling ε X := by
-- BODY
  classical
  have hp (i : Fin N) : Continuous (fun X : ParticleConfig d N => ParticlePosition X i) := by
    unfold ParticlePosition
    fun_prop
  have hk (X : ParticleConfig d N) (i j : Fin N)
      (hij : ParticlePosition X i - ParticlePosition X j ≠ 0) :
      ContinuousAt (fun Y : ParticleConfig d N => RieszKernel s ε (ParticlePosition Y i - ParticlePosition Y j)) X := by
    unfold RieszKernel
    by_cases he : ε = 0
    · simp only [he, if_true]
      exact (((hp i).sub (hp j)).continuousAt.norm.rpow_const
        (Or.inl (norm_ne_zero_iff.2 hij))).div_const s
    · simp only [he, if_false]
      have hn : ‖ParticlePosition X i - ParticlePosition X j‖^2 + ε^2 ≠ 0 :=
        ne_of_gt (add_pos_of_pos_of_nonneg
          (sq_pos_of_ne_zero (norm_ne_zero_iff.2 hij)) (sq_nonneg ε))
      exact (((((hp i).sub (hp j)).continuousAt.norm.pow 2).add_const (ε^2)).rpow_const
        (Or.inl hn)).div_const s
  have hU : ContinuousOn (PairInteraction (d := d) (N := N) s coupling ε) (CollisionSet d N)ᶜ := by
    intro X hX
    apply ContinuousAt.continuousWithinAt
    change Tendsto _ (nhds X) (nhds _)
    unfold PairInteraction
    apply Filter.Tendsto.const_mul
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    by_cases hij : i < j
    · simp only [hij, if_true]
      exact hk X i j (fun hz => hX ⟨i, j, hij, sub_eq_zero.mp hz⟩)
    · simp only [hij, if_false]
      exact tendsto_const_nhds
  constructor
  · have heq : EqOn (InteractionWeight (d := d) (N := N) s coupling ε)
        (fun X => if coupling = 0 then (1 : ℝ) else Real.exp (-PairInteraction s coupling ε X))
        (CollisionSet d N)ᶜ := by
      intro X hX
      change X ∉ CollisionSet d N at hX
      simp [InteractionWeight, hX]
    apply ContinuousOn.congr _ heq
    by_cases hc : coupling = 0
    · simp only [hc, if_true]
      exact continuousOn_const
    · simp only [hc, if_false]
      exact Real.continuous_exp.comp_continuousOn hU.neg
  · intro X hX
    unfold InteractionWeight
    simp only [hX, and_false, if_false]
    split_ifs
    · exact zero_lt_one
    · exact Real.exp_pos _
