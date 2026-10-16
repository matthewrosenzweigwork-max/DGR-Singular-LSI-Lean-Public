module

public import Tablet.InteractionWeight
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

@[expose] public section
open Filter Set
open scoped Topology BigOperators

-- [TABLET NODE: InteractionWeightCutoffLimit]
theorem InteractionWeightCutoffLimit {d N : ℕ} (s coupling : ℝ)
    (X : ParticleConfig d N) (hX : X ∉ CollisionSet d N) :
    Tendsto (fun ε : ℝ => InteractionWeight s coupling ε X) (𝓝 0)
      (𝓝 (InteractionWeight s coupling 0 X)) := by
-- BODY
  classical
  have hk (x : OneParticle d) (hx : x ≠ 0) :
      Tendsto (fun ε : ℝ => RieszKernel s ε x) (𝓝 0) (𝓝 (RieszKernel s 0 x)) := by
    have heq (ε : ℝ) : RieszKernel s ε x = (‖x‖^2 + ε^2)^(-s / 2 : ℝ) / s := by
      unfold RieszKernel
      split_ifs with hε
      · subst ε
        simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
        rw [← Real.rpow_natCast_mul (norm_nonneg _) 2 (-s / 2)]
        congr 2
        ring
      · rfl
    have hn : ‖x‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hx)
    have ht : Tendsto (fun ε : ℝ => ‖x‖^2 + ε^2) (𝓝 0) (𝓝 (‖x‖^2)) := by
      convert (((continuous_const.add (continuous_id.pow 2)) :
        Continuous (fun ε : ℝ => ‖x‖^2 + ε^2)).tendsto (0 : ℝ)) using 1
      all_goals first | rfl | simp
    have hp := (Real.continuousAt_rpow_const _ (-s / 2) (Or.inl hn)).tendsto.comp ht
    simpa only [heq, Function.comp_def, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] using hp.div_const s
  have he : Tendsto (fun ε : ℝ => PairInteraction s coupling ε X) (𝓝 0)
      (𝓝 (PairInteraction s coupling 0 X)) := by
    unfold PairInteraction
    apply Tendsto.const_mul
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    by_cases hij : i < j
    · simp only [hij, if_true]
      apply hk
      exact fun hz => hX ⟨i, j, hij, sub_eq_zero.mp hz⟩
    · simp only [hij, if_false]
      exact tendsto_const_nhds
  unfold InteractionWeight
  simp only [hX, and_false, if_false]
  by_cases hc : coupling = 0
  · simp only [hc, if_true]
    exact tendsto_const_nhds
  · simp only [hc, if_false]
    exact Real.continuous_exp.continuousAt.tendsto.comp he.neg
