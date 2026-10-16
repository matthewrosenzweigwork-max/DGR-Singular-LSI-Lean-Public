import Tablet.InteractionWeight
import Tablet.RieszKernelBounds

-- [TABLET NODE: InteractionWeightBounds]
theorem InteractionWeightBounds {d N : ℕ} (s coupling ε : ℝ)
    (hs : 0 < s) (hc : 0 ≤ coupling) (hε : 0 ≤ ε) :
    (∀ X : ParticleConfig d N, 0 ≤ InteractionWeight s coupling ε X ∧
      InteractionWeight s coupling ε X ≤ 1) ∧
    (∀ X : ParticleConfig d N, InteractionWeight s 0 ε X = 1) ∧
    (∀ X : ParticleConfig d N, coupling ≠ 0 → X ∈ CollisionSet d N →
      InteractionWeight s coupling 0 X = 0) := by
-- BODY
  have hU : ∀ X : ParticleConfig d N, 0 ≤ PairInteraction s coupling ε X := by
    intro X
    unfold PairInteraction
    apply mul_nonneg (div_nonneg hc (Nat.cast_nonneg _))
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    split
    · exact (RieszKernelBounds s ε hs hε).1 _
    · exact le_refl 0
  refine ⟨?_, ?_, ?_⟩
  · intro X
    unfold InteractionWeight
    split
    · exact ⟨zero_le_one, le_refl 1⟩
    · split
      · exact ⟨le_refl 0, zero_le_one⟩
      · exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hU X))⟩
  · intro X
    simp [InteractionWeight]
  · intro X hc0 hcol
    simp [InteractionWeight, hc0, hcol]
