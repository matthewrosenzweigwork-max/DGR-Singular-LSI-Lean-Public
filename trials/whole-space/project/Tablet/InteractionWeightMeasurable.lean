import Tablet.InteractionWeight
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
open MeasureTheory

-- [TABLET NODE: InteractionWeightMeasurable]
theorem InteractionWeightMeasurable {d N : ℕ} (s coupling ε : ℝ) :
    Measurable (InteractionWeight (d := d) (N := N) s coupling ε) := by
-- BODY
  classical
  have hposition (i : Fin N) : Measurable (fun X : ParticleConfig d N => ParticlePosition X i) := by
    have : Continuous (fun X : ParticleConfig d N => ParticlePosition X i) := by
      unfold ParticlePosition
      fun_prop
    exact this.measurable
  have hkernel : Measurable (RieszKernel (d := d) s ε) := by
    unfold RieszKernel
    split_ifs
    · exact (measurable_norm.pow_const _).div_const _
    · exact ((measurable_norm.pow_const 2).add_const (ε ^ 2)).pow_const _ |>.div_const _
  have hpair : Measurable (PairInteraction (d := d) (N := N) s coupling ε) := by
    unfold PairInteraction
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i _
    apply Finset.measurable_sum
    intro j _
    split_ifs
    · exact hkernel.comp ((hposition i).sub (hposition j))
    · exact measurable_const
  have hcollision : MeasurableSet (CollisionSet d N) := by
    have heq : CollisionSet d N = ⋃ i : Fin N, ⋃ j : Fin N,
        {X : ParticleConfig d N | i < j ∧ ParticlePosition X i = ParticlePosition X j} := by
      ext X
      simp [CollisionSet]
    rw [heq]
    apply MeasurableSet.iUnion
    intro i
    apply MeasurableSet.iUnion
    intro j
    by_cases hij : i < j
    · simp only [hij, true_and]
      exact measurableSet_eq_fun (hposition i) (hposition j)
    · simp [hij]
  unfold InteractionWeight
  by_cases hc : coupling = 0
  · simp only [hc, ↓reduceIte]
    exact measurable_const
  · simp only [hc, ↓reduceIte]
    apply Measurable.ite
    · by_cases he : ε = 0
      · simpa [he] using hcollision
      · simp [he]
    · exact measurable_const
    · exact Real.measurable_exp.comp hpair.neg
