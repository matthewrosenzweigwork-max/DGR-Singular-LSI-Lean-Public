import Tablet.CollisionSet
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

-- [TABLET NODE: CollisionNull]
theorem CollisionNull (d N : ℕ) (hd : 0 < d) :
    (MeasureTheory.volume : MeasureTheory.Measure (ParticleConfig d N)) (CollisionSet d N) = 0 := by
-- BODY
  classical
  let k : Fin d := ⟨0, hd⟩
  have hpair : ∀ i j : Fin N,
      (MeasureTheory.volume : MeasureTheory.Measure (ParticleConfig d N))
        {X | i < j ∧ ParticlePosition X i = ParticlePosition X j} = 0 := by
    intro i j
    by_cases hij : i < j
    · let T : ParticleConfig d N →ₗ[ℝ] ℝ :=
        { toFun := fun X => X (i, k) - X (j, k)
          map_add' := by intro X Y; simp; ring
          map_smul' := by intro a X; simp; ring }
      have hker : T.ker ≠ ⊤ := by
        intro htop
        have hm : EuclideanSpace.single (i, k) (1 : ℝ) ∈ T.ker := by
          rw [htop]
          exact Submodule.mem_top
        have hne : j ≠ i := ne_of_gt hij
        have hz : T (EuclideanSpace.single (i, k) (1 : ℝ)) = 0 := hm
        simp [T, hne] at hz
      apply MeasureTheory.measure_mono_null (t := (T.ker : Set (ParticleConfig d N))) _
        (MeasureTheory.Measure.addHaar_submodule MeasureTheory.volume T.ker hker)
      intro X hX
      change X (i, k) - X (j, k) = 0
      have he : (ParticlePosition X i) k = (ParticlePosition X j) k :=
        congrArg (fun x : OneParticle d => x k) hX.2
      exact sub_eq_zero.mpr he
    · simp [hij]
  have heq : CollisionSet d N =
      ⋃ i : Fin N, ⋃ j : Fin N, {X : ParticleConfig d N |
        i < j ∧ ParticlePosition X i = ParticlePosition X j} := by
    ext X
    simp [CollisionSet]
  rw [heq]
  exact MeasureTheory.measure_iUnion_null (fun i =>
    MeasureTheory.measure_iUnion_null (hpair i))
