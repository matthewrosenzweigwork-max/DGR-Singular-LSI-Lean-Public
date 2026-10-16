module

public import Tablet.ConfigurationTranslation
public import Tablet.InteractionWeight
public import Tablet.EuclideanGradient
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Tactic.Abel

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped ContDiff ENNReal
noncomputable section

-- [TABLET NODE: ConfigurationTranslationGeometry]
theorem ConfigurationTranslationGeometry {d N : ℕ} (a : OneParticle d) (s coupling ε : ℝ) :
    (∀ X : ParticleConfig d N, (ConfigurationTranslation a) X ∈ CollisionSet d N ↔ X ∈ CollisionSet d N) ∧
    (∀ X : ParticleConfig d N, PairInteraction s coupling ε ((ConfigurationTranslation a) X) = PairInteraction s coupling ε X) ∧
    (∀ X : ParticleConfig d N, InteractionWeight s coupling ε ((ConfigurationTranslation a) X) = InteractionWeight s coupling ε X) ∧
    (∀ (f : ParticleConfig d N → ℝ) X, EuclideanGradient (fun Y => f ((ConfigurationTranslation a) Y)) X = EuclideanGradient f ((ConfigurationTranslation a) X)) ∧
    (∀ (f : ParticleConfig d N → ℝ) X, EuclideanGradient (fun Y => f ((ConfigurationTranslation a).symm Y)) X = EuclideanGradient f ((ConfigurationTranslation a).symm X)) := by
-- BODY
  let A : ParticleConfig d N := WithLp.toLp 2 (fun ik : Fin N × Fin d => a ik.2)
  have hpos (X : ParticleConfig d N) (i : Fin N) :
      ParticlePosition (ConfigurationTranslation a X) i = ParticlePosition X i - a := by
    apply PiLp.ext
    intro k
    rfl
  have hpair (X : ParticleConfig d N) (i j : Fin N) :
      ParticlePosition (ConfigurationTranslation a X) i - ParticlePosition (ConfigurationTranslation a X) j =
        ParticlePosition X i - ParticlePosition X j := by
    rw [hpos, hpos]
    abel
  have hcollision (X : ParticleConfig d N) :
      ConfigurationTranslation a X ∈ CollisionSet d N ↔ X ∈ CollisionSet d N := by
    simp only [CollisionSet, Set.mem_setOf_eq, hpos, sub_left_inj]
  have hinteraction (X : ParticleConfig d N) :
      PairInteraction s coupling ε (ConfigurationTranslation a X) = PairInteraction s coupling ε X := by
    simp only [PairInteraction, hpair]
  refine ⟨hcollision, hinteraction, ?_, ?_, ?_⟩
  · intro X
    classical
    simp only [InteractionWeight, hcollision, hinteraction]
  · intro f X
    change gradient (fun Y => f (Y + (-A))) X = gradient f (X + (-A))
    unfold gradient
    rw [fderiv_comp_add_right]
  · intro f X
    change gradient (fun Y => f (Y + -(-A))) X = gradient f (X + -(-A))
    unfold gradient
    rw [fderiv_comp_add_right]
