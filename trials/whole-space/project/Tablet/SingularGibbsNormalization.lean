module

public import Tablet.GibbsLaw
public import Tablet.InteractionWeightBounds
public import Tablet.InteractionWeightMeasurable
public import Tablet.ConfigurationReferenceProbability
public import Tablet.ConfigurationCollisionNull

@[expose] public section
open MeasureTheory Filter

-- [TABLET NODE: SingularGibbsNormalization]
theorem SingularGibbsNormalization {d N : ℕ} (hd : 0 < d)
    (μ : Measure (OneParticle d)) [IsProbabilityMeasure μ]
    (hμ : μ ≪ (volume : Measure (OneParticle d)))
    (s coupling : ℝ) (hs : 0 < s) (hc : 0 ≤ coupling) :
    Integrable (InteractionWeight (d := d) (N := N) s coupling 0)
      (ConfigurationReference d N μ) ∧
    (0 < GibbsPartition (N := N) μ s coupling 0 ∧
      GibbsPartition (N := N) μ s coupling 0 ≤ 1) ∧
    IsProbabilityMeasure (GibbsLaw (N := N) μ s coupling 0) := by
-- BODY
  classical
  let Q := ConfigurationReference d N μ
  let : IsProbabilityMeasure Q := ConfigurationReferenceProbability d N μ
  have hb := (InteractionWeightBounds (d := d) (N := N) s coupling 0 hs hc le_rfl).1
  have hi : Integrable (InteractionWeight s coupling 0) Q := by
    apply (integrable_const (1 : ℝ)).mono_nonneg
      (InteractionWeightMeasurable s coupling 0).aestronglyMeasurable
    · exact Eventually.of_forall (fun X => (hb X).1)
    · exact Eventually.of_forall (fun X => (hb X).2)
  have hfree : ∀ᵐ X : ParticleConfig d N ∂Q, X ∉ CollisionSet d N := by
    rw [ae_iff]
    simpa only [not_not, Set.setOf_mem_eq, Q] using ConfigurationCollisionNull d N hd μ hμ
  have hp : 0 < GibbsPartition (N := N) μ s coupling 0 := by
    unfold GibbsPartition
    apply (integral_pos_iff_support_of_nonneg (fun X => (hb X).1) hi).2
    have hsupport : Function.support (InteractionWeight (d := d) (N := N) s coupling 0)
        =ᵐ[Q] Set.univ := by
      filter_upwards [hfree] with X hX
      have hpos : 0 < InteractionWeight s coupling 0 X := by
        unfold InteractionWeight
        simp only [hX, and_false, ↓reduceIte]
        split_ifs
        · exact zero_lt_one
        · exact Real.exp_pos _
      change (InteractionWeight s coupling 0 X ≠ 0) = True
      exact propext ⟨fun _ => trivial, fun _ => ne_of_gt hpos⟩
    rw [measure_congr hsupport]
    change 0 < Q Set.univ
    simp
  have hle : GibbsPartition (N := N) μ s coupling 0 ≤ 1 := by
    unfold GibbsPartition
    calc
      _ ≤ ∫ _ : ParticleConfig d N, (1 : ℝ) ∂Q :=
        integral_mono hi (integrable_const _) (fun X => (hb X).2)
      _ = 1 := by simp
  refine ⟨hi, ⟨hp, hle⟩, ?_⟩
  constructor
  unfold GibbsLaw
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_const_mul]
    change ENNReal.ofReal ((GibbsPartition (N := N) μ s coupling 0)⁻¹ *
      GibbsPartition (N := N) μ s coupling 0) = 1
    simp [ne_of_gt hp]
  · exact hi.const_mul _
  · exact Eventually.of_forall (fun X => mul_nonneg (inv_nonneg.mpr hp.le) (hb X).1)
