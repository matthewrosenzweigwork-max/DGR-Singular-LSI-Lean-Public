module

public import Tablet.GibbsLaw
public import Tablet.InteractionWeightBounds
public import Tablet.SoftInteractionRegularity
public import Tablet.ConfigurationReferenceProbability

@[expose] public section

-- [TABLET NODE: SoftGibbsNormalization]
theorem SoftGibbsNormalization {d N : ℕ}
    (μ : MeasureTheory.Measure (OneParticle d)) [MeasureTheory.IsProbabilityMeasure μ]
    (s coupling ε : ℝ) (hs : 0 < s) (hc : 0 ≤ coupling) (hε : 0 < ε) :
    MeasureTheory.Integrable (InteractionWeight (d := d) (N := N) s coupling ε)
      (ConfigurationReference d N μ) ∧
    (0 < GibbsPartition (N := N) μ s coupling ε ∧
      GibbsPartition (N := N) μ s coupling ε ≤ 1) ∧
    MeasureTheory.IsProbabilityMeasure (GibbsLaw (N := N) μ s coupling ε) := by
-- BODY
  let Q := ConfigurationReference d N μ
  let : MeasureTheory.IsProbabilityMeasure Q := ConfigurationReferenceProbability d N μ
  have hw := SoftInteractionRegularity (d := d) (N := N) s coupling ε hs hc hε
  have hb := (InteractionWeightBounds (d := d) (N := N) s coupling ε hs hc hε.le).1
  have hi : MeasureTheory.Integrable (InteractionWeight s coupling ε) Q := by
    apply (MeasureTheory.integrable_const (1 : ℝ)).mono_nonneg hw.1.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun X => (hb X).1)
    · exact Filter.Eventually.of_forall (fun X => (hb X).2)
  have hp : 0 < GibbsPartition (N := N) μ s coupling ε := by
    unfold GibbsPartition
    rw [MeasureTheory.integral_pos_iff_support_of_nonneg (fun X => (hb X).1) hi]
    have hsupp : Function.support (InteractionWeight (d := d) (N := N) s coupling ε) =
        Set.univ := by
      apply Set.eq_univ_of_forall
      intro X
      exact ne_of_gt (hw.2 X)
    rw [hsupp]
    change 0 < Q Set.univ
    simp
  have hle : GibbsPartition (N := N) μ s coupling ε ≤ 1 := by
    unfold GibbsPartition
    calc
      _ ≤ ∫ _ : ParticleConfig d N, (1 : ℝ) ∂Q :=
        MeasureTheory.integral_mono hi (MeasureTheory.integrable_const _) (fun X => (hb X).2)
      _ = 1 := by simp
  refine ⟨hi, ⟨hp, hle⟩, ?_⟩
  constructor
  unfold GibbsLaw
  rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ, MeasureTheory.Measure.restrict_univ]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
  · rw [MeasureTheory.integral_const_mul]
    change ENNReal.ofReal ((GibbsPartition (N := N) μ s coupling ε)⁻¹ *
      GibbsPartition (N := N) μ s coupling ε) = 1
    simp [ne_of_gt hp]
  · exact hi.const_mul _
  · exact Filter.Eventually.of_forall (fun X =>
      mul_nonneg (inv_nonneg.mpr hp.le) (hb X).1)
