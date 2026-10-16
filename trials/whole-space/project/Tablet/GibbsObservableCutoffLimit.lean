import Tablet.InteractionWeightCutoffLimit
import Tablet.SingularGibbsNormalization
import Tablet.SoftGibbsNormalization
open MeasureTheory Filter Set
open scoped Topology

-- [TABLET NODE: GibbsObservableCutoffLimit]
theorem GibbsObservableCutoffLimit {d N : ℕ} (hd : 0 < d)
    (μ : Measure (OneParticle d)) [IsProbabilityMeasure μ]
    (hμ : μ ≪ (volume : Measure (OneParticle d)))
    (s coupling : ℝ) (hs : 0 < s) (hc : 0 ≤ coupling)
    (f : ParticleConfig d N → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : 0 ≤ C) (hfC : ∀ X, |f X| ≤ C) :
    Tendsto (fun ε : ℝ => GibbsPartition (N := N) μ s coupling ε) (𝓝[≥] 0)
      (𝓝 (GibbsPartition (N := N) μ s coupling 0)) ∧
    Tendsto (fun ε : ℝ => ∫ X, f X ∂GibbsLaw (N := N) μ s coupling ε) (𝓝[≥] 0)
      (𝓝 (∫ X, f X ∂GibbsLaw (N := N) μ s coupling 0)) := by
-- BODY
  let Q := ConfigurationReference d N μ
  let : IsProbabilityMeasure Q := ConfigurationReferenceProbability d N μ
  have hfree : ∀ᵐ X : ParticleConfig d N ∂Q, X ∉ CollisionSet d N := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq, Q] using ConfigurationCollisionNull d N hd μ hμ
  have hweight : Tendsto (fun ε : ℝ => GibbsPartition (N := N) μ s coupling ε)
      (𝓝[≥] 0) (𝓝 (GibbsPartition (N := N) μ s coupling 0)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
    · exact Eventually.of_forall (fun ε => (InteractionWeightMeasurable s coupling ε).aestronglyMeasurable)
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact Eventually.of_forall (fun X => by
        have hb := (InteractionWeightBounds (d := d) (N := N) s coupling ε hs hc hε).1 X
        rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
        exact hb.2)
    · exact integrable_const _
    · exact hfree.mono (fun X hX => (InteractionWeightCutoffLimit s coupling X hX).mono_left nhdsWithin_le_nhds)
  have hweighted : Tendsto (fun ε : ℝ => ∫ X, f X * InteractionWeight s coupling ε X ∂Q)
      (𝓝[≥] 0) (𝓝 (∫ X, f X * InteractionWeight s coupling 0 X ∂Q)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => C)
    · exact Eventually.of_forall (fun ε => hf.aestronglyMeasurable.mul
        (InteractionWeightMeasurable s coupling ε).aestronglyMeasurable)
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact Eventually.of_forall (fun X => by
        rw [norm_mul, Real.norm_eq_abs (f X)]
        have hw : ‖InteractionWeight s coupling ε X‖ ≤ 1 := by
          have hb := (InteractionWeightBounds (d := d) (N := N) s coupling ε hs hc hε).1 X
          rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
          exact hb.2
        exact (mul_le_mul (hfC X) hw (norm_nonneg _) hC).trans_eq (mul_one C))
    · exact integrable_const _
    · exact hfree.mono (fun X hX =>
        ((InteractionWeightCutoffLimit s coupling X hX).mono_left nhdsWithin_le_nhds).const_mul (f X))
  have hz0 := (SingularGibbsNormalization (N := N) hd μ hμ s coupling hs hc).2.1.1
  have hratio (ε : ℝ) (hε : 0 ≤ ε) :
      (∫ X, f X ∂GibbsLaw (N := N) μ s coupling ε) =
        (∫ X, f X * InteractionWeight s coupling ε X ∂Q) / GibbsPartition (N := N) μ s coupling ε := by
    have hz : 0 < GibbsPartition (N := N) μ s coupling ε := by
      by_cases he : ε = 0
      · subst ε
        exact hz0
      · exact (SoftGibbsNormalization μ s coupling ε hs hc (lt_of_le_of_ne hε (Ne.symm he))).2.1.1
    have hm : Measurable (fun X : ParticleConfig d N => ENNReal.ofReal
        ((GibbsPartition (N := N) μ s coupling ε)⁻¹ * InteractionWeight s coupling ε X)) :=
      ((InteractionWeightMeasurable s coupling ε).const_mul _).ennreal_ofReal
    unfold GibbsLaw
    rw [integral_withDensity_eq_integral_toReal_smul hm
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    have heq : (fun X : ParticleConfig d N =>
        (ENNReal.ofReal ((GibbsPartition (N := N) μ s coupling ε)⁻¹ * InteractionWeight s coupling ε X)).toReal • f X) =
        (fun X => (f X * InteractionWeight s coupling ε X) / GibbsPartition (N := N) μ s coupling ε) := by
      funext X
      rw [ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.mpr hz.le)
        ((InteractionWeightBounds s coupling ε hs hc hε).1 X).1), smul_eq_mul]
      ring
    rw [heq, integral_div]
  refine ⟨hweight, ?_⟩
  have hevent : (fun ε => ∫ X, f X ∂GibbsLaw (N := N) μ s coupling ε) =ᶠ[𝓝[≥] 0]
      (fun ε => (∫ X, f X * InteractionWeight s coupling ε X ∂Q) / GibbsPartition (N := N) μ s coupling ε) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hratio ε hε
  rw [hratio 0 le_rfl]
  exact (hweighted.div hweight (ne_of_gt hz0)).congr' hevent.symm
