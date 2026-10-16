import Tablet.GibbsObservableCutoffLimit
import Tablet.ConvexReferenceNormalization
import Tablet.CompactGradientCalculus
import Tablet.LawVariance
import Tablet.PhysicalEnergy
open MeasureTheory Filter
open scoped Topology ContDiff

-- [TABLET NODE: GibbsCompactTestCutoffLimit]
theorem GibbsCompactTestCutoffLimit {d N : ℕ} (hd : 0 < d) (V b : OneParticle d → ℝ)
    (κ L : ℝ) (hκ : 0 < κ) (hV : PotentialBounds d κ V)
    (hb : BoundedMultiplier d L b) (s coupling : ℝ) (hs : 0 < s) (hc : 0 ≤ coupling)
    (f : ParticleConfig d N → ℝ) (hfs : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    Tendsto (fun ε : ℝ => LawVariance (GibbsLaw (N := N) (ReferenceLaw V b) s coupling ε) f)
      (𝓝[≥] 0) (𝓝 (LawVariance (GibbsLaw (N := N) (ReferenceLaw V b) s coupling 0) f)) ∧
    Tendsto (fun ε : ℝ => PhysicalEnergy (GibbsLaw (N := N) (ReferenceLaw V b) s coupling ε) f)
      (𝓝[≥] 0) (𝓝 (PhysicalEnergy (GibbsLaw (N := N) (ReferenceLaw V b) s coupling 0) f)) := by
-- BODY
  obtain ⟨_, _, hprob⟩ := ConvexReferenceNormalization V b κ L hκ hV hb
  let := hprob
  have hAC : ReferenceLaw V b ≪ (volume : Measure (OneParticle d)) := withDensity_absolutelyContinuous _ _
  obtain ⟨C, hC⟩ := hfc.exists_bound_of_continuous hfs.continuous
  have hCn : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
  have hfC : ∀ X, |f X| ≤ C := fun X => by simpa only [Real.norm_eq_abs] using hC X
  constructor
  · have hv (ε : ℝ) (hε : 0 ≤ ε) : LawVariance (GibbsLaw (N := N) (ReferenceLaw V b) s coupling ε) f =
        (∫ X, (f X)^2 ∂GibbsLaw (N := N) (ReferenceLaw V b) s coupling ε) -
          (∫ X, f X ∂GibbsLaw (N := N) (ReferenceLaw V b) s coupling ε)^2 := by
      have hp : IsProbabilityMeasure (GibbsLaw (N := N) (ReferenceLaw V b) s coupling ε) := by
        by_cases he : ε = 0
        · subst ε
          exact (SingularGibbsNormalization hd (ReferenceLaw V b) hAC s coupling hs hc).2.2
        · exact (SoftGibbsNormalization (ReferenceLaw V b) s coupling ε hs hc
            (lt_of_le_of_ne hε (Ne.symm he))).2.2
      let := hp
      apply ProbabilityTheory.variance_eq_sub
      exact MemLp.of_bound hfs.continuous.aestronglyMeasurable C
        (Eventually.of_forall (fun X => by simpa only [Real.norm_eq_abs] using hfC X))
    have ht1 := (GibbsObservableCutoffLimit hd (ReferenceLaw V b) hAC s coupling hs hc
      f hfs.continuous.measurable C hCn hfC).2
    have hf2C (X : ParticleConfig d N) : |(f X)^2| ≤ C^2 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hfC X) 2
    have ht2 := (GibbsObservableCutoffLimit hd (ReferenceLaw V b) hAC s coupling hs hc
      (fun X => (f X)^2) (hfs.continuous.measurable.pow_const 2) (C^2) (sq_nonneg _) hf2C).2
    have heq : (fun ε => LawVariance (GibbsLaw (N := N) (ReferenceLaw V b) s coupling ε) f) =ᶠ[𝓝[≥] 0]
        (fun ε => (∫ X, (f X)^2 ∂GibbsLaw (N := N) (ReferenceLaw V b) s coupling ε) -
          (∫ X, f X ∂GibbsLaw (N := N) (ReferenceLaw V b) s coupling ε)^2) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hv ε hε
    rw [hv 0 le_rfl]
    exact (ht2.sub (ht1.pow 2)).congr' heq.symm
  · have hg := CompactGradientCalculus f hfs hfc
    obtain ⟨D, hD⟩ := hg.2.1.exists_bound_of_continuous hg.1
    exact (GibbsObservableCutoffLimit hd (ReferenceLaw V b) hAC s coupling hs hc
      (fun X => ‖EuclideanGradient f X‖^2) (hg.1.norm.pow 2).measurable (D^2) (sq_nonneg _)
      (fun X => by
        rw [abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hD X) 2)).2
