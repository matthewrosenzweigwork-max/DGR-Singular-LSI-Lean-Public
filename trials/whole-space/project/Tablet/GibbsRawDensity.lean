import Tablet.GibbsLebesgueDensity
import Tablet.ProductReferenceDensity
import Tablet.ConvexReferenceNormalization
import Tablet.SingularGibbsNormalization
import Tablet.SoftGibbsNormalization
open MeasureTheory Filter
open scoped BigOperators

-- [TABLET NODE: GibbsRawDensity]
theorem GibbsRawDensity {d N : ℕ} (hd : 0 < d) (V b : OneParticle d → ℝ)
    (κ L : ℝ) (hκ : 0 < κ) (hV : PotentialBounds d κ V)
    (hb : BoundedMultiplier d L b) (s coupling ε : ℝ)
    (hs : 0 < s) (hc : 0 ≤ coupling) (hε : 0 ≤ ε) :
    GibbsLaw (N := N) (ReferenceLaw V b) s coupling ε =
      (volume : Measure (ParticleConfig d N)).withDensity
        (fun X => ENNReal.ofReal (GibbsLebesgueDensity V b s coupling ε X)) := by
-- BODY
  classical
  obtain ⟨hi, hZ, hprob⟩ := ConvexReferenceNormalization V b κ L hκ hV hb
  let := hprob
  obtain ⟨m, M, hm, _, _, hbounds⟩ := hb.bounds
  have hn : ∀ x, 0 ≤ b x := fun x => hm.le.trans (hbounds x).1
  have hZG : 0 < GibbsPartition (N := N) (ReferenceLaw V b) s coupling ε := by
    by_cases he : ε = 0
    · subst ε
      exact (SingularGibbsNormalization hd (ReferenceLaw V b)
        (withDensity_absolutelyContinuous _ _) s coupling hs hc).2.1.1
    · exact (SoftGibbsNormalization (ReferenceLaw V b) s coupling ε hs hc
        (lt_of_le_of_ne hε (Ne.symm he))).2.1.1
  let q := fun x : OneParticle d => (ReferencePartition V b)⁻¹ * (b x * Real.exp (-V x))
  have hq : Measurable q := (hb.measurable.mul hV.regularity.continuous.measurable.neg.exp).const_mul _
  have hqn : ∀ x, 0 ≤ q x := fun x => mul_nonneg (inv_nonneg.mpr hZ.le)
    (mul_nonneg (hn x) (Real.exp_pos _).le)
  have hqi : Integrable q volume := hi.const_mul _
  have hqm : ∫ x, q x = 1 := by
    rw [integral_const_mul]
    change (ReferencePartition V b)⁻¹ * ReferencePartition V b = 1
    simp [ne_of_gt hZ]
  have hQ : ConfigurationReference d N (ReferenceLaw V b) =
      (volume : Measure (ParticleConfig d N)).withDensity
        (fun X => ENNReal.ofReal (∏ i : Fin N, q (ParticlePosition X i))) :=
    ProductReferenceDensity d N q hq hqn hqi hqm
  have hr : Measurable (fun X : ParticleConfig d N => ENNReal.ofReal (∏ i : Fin N, q (ParticlePosition X i))) := by
    apply Measurable.ennreal_ofReal
    apply Finset.measurable_prod
    intro i _
    have hp : Continuous (fun X : ParticleConfig d N => ParticlePosition X i) := by
      unfold ParticlePosition
      fun_prop
    exact hq.comp hp.measurable
  have hw : Measurable (fun X : ParticleConfig d N => ENNReal.ofReal
      ((GibbsPartition (N := N) (ReferenceLaw V b) s coupling ε)⁻¹ * InteractionWeight s coupling ε X)) :=
    ((InteractionWeightMeasurable s coupling ε).const_mul _).ennreal_ofReal
  unfold GibbsLaw
  rw [hQ, ← withDensity_mul volume hr hw]
  apply withDensity_congr_ae
  filter_upwards [] with X
  have hrn : 0 ≤ ∏ i : Fin N, q (ParticlePosition X i) :=
    Finset.prod_nonneg (fun i _ => hqn _)
  change ENNReal.ofReal (∏ i : Fin N, q (ParticlePosition X i)) * ENNReal.ofReal
    ((GibbsPartition (N := N) (ReferenceLaw V b) s coupling ε)⁻¹ *
      InteractionWeight s coupling ε X) = _
  rw [← ENNReal.ofReal_mul hrn]
  congr 1
  change (∏ i : Fin N, (ReferencePartition V b)⁻¹ *
    (b (ParticlePosition X i) * Real.exp (-V (ParticlePosition X i)))) *
    ((GibbsPartition (N := N) (ReferenceLaw V b) s coupling ε)⁻¹ * InteractionWeight s coupling ε X) = _
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Finset.prod_mul_distrib, ← Real.exp_sum, Finset.sum_neg_distrib, inv_pow]
  simp only [Fintype.card_fin]
  unfold GibbsLebesgueDensity
  rw [mul_inv_rev]
  ring
