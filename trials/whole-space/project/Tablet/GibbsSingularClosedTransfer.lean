import Tablet.GibbsCompactTestCutoffLimit
import Tablet.SmoothCoreClosedPI
open MeasureTheory Filter
open scoped Topology ContDiff

-- [TABLET NODE: GibbsSingularClosedTransfer]
theorem GibbsSingularClosedTransfer {d N : ℕ} (hd : 0 < d) (V b : OneParticle d → ℝ)
    (κ L : ℝ) (hκ : 0 < κ) (hV : PotentialBounds d κ V)
    (hb : BoundedMultiplier d L b) (s coupling A : ℝ) (hs : 0 < s) (hc : 0 ≤ coupling)
    (hreg : ∀ (ε : ℝ), 0 < ε → ∀ (g : ParticleConfig d N → ℝ),
      ContDiff ℝ ∞ g → HasCompactSupport g →
        LawVariance (GibbsLaw (N := N) (ReferenceLaw V b) s coupling ε) g ≤
          A * PhysicalEnergy (GibbsLaw (N := N) (ReferenceLaw V b) s coupling ε) g)
    (f : Lp ℝ 2 (GibbsLaw (N := N) (ReferenceLaw V b) s coupling 0))
    (v : Lp (ParticleConfig d N) 2 (GibbsLaw (N := N) (ReferenceLaw V b) s coupling 0))
    (hfv : (f, v) ∈ ClosedGradientGraph (GibbsLaw (N := N) (ReferenceLaw V b) s coupling 0)) :
    LawVariance (GibbsLaw (N := N) (ReferenceLaw V b) s coupling 0)
      (f : ParticleConfig d N → ℝ) ≤ A * ClosedPhysicalEnergy (f, v) := by
-- BODY
  obtain ⟨_, _, hprob⟩ := ConvexReferenceNormalization V b κ L hκ hV hb
  let := hprob
  let := (SingularGibbsNormalization (N := N) hd (ReferenceLaw V b)
    (withDensity_absolutelyContinuous _ _) s coupling hs hc).2.2
  apply SmoothCoreClosedPI _ A _ f v hfv
  intro g hgs hgc _ _
  have heps : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝[≥] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall (fun n => by
      change 0 ≤ (1 : ℝ) / ((n : ℝ) + 1)
      positivity)⟩
  have hlimit := GibbsCompactTestCutoffLimit hd V b κ L hκ hV hb s coupling hs hc g hgs hgc
  have hv := hlimit.1.comp heps
  have hE := hlimit.2.comp heps
  exact le_of_tendsto_of_tendsto hv (hE.const_mul A)
    (Eventually.of_forall (fun n => hreg (1 / ((n : ℝ) + 1)) (by positivity) g hgs hgc))
