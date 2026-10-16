import Tablet.SinglePairGraphApproximation
import Tablet.WeightedPairCapacity
import Tablet.GibbsLocalDensityBounds
import Tablet.CollisionFreeGradientCore
import Tablet.ClosedGradientGraph
import Tablet.CollisionNull
open MeasureTheory Filter Set
open scoped BigOperators Topology ContDiff
namespace GibbsClosedCoreEquality
private abbrev CollisionPair (N : ℕ) := {p : Fin N × Fin N // p.1 < p.2}

private def pairSupportExcluded {d N : ℕ} (S : Finset (CollisionPair N)) (f : ParticleConfig d N → ℝ) : Prop :=
  ∀ p ∈ S, ∀ x ∈ tsupport f, ParticlePosition x p.val.1 ≠ ParticlePosition x p.val.2

private def pairExcludedCore {d N : ℕ} (P : Measure (ParticleConfig d N)) (S : Finset (CollisionPair N)) :
    Set (Lp ℝ 2 P × Lp (ParticleConfig d N) 2 P) :=
  {q | ∃ f : ParticleConfig d N → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ pairSupportExcluded S f ∧
    ∃ hf : MemLp f 2 P, ∃ hD : MemLp (EuclideanGradient f) 2 P,
      q = (hf.toLp f,hD.toLp (EuclideanGradient f))}

private lemma pairExcludedCore_empty {d N : ℕ} (P : Measure (ParticleConfig d N)) :
    pairExcludedCore P ∅ = SmoothGradientCore P := by
  ext q
  simp [pairExcludedCore,pairSupportExcluded,SmoothGradientCore]

private lemma pairSupportExcluded_univ {d N : ℕ} (f : ParticleConfig d N → ℝ) :
    pairSupportExcluded Finset.univ f ↔ Disjoint (tsupport f) (CollisionSet d N) := by
  rw [Set.disjoint_left]
  constructor
  · intro h x hx hc
    obtain ⟨i,j,hij,he⟩ := hc
    have hn := h ⟨(i,j),hij⟩ (Finset.mem_univ _) x hx
    exact hn he
  · intro h p hp x hx he
    apply h hx
    exact ⟨p.val.1,p.val.2,p.property,he⟩

private lemma pairExcludedCore_univ {d N : ℕ} (P : Measure (ParticleConfig d N)) :
    pairExcludedCore P Finset.univ = CollisionFreeGradientCore P := by
  ext q
  simp only [pairExcludedCore,CollisionFreeGradientCore,Set.mem_ofPred_eq,pairSupportExcluded_univ]


private lemma pairExcludedCore_subset {d N : ℕ} (P : Measure (ParticleConfig d N)) (S : Finset (CollisionPair N)) :
    pairExcludedCore P S ⊆ SmoothGradientCore P := by
  rintro q ⟨f,hs,hc,hx,hf,hD,rfl⟩
  exact ⟨f,hs,hc,hf,hD,rfl⟩


private lemma removeFinitePairs {d N : ℕ} (P : Measure (ParticleConfig d N))
    (hpair : ∀ (i j : Fin N), i ≠ j → ∀ᵐ X ∂P, ParticlePosition X i ≠ ParticlePosition X j)
    (hinv : ∀ f : ParticleConfig d N → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      ∀ (i j : Fin N), i ≠ j →
        Integrable (fun X => (f X)^2 / ‖ParticlePosition X i - ParticlePosition X j‖^2) P)
    (T S : Finset (CollisionPair N)) (f : ParticleConfig d N → ℝ)
    (hs : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hf : MemLp f 2 P) (hg : MemLp (EuclideanGradient f) 2 P)
    (hex : pairSupportExcluded S f) :
    (hf.toLp f, hg.toLp (EuclideanGradient f)) ∈ closure (pairExcludedCore P (S ∪ T)) := by
  classical
  induction T using Finset.induction_on generalizing S f with
  | empty =>
      simp only [Finset.union_empty]
      exact subset_closure ⟨f, hs, hc, hex, hf, hg, rfl⟩
  | @insert p T hp ih =>
      let i := p.val.1
      let j := p.val.2
      have hij : i ≠ j := ne_of_lt p.property
      obtain ⟨fn, hprops, hfn, hgn, ht⟩ :=
        SinglePairGraphApproximation P i j hij (hpair i j hij) f hs hc hf hg
          (hinv f hs hc i j hij)
      have hmem : ∀ n, ((hfn n).toLp (fn n), (hgn n).toLp (EuclideanGradient (fn n))) ∈
          closure (pairExcludedCore P (S ∪ insert p T)) := by
        intro n
        have he : pairSupportExcluded (insert p S) (fn n) := by
          intro q hq X hX
          rcases Finset.mem_insert.mp hq with hqp | hqS
          · subst q
            exact (hprops n).2.2.2 X hX
          · exact hex q hqS X ((hprops n).2.2.1 hX)
        have hh := ih (insert p S) (fn n) (hprops n).1 (hprops n).2.1 (hfn n) (hgn n) he
        have hset : insert p S ∪ T = S ∪ insert p T := by
          ext q
          simp only [Finset.mem_union, Finset.mem_insert]
          tauto
        simpa only [hset] using hh
      exact isClosed_closure.mem_of_tendsto ht (Eventually.of_forall hmem)
end GibbsClosedCoreEquality

-- [TABLET NODE: GibbsClosedCoreEquality]
theorem GibbsClosedCoreEquality {d N : ℕ} (hd : 3 ≤ d) (V b : OneParticle d → ℝ)
    (κ L : ℝ) (hκ : 0 < κ) (hV : PotentialBounds d κ V)
    (hb : BoundedMultiplier d L b) (s coupling ε : ℝ)
    (hs : 0 < s) (hc : 0 ≤ coupling) (hε : 0 ≤ ε) :
    closure (CollisionFreeGradientCore
      (GibbsLaw (N := N) (ReferenceLaw V b) s coupling ε)) =
      ClosedGradientGraph (GibbsLaw (N := N) (ReferenceLaw V b) s coupling ε) := by
-- BODY
  classical
  let P := GibbsLaw (N := N) (ReferenceLaw V b) s coupling ε
  let r := GibbsLebesgueDensity (N := N) V b s coupling ε
  have hraw : P = volume.withDensity (fun X => ENNReal.ofReal (r X)) :=
    GibbsRawDensity (by omega) V b κ L hκ hV hb s coupling ε hs hc hε
  obtain ⟨hi, hZ, hprob⟩ := ConvexReferenceNormalization V b κ L hκ hV hb
  let := hprob
  have hZG : 0 < GibbsPartition (N := N) (ReferenceLaw V b) s coupling ε := by
    by_cases he : ε = 0
    · subst ε
      exact (SingularGibbsNormalization (by omega) (ReferenceLaw V b)
        (withDensity_absolutelyContinuous _ _) s coupling hs hc).2.1.1
    · exact (SoftGibbsNormalization (ReferenceLaw V b) s coupling ε hs hc
        (lt_of_le_of_ne hε (Ne.symm he))).2.1.1
  obtain ⟨blo, bhi, hlo, _, _, hbb⟩ := hb.bounds
  have hbn : ∀ x, 0 ≤ b x := fun x => hlo.le.trans (hbb x).1
  have hr : Measurable r := by
    unfold r GibbsLebesgueDensity
    apply Measurable.mul
    · apply Measurable.mul
      · apply Measurable.const_mul
        apply Finset.measurable_prod
        intro i _
        have hp : Continuous (fun X : ParticleConfig d N => ParticlePosition X i) := by
          unfold ParticlePosition
          fun_prop
        exact hb.measurable.comp hp.measurable
      · have he : Continuous (fun X : ParticleConfig d N =>
            Real.exp (-(∑ i : Fin N, V (ParticlePosition X i)))) := by
          have hv := hV.regularity.continuous
          unfold ParticlePosition
          fun_prop
        exact he.measurable
    · exact InteractionWeightMeasurable s coupling ε
  have hrn : ∀ X, 0 ≤ r X := by
    intro X
    unfold r GibbsLebesgueDensity
    exact mul_nonneg (mul_nonneg
      (mul_nonneg (inv_nonneg.mpr (mul_nonneg (pow_nonneg hZ.le N) hZG.le))
        (Finset.prod_nonneg (fun i _ => hbn _))) (Real.exp_pos _).le)
      ((InteractionWeightBounds s coupling ε hs hc hε).1 X).1
  have hfree : ∀ᵐ X ∂P, X ∉ CollisionSet d N := by
    have ha : P ≪ (volume : Measure (ParticleConfig d N)) := by
      rw [hraw]
      exact withDensity_absolutelyContinuous _ _
    rw [ae_iff]
    apply ha
    simpa only [not_not, Set.ofPred_mem_eq] using CollisionNull d N (by omega)
  have hpair : ∀ (i j : Fin N), i ≠ j →
      ∀ᵐ X ∂P, ParticlePosition X i ≠ ParticlePosition X j := by
    intro i j hij
    filter_upwards [hfree] with X hX
    intro he
    apply hX
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact ⟨i, j, hlt, he⟩
    · exact ⟨j, i, hgt, he.symm⟩
  have hinv : ∀ f : ParticleConfig d N → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      ∀ (i j : Fin N), i ≠ j →
        Integrable (fun X => (f X)^2 / ‖ParticlePosition X i - ParticlePosition X j‖^2) P := by
    intro f hfs hfc i j hij
    obtain ⟨M, hM, hbound⟩ := (GibbsLocalDensityBounds (by omega) V b κ L hκ hV hb
      s coupling ε hs hc hε).1 (tsupport f) hfc
    rw [hraw]
    exact (WeightedPairCapacity hd i j hij f (hfs.of_le (by norm_num)) hfc r hr hrn
      M hM.le hbound).1
  apply le_antisymm
  · apply closure_mono
    rintro q ⟨f, hfs, hfc, hdis, hf, hg, rfl⟩
    exact ⟨f, hfs, hfc, hf, hg, rfl⟩
  · apply closure_minimal _ isClosed_closure
    rintro q ⟨f, hfs, hfc, hf, hg, rfl⟩
    have hh := GibbsClosedCoreEquality.removeFinitePairs P hpair hinv Finset.univ ∅
      f hfs hfc hf hg (by simp [GibbsClosedCoreEquality.pairSupportExcluded])
    simpa only [Finset.empty_union, GibbsClosedCoreEquality.pairExcludedCore_univ] using hh
