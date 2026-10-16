module

public import Tablet.FixedNGibbsBoundedBackgroundPI
public import Tablet.NativeLargeNPhysicalPI
public import Tablet.PhysicalEnergy
public import Tablet.LawVariance
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped ContDiff ENNReal NNReal
noncomputable section
-- [TABLET NODE: NativeAllNRegularizedPI]
theorem NativeAllNRegularizedPI (d : ℕ) (hd : 3 ≤ d) (s B κ L : ℝ)
    (hs : 0 < s) (hsd : s ≤ (d:ℝ)-2) (hB : 0 ≤ B) (hκ : 0 < κ) (hL : 1 ≤ L)
    (Ca Mloc : ℝ → ℝ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ V : OneParticle d → ℝ, PotentialBounds d κ V →
      (∀ x, V 0 ≤ V x) →
      (∀ R : ℝ, 0 < R → ∀ x, ‖x‖ ≤ R → V x-V 0 ≤ Mloc R) →
      (∀ a : ℝ, 0 < a → ∀ x, EuclideanLaplacian V x ≤
        a*‖EuclideanGradient V x‖^(2/(s+1))+Ca a) →
      ∀ b : OneParticle d → ℝ, BoundedMultiplier d L b →
      ∀ N : ℕ, 2 ≤ N → ∀ coupling ε : ℝ, 0 ≤ coupling → coupling ≤ B → 0 < ε →
      let P := GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε
      ∀ f : ParticleConfig d N → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
        IsProbabilityMeasure P ∧ ρ*LawVariance P f ≤ PhysicalEnergy P f := by
-- BODY
  classical
  obtain ⟨rLarge,hrLarge,N_B,hNB,hLarge⟩ := NativeLargeNPhysicalPI
    d hd s B κ L hs hsd hB hκ hL Ca Mloc
  -- Only a finite scalar minimum is used; no model/gap/PI premise is introduced.
  have finite_positive_common_lower_bound (S : Finset ℕ) (r : ℕ → ℝ)
      (hpos : ∀ N ∈ S, 0 < r N) :
      ∃ c : ℝ, 0 < c ∧ ∀ N ∈ S, c ≤ r N := by
    induction S using Finset.induction_on with
    | empty => exact ⟨1,zero_lt_one,by simp⟩
    | @insert n S hn ih =>
      obtain ⟨c,hc,hcle⟩ := ih (fun N hN => hpos N (Finset.mem_insert_of_mem hN))
      refine ⟨min (r n) c,lt_min (hpos n (Finset.mem_insert_self n S)) hc,?_⟩
      intro N hN
      rcases Finset.mem_insert.mp hN with rfl | hN
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hcle N hN)
  have hsmall : ∀ N : ℕ, ∃ r : ℝ, 0 < r ∧
      (2 ≤ N → N < N_B → ∀ V : OneParticle d → ℝ, PotentialBounds d κ V →
        (∀ x, V 0 ≤ V x) →
        (∀ R : ℝ, 0 < R → ∀ x, ‖x‖ ≤ R → V x-V 0 ≤ Mloc R) →
        (∀ a : ℝ, 0 < a → ∀ x, EuclideanLaplacian V x ≤
          a*‖EuclideanGradient V x‖^(2/(s+1))+Ca a) →
        ∀ b : OneParticle d → ℝ, BoundedMultiplier d L b →
        ∀ coupling ε : ℝ, 0 ≤ coupling → coupling ≤ B → 0 < ε →
        ∀ f : ParticleConfig d N → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
          r*LawVariance (GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε) f ≤
            PhysicalEnergy (GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε) f) := by
    intro N
    by_cases hN : 2 ≤ N ∧ N < N_B
    · obtain ⟨rate,σ,hrate,hσ,hσeq,hFixed⟩ := FixedNGibbsBoundedBackgroundPI
        N d hN.1 hd s B κ L hs hsd hB hκ hL Ca Mloc
      refine ⟨σ,hσ,?_⟩
      intro _ _ V hV hmin hlocal hgrowth b hb coupling ε hc hcB hε f hf hfc
      have htrace : ∀ a, 0 < a → ∀ x, EuclideanLaplacian V x ≤
          a*‖EuclideanGradient V x‖^(ForceExponent s)+Ca a := by
        simpa only [ForceExponent] using hgrowth
      have hfc0 : HasCompactSupport (fun X => f X-0) := by
        simpa only [sub_zero] using hfc
      have h := hFixed V hV hmin hlocal htrace b hb coupling ε hc hcB hε
        f (hf.of_le (by simp)) 0 hfc0
      exact h.2.2
    · exact ⟨1,zero_lt_one,fun hN2 hNT => False.elim (hN ⟨hN2,hNT⟩)⟩
  choose r hr using hsmall
  obtain ⟨rSmall,hrSmall,hSmallLe⟩ := finite_positive_common_lower_bound
    (Finset.range N_B) r (fun N _ => (hr N).1)
  let ρ := min rSmall rLarge
  have hρ : 0 < ρ := lt_min hrSmall hrLarge
  refine ⟨ρ,hρ,?_⟩
  intro V hV hmin hlocal hgrowth b hb N hN coupling ε hc hcB hε
  dsimp only
  let μ := ReferenceLaw V b
  let P := GibbsLaw (N:=N) μ s coupling ε
  letI : IsProbabilityMeasure μ := (ConvexReferenceNormalization V b κ L hκ hV hb).2.2
  have hprob : IsProbabilityMeasure P := (SoftGibbsNormalization μ s coupling ε hs hc hε).2.2
  intro f hf hfc
  refine ⟨hprob,?_⟩
  have hvar : 0 ≤ LawVariance P f := ProbabilityTheory.variance_nonneg f P
  by_cases hSmallN : N < N_B
  · have hrate : ρ ≤ r N :=
      (min_le_left _ _).trans (hSmallLe N (Finset.mem_range.mpr hSmallN))
    exact (mul_le_mul_of_nonneg_right hrate hvar).trans
      ((hr N).2 hN hSmallN V hV hmin hlocal hgrowth b hb coupling ε hc hcB hε f hf hfc)
  · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) hvar).trans
      (hLarge V hV hmin hlocal hgrowth b hb N (Nat.le_of_not_gt hSmallN) coupling ε hc hcB hε f hf hfc)
