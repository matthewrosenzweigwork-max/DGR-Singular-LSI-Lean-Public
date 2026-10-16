module

public import Tablet.GibbsRawDensity
public import Tablet.InteractionWeightOffCollision
public import Mathlib.Topology.Order.Compact

@[expose] public section
open MeasureTheory Set
open scoped BigOperators

-- [TABLET NODE: GibbsLocalDensityBounds]
theorem GibbsLocalDensityBounds {d N : ℕ} (hd : 0 < d) (V b : OneParticle d → ℝ)
    (κ L : ℝ) (hκ : 0 < κ) (hV : PotentialBounds d κ V)
    (hb : BoundedMultiplier d L b) (s coupling ε : ℝ)
    (hs : 0 < s) (hc : 0 ≤ coupling) (hε : 0 ≤ ε) :
    (∀ K : Set (ParticleConfig d N), IsCompact K →
      ∃ M : ℝ, 0 < M ∧ ∀ X ∈ K, GibbsLebesgueDensity V b s coupling ε X ≤ M) ∧
    (∀ K : Set (ParticleConfig d N), IsCompact K → K ⊆ (CollisionSet d N)ᶜ →
      ∃ m : ℝ, 0 < m ∧ ∀ X ∈ K, m ≤ GibbsLebesgueDensity V b s coupling ε X) := by
-- BODY
  classical
  obtain ⟨_, hZ, hprob⟩ := ConvexReferenceNormalization V b κ L hκ hV hb
  let := hprob
  have hZG : 0 < GibbsPartition (N := N) (ReferenceLaw V b) s coupling ε := by
    by_cases he : ε = 0
    · subst ε
      exact (SingularGibbsNormalization hd (ReferenceLaw V b)
        (withDensity_absolutelyContinuous _ _) s coupling hs hc).2.1.1
    · exact (SoftGibbsNormalization (ReferenceLaw V b) s coupling ε hs hc
        (lt_of_le_of_ne hε (Ne.symm he))).2.1.1
  let Z := (ReferencePartition V b)^N * GibbsPartition (N := N) (ReferenceLaw V b) s coupling ε
  have hZtotal : 0 < Z := mul_pos (pow_pos hZ N) hZG
  obtain ⟨blo, bhi, hlo, horder, _, hbounds⟩ := hb.bounds
  have hhi : 0 < bhi := hlo.trans_le horder
  let B := fun X : ParticleConfig d N => ∏ i : Fin N, b (ParticlePosition X i)
  let e := fun X : ParticleConfig d N => Real.exp (-(∑ i : Fin N, V (ParticlePosition X i)))
  let c := fun X : ParticleConfig d N => e X * InteractionWeight s coupling ε X
  have hBc (X : ParticleConfig d N) : blo^N ≤ B X ∧ B X ≤ bhi^N := by
    constructor
    · calc
        _ = ∏ _ : Fin N, blo := by simp
        _ ≤ B X := Finset.prod_le_prod₀ (fun _ _ => hlo.le) (fun i _ => (hbounds _).1)
    · calc
        B X ≤ ∏ _ : Fin N, bhi := Finset.prod_le_prod₀
          (fun i _ => hlo.le.trans (hbounds _).1) (fun i _ => (hbounds _).2)
        _ = _ := by simp
  have he : Continuous e := by
    apply Real.continuous_exp.comp
    apply Continuous.neg
    apply continuous_finsetSum
    intro i _
    have hp : Continuous (fun X : ParticleConfig d N => ParticlePosition X i) := by
      unfold ParticlePosition
      fun_prop
    exact hV.regularity.continuous.comp hp
  have hcp : ∀ X ∈ (CollisionSet d N)ᶜ, 0 < c X := fun X hX =>
    mul_pos (Real.exp_pos _) ((InteractionWeightOffCollision s coupling ε).2 X hX)
  have hcc : ContinuousOn c (CollisionSet d N)ᶜ :=
    he.continuousOn.mul (InteractionWeightOffCollision s coupling ε).1
  have hdensity (X : ParticleConfig d N) :
      GibbsLebesgueDensity V b s coupling ε X = B X * c X / Z := by
    dsimp [GibbsLebesgueDensity, B, c, e, Z]
    ring
  constructor
  · intro K hK
    by_cases hne : K.Nonempty
    · obtain ⟨xmax, hxmax, hmax⟩ := hK.exists_isMaxOn hne he.continuousOn
      have hep : 0 < e xmax := Real.exp_pos _
      refine ⟨bhi^N * e xmax / Z, div_pos (mul_pos (pow_pos hhi N) hep) hZtotal, ?_⟩
      intro X hX
      rw [hdensity]
      have hw := (InteractionWeightBounds s coupling ε hs hc hε).1 X
      have hcn : 0 ≤ c X := mul_nonneg (Real.exp_pos _).le hw.1
      have hcu : c X ≤ e xmax := by
        calc
          c X ≤ e X := by dsimp [c]; exact mul_le_of_le_one_right (Real.exp_pos _).le hw.2
          _ ≤ e xmax := hmax hX
      exact div_le_div_of_nonneg_right
        (mul_le_mul (hBc X).2 hcu hcn (pow_nonneg hhi.le N)) hZtotal.le
    · refine ⟨1, by norm_num, ?_⟩
      intro X hX
      exact False.elim (hne ⟨X, hX⟩)
  · intro K hK hKU
    by_cases hne : K.Nonempty
    · obtain ⟨xmin, hxmin, hmin⟩ := hK.exists_isMinOn hne (hcc.mono hKU)
      have hpmin : 0 < c xmin := hcp xmin (hKU hxmin)
      refine ⟨blo^N * c xmin / Z, div_pos (mul_pos (pow_pos hlo N) hpmin) hZtotal, ?_⟩
      intro X hX
      rw [hdensity]
      exact div_le_div_of_nonneg_right
        (mul_le_mul (hBc X).1 (hmin hX) hpmin.le ((pow_pos hlo N).le.trans (hBc X).1)) hZtotal.le
    · refine ⟨1, by norm_num, ?_⟩
      intro X hX
      exact False.elim (hne ⟨X, hX⟩)
