import Tablet.SpatialCutoffApproximation
import Tablet.ClosedGradientGraph
import Tablet.ConvexReferenceNormalization
import Tablet.SingularGibbsNormalization
import Tablet.SoftGibbsNormalization
open MeasureTheory Filter Set
open scoped Topology ContDiff

-- [TABLET NODE: GibbsClosedConstants]
theorem GibbsClosedConstants {d N : ℕ} (hd : 0 < d) (V b : OneParticle d → ℝ)
    (κ L : ℝ) (hκ : 0 < κ) (hV : PotentialBounds d κ V)
    (hb : BoundedMultiplier d L b) (s coupling ε : ℝ)
    (hs : 0 < s) (hc : 0 ≤ coupling) (hε : 0 ≤ ε) :
    ∃ hf : MemLp (fun _ : ParticleConfig d N => (1 : ℝ)) 2
        (GibbsLaw (N := N) (ReferenceLaw V b) s coupling ε),
      (hf.toLp (fun _ => (1 : ℝ)),
        (0 : Lp (ParticleConfig d N) 2 (GibbsLaw (N := N) (ReferenceLaw V b) s coupling ε))) ∈
        ClosedGradientGraph (GibbsLaw (N := N) (ReferenceLaw V b) s coupling ε) := by
-- BODY
  obtain ⟨_, _, hprob⟩ := ConvexReferenceNormalization V b κ L hκ hV hb
  let := hprob
  let P := GibbsLaw (N := N) (ReferenceLaw V b) s coupling ε
  have hP : IsProbabilityMeasure P := by
    by_cases he : ε = 0
    · subst ε
      exact (SingularGibbsNormalization hd (ReferenceLaw V b)
        (withDensity_absolutelyContinuous _ _) s coupling hs hc).2.2
    · exact (SoftGibbsNormalization (ReferenceLaw V b) s coupling ε hs hc
        (lt_of_le_of_ne hε (Ne.symm he))).2.2
  let := hP
  obtain ⟨χ, C, hC, hsmooth, hunit, hlimit, hbound⟩ :=
    SpatialCutoffApproximation (ι := Fin N × Fin d)
  have hmem (n : ℕ) : MemLp (χ n) 2 P ∧ MemLp (EuclideanGradient (χ n)) 2 P := by
    constructor
    · apply MemLp.of_bound (hsmooth n).1.continuous.aestronglyMeasurable 1
      exact Eventually.of_forall (fun X => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hunit n X).1]
        exact (hunit n X).2)
    · exact MemLp.of_bound
        (CompactGradientCalculus (χ n) (hsmooth n).1 (hsmooth n).2).1.aestronglyMeasurable
        (C / ((n : ℝ) + 1)) (Eventually.of_forall (hbound n))
  let one : Lp ℝ 2 P := (memLp_const (1 : ℝ)).toLp (fun _ => 1)
  let hf := fun n => (hmem n).1
  let hD := fun n => (hmem n).2
  let F := fun n => (hf n).toLp (χ n)
  let D := fun n => (hD n).toLp (EuclideanGradient (χ n))
  have hrepr (n : ℕ) : ((F n - one : Lp ℝ 2 P) : ParticleConfig d N → ℝ) =ᵐ[P]
      (fun X => χ n X - 1) := by
    filter_upwards [Lp.coeFn_sub (F n) one, (hf n).coeFn_toLp,
      (memLp_const (1 : ℝ) (μ := P)).coeFn_toLp] with X hx hF hone
    rw [hx]
    change F n X - one X = χ n X - 1
    rw [hF, hone]
  have henergy (n : ℕ) : (∫ X, (χ n X - 1)^2 ∂P) = ‖F n - one‖^2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hrepr n] with X hx
    rw [real_inner_self_eq_norm_sq, hx]
    simp only [Real.norm_eq_abs, sq_abs]
  have hmeanSquare : Tendsto (fun n : ℕ => ∫ X, (χ n X - 1)^2 ∂P) atTop (𝓝 (0 : ℝ)) := by
    have hm : ∀ᶠ n : ℕ in atTop, AEStronglyMeasurable
        (fun X : ParticleConfig d N => (χ n X - 1)^2) P := Eventually.of_forall
      (fun n => (((hsmooth n).1.continuous.measurable.sub_const 1).pow_const 2).aestronglyMeasurable)
    have hbnd : ∀ᶠ n : ℕ in atTop, ∀ᵐ X : ParticleConfig d N ∂P, ‖(χ n X - 1)^2‖ ≤ 1 :=
      Eventually.of_forall (fun n => Eventually.of_forall (fun X => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have hu := hunit n X
        have ha : |χ n X - 1| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith
        simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg _) ha 2))
    have hconv : ∀ᵐ X : ParticleConfig d N ∂P,
        Tendsto (fun n : ℕ => (χ n X - 1)^2) atTop (𝓝 (0 : ℝ)) :=
      Eventually.of_forall (fun X => by simpa using ((hlimit X).sub_const 1).pow 2)
    have ht := tendsto_integral_filter_of_dominated_convergence
      (fun _ : ParticleConfig d N => (1 : ℝ)) hm hbnd (integrable_const _) hconv
    simpa using ht
  have hfn : Tendsto F atTop (𝓝 one) := by
    have hsq : Tendsto (fun n : ℕ => ‖F n - one‖^2) atTop (𝓝 (0 : ℝ)) := by
      simpa only [henergy] using hmeanSquare
    have hnorm : Tendsto (fun n : ℕ => ‖F n - one‖) atTop (𝓝 (0 : ℝ)) := by
      simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using
        Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm
  have hdn : Tendsto D atTop (𝓝 0) := by
    have hbnd (n : ℕ) : ‖D n‖ ≤ C / ((n : ℝ) + 1) := by
      have ha : ∀ᵐ X : ParticleConfig d N ∂P, ‖D n X‖ ≤ C / ((n : ℝ) + 1) := by
        filter_upwards [(hD n).coeFn_toLp] with X hx
        rw [hx]
        exact hbound n X
      have hl := Lp.norm_le_of_ae_bound (by positivity : 0 ≤ C / ((n : ℝ) + 1)) ha
      simpa [measureUnivNNReal] using hl
    have hi : Tendsto (fun n : ℕ => C / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) := by
      simpa only [div_eq_mul_inv, mul_zero, one_div, one_mul] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0)).const_mul C
    exact tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero (fun n => norm_nonneg (D n)) hbnd hi)
  refine ⟨memLp_const (1 : ℝ), ?_⟩
  apply mem_closure_iff_seq_limit.mpr
  refine ⟨fun n => (F n, D n), ?_, hfn.prodMk_nhds hdn⟩
  intro n
  exact ⟨χ n, (hsmooth n).1, (hsmooth n).2, hf n, hD n, rfl⟩
