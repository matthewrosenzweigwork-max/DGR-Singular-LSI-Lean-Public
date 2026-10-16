module

public import Tablet.PairInteractionCalculus
public import Tablet.WeightedPairCapacity
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open MeasureTheory
open scoped ContDiff

-- [TABLET NODE: PairInteractionForceForm]
theorem PairInteractionForceForm (d N : ℕ) (hd : 3 ≤ d) (s B : ℝ)
    (hs : 0 < s) (hB : 0 ≤ B) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ coupling ε : ℝ,
      0 ≤ coupling → coupling ≤ B → 0 < ε →
      ∀ ψ : ParticleConfig d N → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        Integrable (fun X => ‖EuclideanGradient (PairInteraction s coupling ε) X‖ ^
          (ForceExponent s) * (ψ X) ^ 2) volume ∧
        (∫ X, ‖EuclideanGradient (PairInteraction s coupling ε) X‖ ^
          (ForceExponent s) * (ψ X) ^ 2) ≤
          H * ∫ X, ‖EuclideanGradient ψ X‖ ^ 2 := by
-- BODY
  classical
  obtain ⟨K, hK, hcalc⟩ := PairInteractionCalculus d N s B hs hB
  let c := 2 / ((d : ℝ) - 2) ^ 2
  let H := K * (N : ℝ) ^ 2 * c
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  refine ⟨H, hH, ?_⟩
  intro coupling ε ha haB hε ψ hψ hcψ
  obtain ⟨hU, hpower⟩ := hcalc coupling ε ha haB hε
  have hpair (i j : Fin N) (hij : i ≠ j) :
      Integrable (fun X => (ψ X)^2 / ‖ParticlePosition X i - ParticlePosition X j‖^2) volume ∧
      (∫ X, (ψ X)^2 / ‖ParticlePosition X i - ParticlePosition X j‖^2) ≤
        c * ∫ X, ‖EuclideanGradient ψ X‖^2 := by
    have hh := WeightedPairCapacity hd i j hij ψ hψ hcψ
      (fun _ => (1 : ℝ)) measurable_const (fun _ => zero_le_one)
      1 zero_le_one (fun _ _ => le_refl _)
    simpa [c] using hh
  let A : Fin N → Fin N → ParticleConfig d N → ℝ := fun i j X =>
    if i < j then (ψ X)^2 / ‖ParticlePosition X i - ParticlePosition X j‖^2 else 0
  have hAi (i j : Fin N) : Integrable (A i j) volume := by
    by_cases hij : i < j
    · simpa only [A, if_pos hij] using (hpair i j (ne_of_lt hij)).1
    · simp only [A, if_neg hij]
      exact (continuous_const : Continuous (fun _ : ParticleConfig d N => (0 : ℝ))).integrable_of_hasCompactSupport HasCompactSupport.zero
  have hAsum : Integrable (fun X => ∑ i : Fin N, ∑ j : Fin N, A i j X) volume := by
    exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hAi i j))
  have henergy : 0 ≤ ∫ X, ‖EuclideanGradient ψ X‖^2 := integral_nonneg (fun _ => sq_nonneg _)
  have hAbound (i j : Fin N) : (∫ X, A i j X) ≤ c * ∫ X, ‖EuclideanGradient ψ X‖^2 := by
    by_cases hij : i < j
    · simpa only [A, if_pos hij] using (hpair i j (ne_of_lt hij)).2
    · simp only [A, if_neg hij, integral_zero]
      exact mul_nonneg hc henergy
  have htotal : (∫ X, ∑ i : Fin N, ∑ j : Fin N, A i j X) ≤
      (N : ℝ)^2 * c * ∫ X, ‖EuclideanGradient ψ X‖^2 := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hAi i j))]
    simp_rw [integral_finsetSum _ (fun j _ => hAi _ j)]
    calc
      _ ≤ ∑ _i : Fin N, ∑ _j : Fin N, c * ∫ X, ‖EuclideanGradient ψ X‖^2 :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hAbound i j))
      _ = _ := by simp; ring
  have hgrad : Continuous (fun X : ParticleConfig d N => ‖EuclideanGradient (PairInteraction s coupling ε) X‖) := by
    have heq : (fun X : ParticleConfig d N => ‖EuclideanGradient (PairInteraction s coupling ε) X‖) =
        fun X => ‖fderiv ℝ (PairInteraction s coupling ε) X‖ :=
      funext (fun X => (GradientNormIdentity _ X).2)
    rw [heq]
    exact (hU.continuous_fderiv (by simp)).norm
  have hθ : 0 < ForceExponent s := by unfold ForceExponent; positivity
  have hp : ∀ X : ParticleConfig d N,
      ‖EuclideanGradient (PairInteraction s coupling ε) X‖ ^ (ForceExponent s) * (ψ X)^2 ≤
        K * ∑ i : Fin N, ∑ j : Fin N, A i j X := by
    intro X
    have hh := mul_le_mul_of_nonneg_right (hpower X) (sq_nonneg (ψ X))
    have heq : (K * ∑ i : Fin N, ∑ j : Fin N,
        if i < j then 1 / ‖ParticlePosition X i - ParticlePosition X j‖ ^ 2 else 0) * (ψ X)^2 =
        K * ∑ i : Fin N, ∑ j : Fin N, A i j X := by
      rw [mul_assoc, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i < j <;> simp [A, hij, div_eq_mul_inv] <;> ring
    rw [heq] at hh
    exact hh
  have hm : Measurable (fun X : ParticleConfig d N =>
      ‖EuclideanGradient (PairInteraction s coupling ε) X‖ ^ (ForceExponent s) * (ψ X)^2) :=
    (hgrad.measurable.pow_const _).mul (hψ.continuous.measurable.pow_const 2)
  have hi : Integrable (fun X : ParticleConfig d N =>
      ‖EuclideanGradient (PairInteraction s coupling ε) X‖ ^ (ForceExponent s) * (ψ X)^2) volume := by
    apply (hAsum.const_mul K).mono' hm.aestronglyMeasurable
    filter_upwards [] with X
    rw [Real.norm_of_nonneg (by positivity : 0 ≤
      ‖EuclideanGradient (PairInteraction s coupling ε) X‖ ^ (ForceExponent s) * (ψ X)^2)]
    exact hp X
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ X, K * ∑ i : Fin N, ∑ j : Fin N, A i j X :=
      integral_mono hi (hAsum.const_mul K) hp
    _ = K * ∫ X, ∑ i : Fin N, ∑ j : Fin N, A i j X := integral_const_mul K _
    _ ≤ K * ((N : ℝ)^2 * c * ∫ X, ‖EuclideanGradient ψ X‖^2) :=
      mul_le_mul_of_nonneg_left htotal hK
    _ = _ := by dsimp [H]; ring
