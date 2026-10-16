import Tablet.StrongMidpointMinimum
import Tablet.BoundedDensityEntropyMidpoint
import Tablet.L2BoxContinuousIntegral
import Tablet.L2DensityBoxComplete

open MeasureTheory
open scoped Topology

-- [TABLET NODE: L2EntropyQuadraticMinimum]
theorem L2EntropyQuadraticMinimum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M β : ℝ) (hM : 1 ≤ M) (hβ : 0 ≤ β)
    (a : Lp ℝ 2 μ) (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hT : ∀ f : Lp ℝ 2 μ, 0 ≤ inner ℝ f (T f)) :
    ∃ f : Lp ℝ 2 μ,
      (∀ᵐ x ∂μ, f x ∈ Set.Icc 0 M) ∧ (∫ x, f x ∂μ) = 1 ∧
      ∀ r : Lp ℝ 2 μ, (∀ᵐ x ∂μ, r x ∈ Set.Icc 0 M) → (∫ x, r x ∂μ) = 1 →
        (∫ x, f x * Real.log (f x) ∂μ) - inner ℝ f a + β / 2 * inner ℝ f (T f) ≤
          (∫ x, r x * Real.log (r x) ∂μ) - inner ℝ r a + β / 2 * inner ℝ r (T r) := by
-- BODY
  classical
  let K : Set (Lp ℝ 2 μ) := {f | (∀ᵐ x ∂μ, f x ∈ Set.Icc 0 M) ∧ (∫ x, f x ∂μ) = 1}
  let F : Lp ℝ 2 μ → ℝ := fun f =>
    (∫ x, f x * Real.log (f x) ∂μ) - inner ℝ f a + β / 2 * inner ℝ f (T f)
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hK := L2DensityBoxComplete μ M hM
  have hE : ContinuousOn (fun f : Lp ℝ 2 μ => ∫ x, f x * Real.log (f x) ∂μ) K := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hb := L2BoxContinuousIntegral μ M (fun z => z * Real.log z) Real.continuous_mul_log
    exact hb.comp (continuous_subtype_val.subtype_mk fun f : K => f.property.1)
  have hF : ContinuousOn F K :=
    (hE.sub ((continuous_id.inner continuous_const (𝕜 := ℝ)).continuousOn)).add
      (((continuous_id.inner T.continuous (𝕜 := ℝ)).const_mul (β / 2)).continuousOn)
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) M)).exists_bound_of_continuousOn
    Real.continuous_mul_log.continuousOn
  have hbdd : BddBelow (F '' K) := by
    refine ⟨-C - M * ‖a‖, ?_⟩
    rintro _ ⟨f, hf, rfl⟩
    have hb : ∀ᵐ x ∂μ, ‖f x‖ ≤ M := hf.1.mono fun _ hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
      exact hx.2
    have hfn : ‖f‖ ≤ M := by simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound hMp.le hb
    have he : ‖∫ x, f x * Real.log (f x) ∂μ‖ ≤ C := by
      simpa using norm_integral_le_of_norm_le_const (hf.1.mono fun x hx => hC (f x) hx)
    have hlin : inner ℝ f a ≤ M * ‖a‖ :=
      (le_abs_self _).trans ((show |inner ℝ f a| ≤ ‖f‖ * ‖a‖ by simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) f a).trans
        (mul_le_mul_of_nonneg_right hfn (norm_nonneg a)))
    have helo : -C ≤ ∫ x, f x * Real.log (f x) ∂μ := by
      rw [Real.norm_eq_abs] at he
      exact (abs_le.mp he).1
    have hq : 0 ≤ β / 2 * inner ℝ f (T f) := mul_nonneg (by positivity) (hT f)
    dsimp [F]
    linarith
  have hmid : ∀ u ∈ K, ∀ v ∈ K, ∃ z ∈ K,
      F z ≤ (F u + F v) / 2 - (1 / (8 * M)) * dist u v ^ 2 := by
    intro u hu v hv
    let z : Lp ℝ 2 μ := (1 / 2 : ℝ) • (u + v)
    have hz : ∀ᵐ x ∂μ, z x = (u x + v x) / 2 := by
      filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) (u + v), Lp.coeFn_add u v] with x hx hy
      dsimp [z]
      rw [hx]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hy]
      simp only [Pi.add_apply]
      ring
    have hzi : Integrable (fun x => z x) μ := (Lp.memLp z).integrable (by norm_num)
    have hui : Integrable (fun x => u x) μ := (Lp.memLp u).integrable (by norm_num)
    have hvi : Integrable (fun x => v x) μ := (Lp.memLp v).integrable (by norm_num)
    have hzK : z ∈ K := by
      constructor
      · filter_upwards [hz, hu.1, hv.1] with x hx hux hvx
        rw [hx]
        constructor <;> linarith [hux.1, hux.2, hvx.1, hvx.2]
      · rw [integral_congr_ae hz, integral_div, integral_add hui hvi, hu.2, hv.2]
        norm_num
    have hgap := (BoundedDensityEntropyMidpoint μ u v M hMp
      (Lp.aestronglyMeasurable u) (Lp.aestronglyMeasurable v) hu.1 hv.1).2.2.2
    have hsq : (∫ x, (u x - v x) ^ 2 ∂μ) = ‖u - v‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub u v] with x hx
      change (u x - v x) ^ 2 = (u - v) x * (u - v) x
      rw [hx]
      simp [sq]
    have hent : (∫ x, z x * Real.log (z x) ∂μ) =
        ∫ x, ((u x + v x) / 2) * Real.log ((u x + v x) / 2) ∂μ :=
      integral_congr_ae (hz.mono fun _ hx => by dsimp; rw [hx])
    rw [hsq, ← hent, ← dist_eq_norm] at hgap
    have hlinear : inner ℝ z a = (inner ℝ u a + inner ℝ v a) / 2 := by
      simp only [z, inner_smul_left, inner_add_left, RCLike.conj_to_real]
      ring
    have hquad : inner ℝ z (T z) = (inner ℝ u (T u) + inner ℝ v (T v)) / 2 -
        inner ℝ (u - v) (T (u - v)) / 4 := by
      simp only [z, map_smul, map_add, map_sub, inner_smul_left, inner_smul_right,
        inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, RCLike.conj_to_real]
      ring
    have hqle : inner ℝ z (T z) ≤ (inner ℝ u (T u) + inner ℝ v (T v)) / 2 := by
      rw [hquad]
      linarith [hT (u - v)]
    have hhq := mul_le_mul_of_nonneg_left hqle (show 0 ≤ β / 2 by positivity)
    refine ⟨z, hzK, ?_⟩
    dsimp [F]
    rw [hlinear]
    have hid : (dist u v ^ 2) / (8 * M) = 1 / (8 * M) * dist u v ^ 2 := by ring
    rw [hid] at hgap
    linarith
  obtain ⟨f, hf, hmin⟩ := StrongMidpointMinimum K F (1 / (8 * M)) (by positivity)
    hK.2.2 hK.2.1 hF hbdd hmid
  exact ⟨f, hf.1, hf.2, fun r hr hm => hmin r ⟨hr, hm⟩⟩
