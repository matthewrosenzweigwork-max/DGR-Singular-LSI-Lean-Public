import Tablet.EuclideanSobolev
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Tactic
set_option maxHeartbeats 2400000
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace WeakPotentialForm
private noncomputable abbrev criticalExponent (d : ℕ) (hd : 3 ≤ d) := SobolevExponent d hd
private theorem euclidean_sobolev (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ≥0, ∀ f : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ 1 f → HasCompactSupport f →
      eLpNorm f (criticalExponent d hd) volume ≤ C * eLpNorm (fderiv ℝ f) 2 volume := by
  obtain ⟨C, hC⟩ := EuclideanSobolev (ι := Fin d) (by simpa using hd)
  refine ⟨C, ?_⟩
  intro f hf hc
  have hn : eLpNorm (EuclideanGradient f) 2 volume = eLpNorm (fderiv ℝ f) 2 volume :=
    eLpNorm_congr_norm_ae (Filter.Eventually.of_forall (fun x => (GradientNormIdentity f x).2))
  simpa only [Fintype.card_fin, criticalExponent, hn] using hC f hf hc

private theorem transition_deriv_zero_left {x : ℝ} (hx : x ≤ 0) :
    deriv Real.smoothTransition x = 0 := by
  have hmin : IsLocalMin Real.smoothTransition x := by
    apply Filter.Eventually.of_forall
    intro y
    rw [Real.smoothTransition.zero_of_nonpos hx]
    exact Real.smoothTransition.nonneg y
  exact hmin.deriv_eq_zero

private theorem transition_deriv_zero_right {x : ℝ} (hx : 1 ≤ x) :
    deriv Real.smoothTransition x = 0 := by
  have hmax : IsLocalMax Real.smoothTransition x := by
    apply Filter.Eventually.of_forall
    intro y
    rw [Real.smoothTransition.one_of_one_le hx]
    exact Real.smoothTransition.le_one y
  exact hmax.deriv_eq_zero

private theorem transition_deriv_bounded :
    ∃ L : ℝ, 0 < L ∧ ∀ x, |deriv Real.smoothTransition x| ≤ L := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv_one
  obtain ⟨L, hL⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max L 0 + 1, by positivity, ?_⟩
  intro x
  by_cases h0 : x ≤ 0
  · rw [transition_deriv_zero_left h0, abs_zero]
    positivity
  by_cases h1 : 1 ≤ x
  · rw [transition_deriv_zero_right h1, abs_zero]
    positivity
  have hh := hL x ⟨(lt_of_not_ge h0).le, (lt_of_not_ge h1).le⟩
  rw [Real.norm_eq_abs] at hh
  exact hh.trans (by linarith [le_max_left L 0])

private noncomputable def squareRamp (t z : ℝ) : ℝ :=
  t * Real.smoothTransition ((z ^ 2 / t ^ 2 - 1) / 3)

private theorem squareRamp_zero_of_abs_le (t z : ℝ) (ht : 0 < t) (hz : |z| ≤ t) :
    squareRamp t z = 0 := by
  have hsq : z ^ 2 ≤ t ^ 2 := by nlinarith [sq_abs z, abs_nonneg z]
  have ht2 : 0 < t ^ 2 := by positivity
  have harg : (z ^ 2 / t ^ 2 - 1) / 3 ≤ 0 := by
    have hh : z ^ 2 / t ^ 2 ≤ 1 := (div_le_iff₀ ht2).2 (by simpa only [one_mul] using hsq)
    linarith
  simp only [squareRamp, Real.smoothTransition.zero_of_nonpos harg, mul_zero]

private theorem squareRamp_one_of_double_le_abs (t z : ℝ) (ht : 0 < t) (hz : 2 * t ≤ |z|) :
    squareRamp t z = t := by
  have hsq : 4 * t ^ 2 ≤ z ^ 2 := by nlinarith [sq_abs z]
  have ht2 : 0 < t ^ 2 := by positivity
  have harg : 1 ≤ (z ^ 2 / t ^ 2 - 1) / 3 := by
    have hh : 4 ≤ z ^ 2 / t ^ 2 := (le_div_iff₀ ht2).2 (by nlinarith)
    linarith
  simp only [squareRamp, Real.smoothTransition.one_of_one_le harg, mul_one]

private theorem squareRamp_nonneg (t z : ℝ) (ht : 0 ≤ t) : 0 ≤ squareRamp t z :=
  mul_nonneg ht (Real.smoothTransition.nonneg _)

private theorem squareRamp_le (t z : ℝ) (ht : 0 ≤ t) : squareRamp t z ≤ t := by
  unfold squareRamp
  have hh := mul_le_mul_of_nonneg_left
    (Real.smoothTransition.le_one ((z ^ 2 / t ^ 2 - 1) / 3)) ht
  simpa only [mul_one] using hh

private theorem squareRamp_zero (t : ℝ) (ht : 0 < t) : squareRamp t 0 = 0 :=
  squareRamp_zero_of_abs_le t 0 ht (by simpa only [abs_zero] using ht.le)

private theorem squareRamp_contDiff (t : ℝ) {n : ℕ∞} : ContDiff ℝ n (squareRamp t) := by
  unfold squareRamp
  have hc : ContDiff ℝ n Real.smoothTransition := Real.smoothTransition.contDiff
  have hc2 : ContDiff ℝ n (fun z : ℝ => z ^ 2 / t ^ 2) :=
    (contDiff_id.pow 2).div_const (t ^ 2)
  have hc3 : ContDiff ℝ n (fun z : ℝ => (z ^ 2 / t ^ 2 - 1) / 3) :=
    (hc2.sub contDiff_const).div_const 3
  exact contDiff_const.mul (hc.comp hc3)

private theorem squareRamp_comp_hasCompactSupport {E : Type*} [TopologicalSpace E]
    (ψ : E → ℝ) (hψ : HasCompactSupport ψ) (t : ℝ) (ht : 0 < t) :
    HasCompactSupport (fun x => squareRamp t (ψ x)) :=
  hψ.comp_left (squareRamp_zero t ht)

private theorem squareRamp_hasDerivAt (t z : ℝ) (ht : 0 < t) :
    HasDerivAt (squareRamp t)
      (deriv Real.smoothTransition ((z ^ 2 / t ^ 2 - 1) / 3) * (2 * z / (3 * t))) z := by
  have harg := ((((hasDerivAt_id z).pow 2).div_const (t ^ 2)).sub_const 1).div_const 3
  have hdiff : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)
  have htran := (hdiff ((z ^ 2 / t ^ 2 - 1) / 3)).hasDerivAt
  have hh := (htran.comp z harg).const_mul t
  simp only [Function.comp_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] at hh
  have heq : t * (deriv Real.smoothTransition ((z ^ 2 / t ^ 2 - 1) / 3) *
      (((2 : ℝ) * z ^ 1 * 1 / t ^ 2) / 3)) =
      deriv Real.smoothTransition ((z ^ 2 / t ^ 2 - 1) / 3) * (2 * z / (3 * t)) := by
    field_simp
  simp only [pow_one, mul_one] at heq
  rw [heq] at hh
  exact hh

private theorem squareRamp_deriv_zero_of_abs_le (t z : ℝ) (ht : 0 < t) (hz : |z| ≤ t) :
    deriv (squareRamp t) z = 0 := by
  have hsq : z ^ 2 ≤ t ^ 2 := by nlinarith [sq_abs z, abs_nonneg z]
  have ht2 : 0 < t ^ 2 := by positivity
  have harg : (z ^ 2 / t ^ 2 - 1) / 3 ≤ 0 := by
    have hh : z ^ 2 / t ^ 2 ≤ 1 := (div_le_iff₀ ht2).2 (by simpa only [one_mul] using hsq)
    linarith
  rw [(squareRamp_hasDerivAt t z ht).deriv, transition_deriv_zero_left harg]
  ring

private theorem squareRamp_deriv_zero_of_double_le_abs (t z : ℝ) (ht : 0 < t) (hz : 2 * t ≤ |z|) :
    deriv (squareRamp t) z = 0 := by
  have hsq : 4 * t ^ 2 ≤ z ^ 2 := by nlinarith [sq_abs z]
  have ht2 : 0 < t ^ 2 := by positivity
  have harg : 1 ≤ (z ^ 2 / t ^ 2 - 1) / 3 := by
    have hh : 4 ≤ z ^ 2 / t ^ 2 := (le_div_iff₀ ht2).2 (by nlinarith)
    linarith
  rw [(squareRamp_hasDerivAt t z ht).deriv, transition_deriv_zero_right harg]
  ring

private theorem squareRamp_deriv_bound (L : ℝ) (hL0 : 0 ≤ L)
    (hL : ∀ u, |deriv Real.smoothTransition u| ≤ L) (t z : ℝ) (ht : 0 < t) :
    |deriv (squareRamp t) z| ≤ 4 * L / 3 := by
  by_cases hz0 : |z| ≤ t
  · rw [squareRamp_deriv_zero_of_abs_le t z ht hz0, abs_zero]
    positivity
  by_cases hz1 : 2 * t ≤ |z|
  · rw [squareRamp_deriv_zero_of_double_le_abs t z ht hz1, abs_zero]
    positivity
  have hz : |z| ≤ 2 * t := (lt_of_not_ge hz1).le
  rw [(squareRamp_hasDerivAt t z ht).deriv, abs_mul]
  have hfactor : |2 * z / (3 * t)| ≤ 4 / 3 := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity : 0 < 3 * t)]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply (div_le_iff₀ (by positivity : 0 < 3 * t)).2
    nlinarith
  have hh := mul_le_mul (hL ((z ^ 2 / t ^ 2 - 1) / 3)) hfactor
    (abs_nonneg (2 * z / (3 * t))) hL0
  nlinarith

-- Actual gradient strip domination for compact C¹ Sobolev tests.
private theorem squareRamp_comp_fderiv_strip {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : E → ℝ) (hψ : Differentiable ℝ ψ) (L : ℝ) (hL0 : 0 ≤ L)
    (hL : ∀ u, |deriv Real.smoothTransition u| ≤ L) (t : ℝ) (ht : 0 < t) (x : E) :
    ‖fderiv ℝ (fun y => squareRamp t (ψ y)) x‖ ≤
      if t < |ψ x| ∧ |ψ x| < 2 * t then (4 * L / 3) * ‖fderiv ℝ ψ x‖ else 0 := by
  have hc := (squareRamp_hasDerivAt t (ψ x) ht).comp_hasFDerivAt x (hψ x).hasFDerivAt
  simp only [Function.comp_def] at hc
  rw [hc.fderiv, norm_smul, Real.norm_eq_abs]
  split_ifs with hstrip
  · have hh := squareRamp_deriv_bound L hL0 hL t (ψ x) ht
    rw [(squareRamp_hasDerivAt t (ψ x) ht).deriv] at hh
    exact mul_le_mul_of_nonneg_right hh (norm_nonneg _)
  · have hz : deriv (squareRamp t) (ψ x) = 0 := by
      by_cases hlow : |ψ x| ≤ t
      · exact squareRamp_deriv_zero_of_abs_le t (ψ x) ht hlow
      · have hhigh : 2 * t ≤ |ψ x| := by
          by_contra hh
          exact hstrip ⟨lt_of_not_ge hlow, lt_of_not_ge hh⟩
        exact squareRamp_deriv_zero_of_double_le_abs t (ψ x) ht hhigh
    rw [(squareRamp_hasDerivAt t (ψ x) ht).deriv] at hz
    rw [hz, abs_zero, zero_mul]


private theorem tail_power_lintegral (q h : ℝ) (hq : 1 < q) (hh : 0 < h) :
    (∫⁻ t : ℝ in Ioi h, ENNReal.ofReal (t ^ (-q))) =
      ENNReal.ofReal (h ^ (1 - q) / (q - 1)) := by
  have he : -q < (-1 : ℝ) := by linarith
  have hi := integrableOn_Ioi_rpow_of_lt he hh
  have hn : 0 ≤ᵐ[volume.restrict (Ioi h)] (fun t : ℝ => t ^ (-q)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (le_of_lt (hh.trans ht)) _
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn, integral_Ioi_rpow_of_lt he hh]
  congr 1
  have hexp : -q + 1 = 1 - q := by ring
  rw [hexp]
  have hq1 : q - 1 ≠ 0 := by linarith
  have h1q : 1 - q ≠ 0 := by linarith
  field_simp [hq1, h1q]
  ring

-- Genuine layer-cake consequence of the weak distribution hypothesis.
-- No squared-test form or Sobolev inequality is assumed.
private theorem weak_potential_set_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ x, 0 ≤ W x)
    (D q h : ℝ) (hD : 0 ≤ D) (hq : 1 < q) (hh : 0 < h)
    (hweak : ∀ t : ℝ, 0 < t → μ {x | t < W x} ≤ ENNReal.ofReal D * ENNReal.ofReal (t ^ (-q)))
    (E : Set Ω) (hE : MeasurableSet E) :
    (∫⁻ x in E, ENNReal.ofReal (W x) ∂μ) ≤
      ENNReal.ofReal h * μ E +
        ENNReal.ofReal D * ENNReal.ofReal (h ^ (1 - q) / (q - 1)) := by
  let F : ℝ → ℝ≥0∞ := fun t =>
    (Ioc (0 : ℝ) h).indicator (fun _ => μ E) t +
    (Ioi h).indicator (fun t => ENNReal.ofReal D * ENNReal.ofReal (t ^ (-q))) t
  have hFm : Measurable F := by
    exact (measurable_const.indicator measurableSet_Ioc).add
      ((measurable_const.mul (measurable_id.pow_const _).ennreal_ofReal).indicator measurableSet_Ioi)
  rw [lintegral_eq_lintegral_meas_lt (μ.restrict E)
    (Eventually.of_forall hW0) hW.aemeasurable]
  have hbound : ∀ t : ℝ, 0 < t → (μ.restrict E) {x | t < W x} ≤ F t := by
    intro t ht
    have hmeas : MeasurableSet {x | t < W x} := measurableSet_lt measurable_const hW
    rw [Measure.restrict_apply hmeas]
    by_cases hth : t ≤ h
    · have hle : μ ({x | t < W x} ∩ E) ≤ μ E := measure_mono inter_subset_right
      simpa [F, Set.indicator, ht, hth, show ¬h < t from not_lt_of_ge hth] using hle
    · have hle := (measure_mono (inter_subset_left : {x | t < W x} ∩ E ⊆ {x | t < W x})).trans (hweak t ht)
      simpa [F, Set.indicator, ht, hth, show h < t from lt_of_not_ge hth] using hle
  calc
    (∫⁻ t : ℝ in Ioi 0, (μ.restrict E) {x | t < W x})
        ≤ ∫⁻ t : ℝ in Ioi 0, F t := by
          apply lintegral_mono_ae
          filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
          exact hbound t ht
    _ ≤ ∫⁻ t : ℝ, F t := by
          simpa only [Measure.restrict_univ] using
            (lintegral_mono_set (f := F) (μ := volume) (subset_univ (Ioi (0 : ℝ))))
    _ = ENNReal.ofReal h * μ E +
        ENNReal.ofReal D * ENNReal.ofReal (h ^ (1 - q) / (q - 1)) := by
          unfold F
          rw [lintegral_add_left (measurable_const.indicator measurableSet_Ioc),
            lintegral_indicator measurableSet_Ioc, lintegral_indicator measurableSet_Ioi,
            lintegral_const, Measure.restrict_apply_univ,
            Real.volume_Ioc, sub_zero,
            lintegral_const_mul' (ENNReal.ofReal D)
              (fun t : ℝ => ENNReal.ofReal (t ^ (-q))) ENNReal.ofReal_ne_top,
            tail_power_lintegral q h hq hh]
          rw [mul_comm (μ E) (ENNReal.ofReal h)]


-- Exact optimization uses real exponents, without restricting s to s ≤ 1.
private theorem optimized_cutoff_identity (D m q : ℝ) (hD : 0 < D) (hm : 0 < m)
    (hq : 1 < q) :
    let h := (D / m) ^ (1 / q)
    h * m + D * (h ^ (1 - q) / (q - 1)) =
      q / (q - 1) * D ^ (1 / q) * m ^ (1 - 1 / q) := by
  dsimp
  have hq0 : q ≠ 0 := by linarith
  have hq1 : q - 1 ≠ 0 := by linarith
  have hDm : 0 < D / m := div_pos hD hm
  have he : 1 / q * (1 - q) = 1 / q - 1 := by field_simp
  rw [← Real.rpow_mul hDm.le, he, Real.rpow_sub hDm,
    Real.rpow_one, Real.div_rpow hD.le hm.le]
  have hid : m ^ (1 - 1 / q) = m / m ^ (1 / q) := by
    rw [Real.rpow_sub hm, Real.rpow_one]
  rw [hid]
  have hd : D ^ (1 / q) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hD _)
  have hm' : m ^ (1 / q) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hm _)
  field_simp
  <;> ring

private theorem optimized_weak_set_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ x, 0 ≤ W x)
    (D q : ℝ) (hD : 0 < D) (hq : 1 < q)
    (hweak : ∀ t : ℝ, 0 < t → μ {x | t < W x} ≤
      ENNReal.ofReal D * ENNReal.ofReal (t ^ (-q)))
    (E : Set Ω) (hE : MeasurableSet E) (hEfin : μ E ≠ ⊤) (hEpos : 0 < μ E) :
    (∫⁻ x in E, ENNReal.ofReal (W x) ∂μ) ≤
      ENNReal.ofReal (q / (q - 1) * D ^ (1 / q) * (μ E).toReal ^ (1 - 1 / q)) := by
  have hm : 0 < (μ E).toReal := ENNReal.toReal_pos (ne_of_gt hEpos) hEfin
  have hh : 0 < (D / (μ E).toReal) ^ (1 / q) :=
    Real.rpow_pos_of_pos (div_pos hD hm) _
  have H := weak_potential_set_bound μ W hW hW0 D q
    ((D / (μ E).toReal) ^ (1 / q)) hD.le hq hh hweak E hE
  have he := optimized_cutoff_identity D (μ E).toReal q hD hm hq
  dsimp at he
  conv at H => rhs; lhs; rhs; rw [← ENNReal.ofReal_toReal hEfin]
  rw [← ENNReal.ofReal_mul hh.le, ← ENNReal.ofReal_mul hD.le,
    ← ENNReal.ofReal_add (by positivity) (by positivity), he] at H
  exact H

private noncomputable def dyadicScale (k : ℤ) : ℝ := (2 : ℝ) ^ k

private lemma dyadicScale_pos (k : ℤ) : 0 < dyadicScale k := by
  exact zpow_pos (by norm_num) _

private lemma dyadicScale_succ (k : ℤ) : dyadicScale (k + 1) = 2 * dyadicScale k := by
  simp [dyadicScale, zpow_add₀, mul_comm]

-- A selected geometric weight already gives a uniform domination by the full sum.
private theorem dyadic_weight_domination (z : ℝ) :
    ENNReal.ofReal (z ^ 2) ≤ 16 * ∑' k : ℤ,
      if 2 * dyadicScale k ≤ |z| then ENNReal.ofReal ((dyadicScale k) ^ 2) else 0 := by
  by_cases hz : z = 0
  · simp [hz]
  have hzpos : 0 < |z| / 2 := by positivity
  obtain ⟨k, hk₁, hk₂⟩ := exists_mem_Ico_zpow hzpos (by norm_num : (1 : ℝ) < 2)
  change (2 : ℝ) ^ k ≤ |z| / 2 at hk₁
  change |z| / 2 < (2 : ℝ) ^ (k + 1) at hk₂
  have hk : 2 * dyadicScale k ≤ |z| := by dsimp [dyadicScale]; linarith
  have hk' : |z| < 4 * dyadicScale k := by
    change |z| / 2 < dyadicScale (k + 1) at hk₂
    rw [dyadicScale_succ] at hk₂
    linarith
  have hs : z ^ 2 ≤ 16 * (dyadicScale k) ^ 2 := by
    nlinarith [sq_abs z, dyadicScale_pos k, abs_nonneg z]
  calc
    ENNReal.ofReal (z ^ 2) ≤ ENNReal.ofReal (16 * (dyadicScale k) ^ 2) :=
      ENNReal.ofReal_le_ofReal hs
    _ = 16 * ENNReal.ofReal ((dyadicScale k) ^ 2) := by
      rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
    _ ≤ 16 * ∑' j : ℤ, if 2 * dyadicScale j ≤ |z| then
        ENNReal.ofReal ((dyadicScale j) ^ 2) else 0 := by
      gcongr
      simpa only [if_pos hk] using (ENNReal.le_tsum k (f := fun j : ℤ =>
        if 2 * dyadicScale j ≤ |z| then ENNReal.ofReal ((dyadicScale j) ^ 2) else 0))

private lemma dyadic_strips_disjoint (j k : ℤ) (z : ℝ)
    (hj : dyadicScale j < |z| ∧ |z| < 2 * dyadicScale j)
    (hk : dyadicScale k < |z| ∧ |z| < 2 * dyadicScale k) : j = k := by
  by_contra hne
  have aux : ∀ a b : ℤ, a < b →
      dyadicScale a < |z| ∧ |z| < 2 * dyadicScale a →
      dyadicScale b < |z| ∧ |z| < 2 * dyadicScale b → False := by
    intro a b hab ha hb
    have hab' : a + 1 ≤ b := by omega
    have hle : dyadicScale (a + 1) ≤ dyadicScale b :=
      zpow_le_zpow_right₀ (by norm_num) hab'
    rw [dyadicScale_succ] at hle
    linarith [ha.2, hb.1]
  rcases lt_or_gt_of_ne hne with h | h
  · exact aux j k h hj hk
  · exact aux k j h hk hj


private theorem weak_set_integral_ennreal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ x, 0 ≤ W x)
    (D q : ℝ) (hD : 0 < D) (hq : 1 < q)
    (hweak : ∀ t : ℝ, 0 < t → μ {x | t < W x} ≤
      ENNReal.ofReal D * ENNReal.ofReal (t ^ (-q)))
    (E : Set Ω) (hE : MeasurableSet E) (hEfin : μ E ≠ ⊤) :
    (∫⁻ x in E, ENNReal.ofReal (W x) ∂μ) ≤
      ENNReal.ofReal (q / (q - 1) * D ^ (1 / q)) * (μ E) ^ (1 - 1 / q) := by
  by_cases hz : μ E = 0
  · simp [Measure.restrict_eq_zero.mpr hz]
  have hm := ENNReal.toReal_pos hz hEfin
  have H := optimized_weak_set_integral μ W hW hW0 D q hD hq hweak E hE hEfin
    (pos_iff_ne_zero.mpr hz)
  rw [ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_rpow_of_pos hm, ENNReal.ofReal_toReal hEfin] at H
  exact H

-- The lower level-set norm is computed on the actual smooth squared-test ramp.
private theorem ramp_level_lp_lower {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (ψ : Ω → ℝ) (hψ : Measurable ψ) (t : ℝ) (ht : 0 < t)
    (p : ℝ≥0∞) (hp : p ≠ 0) (hpfin : p ≠ ⊤) :
    ENNReal.ofReal t * (μ {x | 2 * t ≤ |ψ x|}) ^ (1 / p.toReal) ≤
      eLpNorm (fun x => squareRamp t (ψ x)) p μ := by
  have hE : MeasurableSet {x | 2 * t ≤ |ψ x|} :=
    measurableSet_le measurable_const (continuous_abs.measurable.comp hψ)
  have H : eLpNorm (({x | 2 * t ≤ |ψ x|} : Set Ω).indicator (fun _ => t)) p μ ≤
      eLpNorm (fun x => squareRamp t (ψ x)) p μ := by
    apply eLpNorm_mono
    intro x
    by_cases hx : 2 * t ≤ |ψ x|
    · simp [Set.indicator, hx, squareRamp_one_of_double_le_abs t (ψ x) ht hx]
    · simp [Set.indicator, hx]
  rw [eLpNorm_indicator_const hE hp hpfin, Real.enorm_eq_ofReal (le_of_lt ht)] at H
  exact H

-- Squaring the genuine Euclidean Sobolev inequality gives the precise measure exponent.
private theorem ramp_level_sobolev (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ≥0, ∀ (ψ : EuclideanSpace ℝ (Fin d) → ℝ),
      ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∀ t : ℝ, 0 < t →
      ENNReal.ofReal (t ^ 2) *
        (volume {x | 2 * t ≤ |ψ x|}) ^ (1 - 2 / (d : ℝ)) ≤
      (C : ℝ≥0∞) ^ 2 * ∫⁻ x, ‖fderiv ℝ (fun y => squareRamp t (ψ y)) x‖ₑ ^ (2 : ℕ) := by
  obtain ⟨C, hC⟩ := euclidean_sobolev d hd
  refine ⟨C, ?_⟩
  intro ψ hψ hsupp t ht
  have hp0 : (criticalExponent d hd : ℝ≥0∞) ≠ 0 := by
    have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have hc : (0 : ℝ) < criticalExponent d hd := by
      change 0 < 2 * (d : ℝ) / ((d : ℝ) - 2)
      exact div_pos (by positivity) (by linarith)
    exact_mod_cast (ne_of_gt hc)
  have Hp := ramp_level_lp_lower volume ψ hψ.continuous.measurable t ht
    (criticalExponent d hd) hp0 ENNReal.coe_ne_top
  have Hr : ContDiff ℝ 1 (fun x => squareRamp t (ψ x)) :=
    (squareRamp_contDiff t).comp hψ
  have HS := Hp.trans (hC _ Hr (squareRamp_comp_hasCompactSupport ψ hsupp t ht))
  have Hsq := pow_le_pow_left' HS 2
  have hexp : (1 / (criticalExponent d hd : ℝ≥0∞).toReal) * 2 = 1 - 2 / (d : ℝ) := by
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    have hd2 : (d : ℝ) - 2 ≠ 0 := by
      have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    change (1 / (2 * (d : ℝ) / ((d : ℝ) - 2))) * 2 = 1 - 2 / (d : ℝ)
    field_simp
  simp only [mul_pow] at Hsq
  have hpow : ((volume {x | 2 * t ≤ |ψ x|}) ^ (1 / (criticalExponent d hd : ℝ≥0∞).toReal)) ^ (2 : ℕ) =
      (volume {x | 2 * t ≤ |ψ x|}) ^ (1 - 2 / (d : ℝ)) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num only [Nat.cast_ofNat]
    rw [hexp]
  rw [hpow] at Hsq
  have he : (ENNReal.ofReal t) ^ 2 = ENNReal.ofReal (t ^ 2) := by
    rw [← ENNReal.rpow_natCast, ENNReal.ofReal_rpow_of_pos ht, Real.rpow_natCast]
  rw [he] at Hsq
  have hn := eLpNorm_nnreal_pow_eq_lintegral (μ := volume)
    (f := fderiv ℝ (fun y => squareRamp t (ψ y))) (p := (2 : ℝ≥0)) (by norm_num)
  norm_num only [NNReal.coe_ofNat, ENNReal.rpow_natCast] at hn
  have hc : ((2 : ℝ≥0) : ℝ≥0∞) = 2 := by norm_num
  rw [hc] at hn
  have hpow2 : ∀ x : ℝ≥0∞, x ^ (2 : ℝ) = x ^ (2 : ℕ) := by
    intro x
    simpa only [Nat.cast_ofNat] using ENNReal.rpow_natCast x 2
  simp only [hpow2] at hn
  rw [hn] at Hsq
  exact Hsq


private noncomputable def stripWeight (k : ℤ) (z : ℝ) (G : ℝ≥0∞) : ℝ≥0∞ :=
  if dyadicScale k < |z| ∧ |z| < 2 * dyadicScale k then G else 0

private theorem stripWeight_tsum_le (z : ℝ) (G : ℝ≥0∞) :
    (∑' k : ℤ, stripWeight k z G) ≤ G := by
  classical
  by_cases h : ∃ k : ℤ, dyadicScale k < |z| ∧ |z| < 2 * dyadicScale k
  · obtain ⟨k, hk⟩ := h
    rw [tsum_eq_single k]
    · simp [stripWeight, hk]
    · intro j hj
      have hh : ¬ (dyadicScale j < |z| ∧ |z| < 2 * dyadicScale j) := by
        intro hh
        exact hj (dyadic_strips_disjoint j k z hh hk)
      simp [stripWeight, hh]
  · have hh : ∀ k : ℤ, stripWeight k z G = 0 := by
      intro k
      simp only [stripWeight, if_neg (fun hk => h ⟨k, hk⟩)]
    simp [hh]

private theorem actual_ramp_derivative_tsum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : E → ℝ) (hψ : Differentiable ℝ ψ) (L : ℝ) (hL0 : 0 ≤ L)
    (hL : ∀ u, |deriv Real.smoothTransition u| ≤ L) (x : E) :
    (∑' k : ℤ, ‖fderiv ℝ (fun y => squareRamp (dyadicScale k) (ψ y)) x‖ₑ ^ (2 : ℕ)) ≤
      ENNReal.ofReal ((4 * L / 3) ^ 2) * ‖fderiv ℝ ψ x‖ₑ ^ (2 : ℕ) := by
  calc
    (∑' k : ℤ, ‖fderiv ℝ (fun y => squareRamp (dyadicScale k) (ψ y)) x‖ₑ ^ (2 : ℕ)) ≤
        ∑' k : ℤ, stripWeight k (ψ x)
          (ENNReal.ofReal ((4 * L / 3) ^ 2) * ‖fderiv ℝ ψ x‖ₑ ^ (2 : ℕ)) := by
      apply ENNReal.tsum_le_tsum
      intro k
      have H := squareRamp_comp_fderiv_strip ψ hψ L hL0 hL (dyadicScale k) (dyadicScale_pos k) x
      by_cases hk : dyadicScale k < |ψ x| ∧ |ψ x| < 2 * dyadicScale k
      · simp only [if_pos hk] at H
        have HH := ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) H 2)
        simpa only [stripWeight, if_pos hk, mul_pow, ENNReal.ofReal_mul (sq_nonneg _),
          ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] using HH
      · simp only [if_neg hk] at H
        have hh : fderiv ℝ (fun y => squareRamp (dyadicScale k) (ψ y)) x = 0 :=
          norm_eq_zero.mp (le_antisymm H (norm_nonneg _))
        simp only [stripWeight, if_neg hk, ← ofReal_norm, hh, norm_zero,
          ENNReal.ofReal_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), le_refl]
    _ ≤ _ := stripWeight_tsum_le _ _

-- Tonelli assembly with the proved dyadic coefficient 16.
private theorem dyadic_form_assembly16 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (W ψsq energy : Ω → ℝ≥0∞) (b e : ℤ → Ω → ℝ≥0∞) (K : ℝ≥0∞)
    (hW : AEMeasurable W μ) (hb : ∀ k, AEMeasurable (b k) μ)
    (he : ∀ k, AEMeasurable (e k) μ)
    (hdyadic : ∀ x, ψsq x ≤ 16 * ∑' k : ℤ, b k x)
    (hlevel : ∀ k, (∫⁻ x, W x * b k x ∂μ) ≤ K * ∫⁻ x, e k x ∂μ)
    (hdisjoint : ∀ x, (∑' k : ℤ, e k x) ≤ energy x) :
    (∫⁻ x, W x * ψsq x ∂μ) ≤ 16 * K * ∫⁻ x, energy x ∂μ := by
  calc
    (∫⁻ x, W x * ψsq x ∂μ) ≤ ∫⁻ x, 16 * ∑' k : ℤ, W x * b k x ∂μ := by
      apply lintegral_mono
      intro x
      have H := mul_le_mul_left (hdyadic x) (W x)
      simpa only [ENNReal.tsum_mul_left, mul_assoc, mul_comm, mul_left_comm] using H
    _ = 16 * ∑' k : ℤ, ∫⁻ x, W x * b k x ∂μ := by
      rw [lintegral_const_mul' (16 : ℝ≥0∞) _ (by norm_num),
        lintegral_tsum (fun k => (show AEMeasurable (fun x => W x * b k x) μ from hW.mul (hb k)))]
    _ ≤ 16 * ∑' k : ℤ, K * ∫⁻ x, e k x ∂μ := by
      gcongr with k
      exact hlevel k
    _ = 16 * K * ∫⁻ x, ∑' k : ℤ, e k x ∂μ := by
      rw [ENNReal.tsum_mul_left, lintegral_tsum he, mul_assoc]
    _ ≤ 16 * K * ∫⁻ x, energy x ∂μ := by
      gcongr with x
      exact hdisjoint x


-- Actual finite measure for every positive compact-test level, not a distribution assumption.
private theorem compact_test_level_finite (d : ℕ) (ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hsupp : HasCompactSupport ψ) (t : ℝ) (ht : 0 < t) :
    volume {x | 2 * t ≤ |ψ x|} ≠ ⊤ := by
  have hsub : {x | 2 * t ≤ |ψ x|} ⊆ tsupport ψ := by
    intro x hx
    change 2 * t ≤ |ψ x| at hx
    apply subset_tsupport ψ
    change ψ x ≠ 0
    intro hz
    simp only [hz, abs_zero] at hx
    linarith
  exact ne_of_lt ((measure_mono hsub).trans_lt hsupp.measure_lt_top)

-- Weak L^(d/2) gives the gradient form bound on every actual compact C¹ test.
-- All ramps, level sets, derivatives and Euclidean measures are explicit.

end WeakPotentialForm

open WeakPotentialForm
-- [TABLET NODE: WeakPotentialForm]
theorem WeakPotentialForm (d : ℕ) (hd : 3 ≤ d) (q : ℝ)
    (hq : 1 < q) (hexp : 1 - 1 / q = 1 - 2 / (d : ℝ)) :
    ∃ B : ℝ≥0, ∀ D : ℝ, 0 < D →
      ∀ W : EuclideanSpace ℝ (Fin d) → ℝ, Measurable W → (∀ x, 0 ≤ W x) →
      (∀ t : ℝ, 0 < t → volume {x | t < W x} ≤
        ENNReal.ofReal D * ENNReal.ofReal (t ^ (-q))) →
      ∀ ψ : EuclideanSpace ℝ (Fin d) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫⁻ x, ENNReal.ofReal (W x) * ENNReal.ofReal ((ψ x) ^ 2)) ≤
          B * ENNReal.ofReal (D ^ (1 / q)) * ∫⁻ x, ‖fderiv ℝ ψ x‖ₑ ^ (2 : ℕ) := by
-- BODY
  classical
  obtain ⟨C, hC⟩ := ramp_level_sobolev d hd
  obtain ⟨L, hL0, hL⟩ := transition_deriv_bounded
  let Q : ℝ≥0 := ⟨q / (q - 1), by positivity⟩
  let M : ℝ≥0 := ⟨(4 * L / 3) ^ 2, sq_nonneg _⟩
  refine ⟨16 * Q * C ^ 2 * M, ?_⟩
  intro D hD W hW hW0 hweak ψ hψ hsupp
  let b : ℤ → EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun k x =>
    if 2 * dyadicScale k ≤ |ψ x| then ENNReal.ofReal ((dyadicScale k) ^ 2) else 0
  let e : ℤ → EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun k x =>
    ‖fderiv ℝ (fun y => squareRamp (dyadicScale k) (ψ y)) x‖ₑ ^ (2 : ℕ)
  have hb : ∀ k, AEMeasurable (b k) volume := by
    intro k
    exact (measurable_const.ite
      (measurableSet_le measurable_const (continuous_abs.comp hψ.continuous).measurable) measurable_const).aemeasurable
  have he : ∀ k, AEMeasurable (e k) volume := by
    intro k
    exact (((squareRamp_contDiff (dyadicScale k)).comp hψ).continuous_fderiv (by norm_num)).measurable.enorm.pow_const 2 |>.aemeasurable
  have hlevel : ∀ k, (∫⁻ x, ENNReal.ofReal (W x) * b k x) ≤
      ENNReal.ofReal (q / (q - 1) * D ^ (1 / q)) * C ^ 2 * ∫⁻ x, e k x := by
    intro k
    let t := dyadicScale k
    have ht : 0 < t := dyadicScale_pos k
    let E : Set (EuclideanSpace ℝ (Fin d)) := {x | 2 * t ≤ |ψ x|}
    have hE : MeasurableSet E := measurableSet_le measurable_const (continuous_abs.comp hψ.continuous).measurable
    have H := weak_set_integral_ennreal volume W hW hW0 D q hD hq hweak E hE
      (compact_test_level_finite d ψ hsupp t ht)
    have HS := hC ψ hψ hsupp t ht
    rw [← hexp] at HS
    have hid : (∫⁻ x, ENNReal.ofReal (W x) * b k x) =
        ENNReal.ofReal (t ^ 2) * ∫⁻ x in E, ENNReal.ofReal (W x) := by
      have hf : (fun x => ENNReal.ofReal (W x) * b k x) =
          E.indicator (fun x => ENNReal.ofReal (t ^ 2) * ENNReal.ofReal (W x)) := by
        funext x
        by_cases hx : x ∈ E
        · change 2 * dyadicScale k ≤ |ψ x| at hx
          simp [E, b, t, hx, Set.indicator, mul_comm]
        · change ¬ 2 * dyadicScale k ≤ |ψ x| at hx
          simp [E, b, t, hx, Set.indicator]
      rw [hf, lintegral_indicator hE, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [hid]
    calc
      ENNReal.ofReal (t ^ 2) * ∫⁻ x in E, ENNReal.ofReal (W x) ≤
          ENNReal.ofReal (t ^ 2) * (ENNReal.ofReal (q / (q - 1) * D ^ (1 / q)) * volume E ^ (1 - 1 / q)) := by gcongr
      _ = ENNReal.ofReal (q / (q - 1) * D ^ (1 / q)) *
          (ENNReal.ofReal (t ^ 2) * volume E ^ (1 - 1 / q)) := by simp only [mul_assoc, mul_comm, mul_left_comm]
      _ ≤ ENNReal.ofReal (q / (q - 1) * D ^ (1 / q)) *
          (C ^ 2 * ∫⁻ x, e k x) := by
            exact mul_le_mul_right HS _
      _ = _ := by simp only [mul_assoc, mul_comm, mul_left_comm]
  have H := dyadic_form_assembly16 volume (fun x => ENNReal.ofReal (W x))
    (fun x => ENNReal.ofReal ((ψ x) ^ 2))
    (fun x => ENNReal.ofReal ((4 * L / 3) ^ 2) * ‖fderiv ℝ ψ x‖ₑ ^ (2 : ℕ)) b e
    (ENNReal.ofReal (q / (q - 1) * D ^ (1 / q)) * C ^ 2)
    hW.ennreal_ofReal.aemeasurable hb he (fun x => dyadic_weight_domination (ψ x)) hlevel
    (actual_ramp_derivative_tsum ψ (hψ.differentiable (by norm_num)) L hL0.le hL)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ENNReal.ofReal_mul (by positivity)] at H
  have hQ : (Q : ℝ≥0∞) = ENNReal.ofReal (q / (q - 1)) := by
    rw [← ENNReal.ofReal_coe_nnreal]; rfl
  have hM : (M : ℝ≥0∞) = ENNReal.ofReal ((4 * L / 3) ^ 2) := by
    rw [← ENNReal.ofReal_coe_nnreal]; rfl
  simpa only [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_ofNat, hQ, hM,
    mul_assoc, mul_comm, mul_left_comm] using H
