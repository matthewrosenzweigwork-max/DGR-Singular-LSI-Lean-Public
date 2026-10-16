import Tablet.RieszProbabilityRows
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
open MeasureTheory Filter Set Metric
open scoped ENNReal
set_option maxHeartbeats 1500000

namespace MayerUniformRemainder
private theorem scalar_bounds (a u : ℝ) (ha : 0 ≤ a) (hu : 0 ≤ u) :
    0 ≤ a*u-1+Real.exp (-a*u) ∧
    a*u-1+Real.exp (-a*u) ≤ a*u ∧
    a*u-1+Real.exp (-a*u) ≤ a^2*u^2/2 := by
  have hl := Real.add_one_le_exp (-a*u)
  have he : Real.exp (-a*u) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  let F := fun x : ℝ => x^2/2-x+1-Real.exp (-x)
  have hder (x : ℝ) : HasDerivAt F (x-1+Real.exp (-x)) x := by
    have h := (((((hasDerivAt_id x).pow 2).div_const 2).sub (hasDerivAt_id x)).add_const 1).sub
      ((hasDerivAt_id x).neg.exp)
    convert h using 1 <;> first | rfl | simp
  have hm : Monotone F := monotone_of_hasDerivAt_nonneg hder
    (fun x => by change 0 ≤ x-1+Real.exp (-x); nlinarith [Real.add_one_le_exp (-x)])
  have hq := hm (mul_nonneg ha hu)
  dsimp [F] at hq
  norm_num at hq
  simp only [mul_pow, neg_mul] at *
  exact ⟨by linarith, by linarith, by linarith⟩

private noncomputable def near {d : ℕ} (s r : ℝ) (x : OneParticle d) : ℝ :=
  if ‖x‖ < r then ‖x‖ ^ (-s) else 0

private theorem near_nonneg {d : ℕ} (s r : ℝ) (x : OneParticle d) :
    0 ≤ near s r x := by unfold near; split_ifs <;> positivity

private theorem near_integrable (d : ℕ) (hd : 1 ≤ d) (s r : ℝ)
    (hsd : s < (d : ℝ)) : Integrable (near (d := d) s r) volume := by
  have hdim : 1 ≤ Module.finrank ℝ (OneParticle d) := by simpa [OneParticle] using hd
  have hsd' : s < Module.finrank ℝ (OneParticle d) := by simpa [OneParticle] using hsd
  have hm : AEStronglyMeasurable (fun x : OneParticle d => ‖x‖ ^ (-s)) volume :=
    (continuous_norm.measurable.pow_const _).aestronglyMeasurable
  have hi := integrableOn_ball_of_norm_le_rpow (μ := (volume : Measure (OneParticle d)))
    hdim hsd' (C := (1 : ℝ)) (r := r)
    (by filter_upwards with x; simp [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) (-s))]) hm
  have he : near (d := d) s r = (ball (0 : OneParticle d) r).indicator
      (fun x => ‖x‖ ^ (-s)) := by funext x; simp [near, Set.indicator]
  rw [he]
  exact (integrable_indicator_iff measurableSet_ball).2 hi

private theorem near_scale (d : ℕ) (s r : ℝ) (hr : 0 < r) :
    (∫ x : OneParticle d, near s r x) =
      (∫ x : OneParticle d, near s 1 x) * r ^ ((d : ℝ) - s) := by
  have hsmul (x : OneParticle d) : near s r (r • x) = r ^ (-s) * near s 1 x := by
    have hn : ‖r • x‖ = r * ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    have hlt : r * ‖x‖ < r ↔ ‖x‖ < 1 := by
      constructor <;> intro h <;> nlinarith
    simp only [near, hn, hlt]
    split_ifs
    · exact Real.mul_rpow hr.le (norm_nonneg x)
    · ring
  have hc := Measure.integral_comp_smul_of_nonneg
    (volume : Measure (OneParticle d)) (near s r) r (hR := hr.le)
  simp only [OneParticle, finrank_euclideanSpace_fin, smul_eq_mul] at hc
  simp_rw [hsmul] at hc
  rw [integral_const_mul] at hc
  have hpow : r ^ d ≠ 0 := pow_ne_zero _ hr.ne'
  have hm := congrArg (fun z : ℝ => r ^ d * z) hc
  have hi : (∫ x : OneParticle d, near s r x) =
      r ^ d * r ^ (-s) * (∫ x : OneParticle d, near s 1 x) := by
    simp only [← mul_assoc, mul_inv_cancel₀ hpow, one_mul] at hm
    exact hm.symm
  rw [hi, ← Real.rpow_natCast r d, ← Real.rpow_add hr]
  rw [sub_eq_add_neg, mul_comm]

private theorem split_bound {d : ℕ} (s r a ε : ℝ)
    (hs : 0 < s) (hr : 0 < r) (ha : 0 < a) (hε : 0 ≤ ε)
    (z : OneParticle d) (hz : z ≠ 0) :
    (a * RieszKernel s ε z - 1 + Real.exp (-a * RieszKernel s ε z)) / a ≤
      near s r z / s + (a / 2) * (r ^ (-s) / s) * RieszKernel s ε z := by
  let g := RieszKernel s ε z
  have hg : 0 ≤ g := (RieszKernelBounds s ε hs hε).1 z
  have hb := scalar_bounds a g ha.le hg
  by_cases hn : ‖z‖ < r
  · have hsing : near s r z / s = RieszKernel s 0 z := by
      simp [near, hn, RieszKernel]
    have hcmp := (RieszKernelBounds s ε hs hε).2 z hz
    have hdiv : (a*g-1+Real.exp (-a*g))/a ≤ g :=
      (div_le_iff₀ ha).mpr (by nlinarith only [hb.2.1])
    rw [hsing]
    exact hdiv.trans (hcmp.trans (le_add_of_nonneg_right (by positivity)))
  · have hT : g ≤ r ^ (-s) / s := by
      apply ((RieszKernelBounds s ε hs hε).2 z hz).trans
      simp only [RieszKernel]
      exact div_le_div_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hr (le_of_not_gt hn) (by linarith)) hs.le
    have hdiv : (a*g-1+Real.exp (-a*g))/a ≤ (a/2)*g*g :=
      (div_le_iff₀ ha).mpr (by nlinarith only [hb.2.2])
    have hmul : (a/2)*g*g ≤ (a/2)*(r^(-s)/s)*g := by gcongr
    simpa only [near, hn, if_false, zero_div, zero_add] using hdiv.trans hmul
end MayerUniformRemainder

-- [TABLET NODE: MayerUniformRemainder]
theorem MayerUniformRemainder (d : ℕ) (hd : 1 ≤ d) (s Q : ℝ)
    (hs : 0 < s) (hsd : s < (d : ℝ)) (hQ : 0 ≤ Q) :
    ∀ δ : ℝ, 0 < δ → ∃ a₀ : ℝ, 0 < a₀ ∧
    ∀ (μ : Measure (OneParticle d)), IsProbabilityMeasure μ →
      μ ≤ ENNReal.ofReal Q • volume →
    ∀ ε : ℝ, 0 ≤ ε → ∀ a : ℝ, 0 ≤ a → a ≤ a₀ → ∀ y : OneParticle d,
      let R := fun x => a * RieszKernel s ε (x - y) - 1 +
        Real.exp (-a * RieszKernel s ε (x - y))
      Integrable R μ ∧ 0 ≤ (∫ x, R x ∂μ) ∧ (∫ x, R x ∂μ) ≤ a * δ := by
-- BODY
  intro δ hδ
  obtain ⟨C, hC, hrows⟩ := RieszProbabilityRows d hd s Q hs hsd hQ
  let p := (d : ℝ) - s
  let D := Q * (∫ x : OneParticle d, MayerUniformRemainder.near s 1 x) / s
  have hp : 0 < p := by dsimp [p]; linarith
  have hD : 0 ≤ D := div_nonneg (mul_nonneg hQ
    (integral_nonneg (MayerUniformRemainder.near_nonneg s 1))) hs.le
  let u := δ / (2 * (D + 1))
  let r := u ^ (1 / p)
  have hu : 0 < u := by dsimp [u]; positivity
  have hr : 0 < r := Real.rpow_pos_of_pos hu _
  have hrp : r ^ p = u := by
    dsimp [r]
    rw [← Real.rpow_mul hu.le]
    have he : (1 / p) * p = (1 : ℝ) := by field_simp
    rw [he, Real.rpow_one]
  have hnear : D * r ^ p ≤ δ / 2 := by
    rw [hrp]
    dsimp [u]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < 2 * (D + 1))).mpr
    nlinarith only [hδ]
  let A := (r ^ (-s) / s) * C / 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let a₀ := δ / (2 * (A + 1))
  have ha₀ : 0 < a₀ := by dsimp [a₀]; positivity
  refine ⟨a₀, ha₀, ?_⟩
  intro μ hprob hdom ε hε a ha haa₀ y
  let : IsProbabilityMeasure μ := hprob
  dsimp only
  let g := fun x => RieszKernel s ε (x - y)
  let R := fun x => a * g x - 1 + Real.exp (-a * g x)
  have hg (x) : 0 ≤ g x := (RieszKernelBounds s ε hs hε).1 _
  have hi := (hrows ε hε μ hprob hdom y).1
  have hm : Measurable R := by dsimp [R, g, RieszKernel]; split_ifs <;> fun_prop
  have hRi : Integrable R μ := (hi.const_mul a).mono' hm.aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (MayerUniformRemainder.scalar_bounds a _ ha (hg x)).1]
      exact (MayerUniformRemainder.scalar_bounds a _ ha (hg x)).2.1)
  refine ⟨hRi, integral_nonneg (fun x =>
    (MayerUniformRemainder.scalar_bounds a _ ha (hg x)).1), ?_⟩
  by_cases ha0 : a = 0
  · subst a; simp
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hfar : a * A ≤ δ / 2 := by
    calc
      a * A ≤ a₀ * A := mul_le_mul_of_nonneg_right haa₀ hA
      _ = A * (δ / (2 * (A + 1))) := by dsimp [a₀]; ring
      _ ≤ δ / 2 := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (by positivity : 0 < 2 * (A + 1))).mpr
        nlinarith only [hδ]
  have hniv : Integrable (fun x => MayerUniformRemainder.near s r (x - y)) volume := by
    simpa only [sub_eq_add_neg] using
      (MayerUniformRemainder.near_integrable d hd s r hsd).comp_add_right (-y)
  have hnis := hniv.smul_measure (c := ENNReal.ofReal Q) ENNReal.ofReal_ne_top
  have hnim := hnis.mono_measure hdom
  have hn := integral_mono_measure hdom (Eventually.of_forall fun x =>
    MayerUniformRemainder.near_nonneg s r (x - y)) hnis
  rw [integral_smul_measure, ENNReal.toReal_ofReal hQ, smul_eq_mul] at hn
  have htrans : (∫ x : OneParticle d, MayerUniformRemainder.near s r (x - y)) =
      ∫ x : OneParticle d, MayerUniformRemainder.near s r x := by
    simpa only [sub_eq_add_neg] using integral_add_right_eq_self
      (MayerUniformRemainder.near (d := d) s r) (-y) (μ := volume)
  rw [htrans, MayerUniformRemainder.near_scale d s r hr] at hn
  let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hz : μ {y} = 0 := le_antisymm (by simpa using hdom {y}) zero_le
  have hne : ∀ᵐ x ∂μ, x ≠ y := by rw [ae_iff]; simpa using hz
  have hcmp : (∫ x, R x / a ∂μ) ≤
      ∫ x, MayerUniformRemainder.near s r (x - y) / s +
        (a / 2) * (r ^ (-s) / s) * g x ∂μ := by
    apply integral_mono_ae (hRi.div_const a) ((hnim.div_const s).add (hi.const_mul _))
    exact hne.mono fun x hx => MayerUniformRemainder.split_bound s r a ε
      hs hr hap hε (x - y) (sub_ne_zero.mpr hx)
  rw [integral_div, integral_add (hnim.div_const s) (hi.const_mul _),
    integral_div, integral_const_mul] at hcmp
  have hbound : (∫ x, R x ∂μ) / a ≤ D * r ^ p + a * A := by
    apply hcmp.trans
    have hn' := div_le_div_of_nonneg_right hn hs.le
    have hg' := mul_le_mul_of_nonneg_left (hrows ε hε μ hprob hdom y).2
      (show 0 ≤ (a / 2) * (r ^ (-s) / s) by positivity)
    convert add_le_add hn' hg' using 1 <;> dsimp [D, p, A] <;> ring
  have hfinal : (∫ x, R x ∂μ) / a ≤ δ := hbound.trans (by linarith)
  simpa only [mul_comm] using (div_le_iff₀ hap).mp hfinal
