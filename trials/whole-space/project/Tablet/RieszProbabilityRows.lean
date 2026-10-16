import Tablet.RieszKernelBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic
open MeasureTheory Filter Set Metric
open scoped ENNReal
set_option maxHeartbeats 1000000

-- [TABLET NODE: RieszProbabilityRows]
theorem RieszProbabilityRows (d : ℕ) (hd : 1 ≤ d) (s Q : ℝ)
    (hs : 0 < s) (hsd : s < (d : ℝ)) (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ), 0 ≤ ε →
      ∀ (μ : Measure (OneParticle d)), IsProbabilityMeasure μ →
      μ ≤ ENNReal.ofReal Q • volume → ∀ y : OneParticle d,
      Integrable (fun x => RieszKernel s ε (x - y)) μ ∧
      (∫ x, RieszKernel s ε (x - y) ∂μ) ≤ C := by
-- BODY
  let near := fun x : OneParticle d => if ‖x‖ < 1 then ‖x‖ ^ (-s) else 0
  let far := fun x : OneParticle d => if ‖x‖ < 1 then 0 else ‖x‖ ^ (-s)
  have hn (x) : 0 ≤ near x := by dsimp [near]; split_ifs <;> positivity
  have hf (x) : 0 ≤ far x := by dsimp [far]; split_ifs <;> positivity
  have hfb (x) : far x ≤ 1 := by
    dsimp [far]
    split_ifs with h
    · norm_num
    · simpa using Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1)
        (le_of_not_gt h) (by linarith : -s ≤ 0)
  have hni : Integrable near volume := by
    have hdim : 1 ≤ Module.finrank ℝ (OneParticle d) := by simpa [OneParticle] using hd
    have hsd' : s < Module.finrank ℝ (OneParticle d) := by simpa [OneParticle] using hsd
    have hm : AEStronglyMeasurable (fun x : OneParticle d => ‖x‖ ^ (-s)) volume :=
      (continuous_norm.measurable.pow_const _).aestronglyMeasurable
    have hi := integrableOn_ball_of_norm_le_rpow (μ := (volume : Measure (OneParticle d)))
      hdim hsd' (C := (1 : ℝ)) (r := 1)
      (by filter_upwards with x; simp [Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) (-s))]) hm
    have he : near = (ball (0 : OneParticle d) 1).indicator
        (fun x => ‖x‖ ^ (-s)) := by funext x; simp [near, Set.indicator]
    rw [he]
    exact (integrable_indicator_iff measurableSet_ball).2 hi
  let C := (Q * (∫ x, near x) + 1) / s
  have hC : 0 ≤ C := div_nonneg
    (add_nonneg (mul_nonneg hQ (integral_nonneg hn)) zero_le_one) hs.le
  refine ⟨C, hC, ?_⟩
  intro ε hε μ hProb hdom y
  let : IsProbabilityMeasure μ := hProb
  have hniv : Integrable (fun x => near (x - y)) volume := by
    simpa only [sub_eq_add_neg] using hni.comp_add_right (-y)
  have hnis := hniv.smul_measure (c := ENNReal.ofReal Q) ENNReal.ofReal_ne_top
  have hnim := hnis.mono_measure hdom
  have hnear := integral_mono_measure hdom (Eventually.of_forall fun x => hn (x - y)) hnis
  rw [integral_smul_measure, ENNReal.toReal_ofReal hQ, smul_eq_mul] at hnear
  have htrans : (∫ x : OneParticle d, near (x - y)) = ∫ x, near x := by
    simpa only [sub_eq_add_neg] using integral_add_right_eq_self near (-y)
      (μ := (volume : Measure (OneParticle d)))
  rw [htrans] at hnear
  have hfm : Measurable (fun x => far (x - y)) := by
    dsimp [far]
    exact Measurable.ite
      (measurableSet_lt (continuous_norm.comp (continuous_id.sub continuous_const)).measurable
        measurable_const) measurable_const
      ((continuous_norm.comp (continuous_id.sub continuous_const)).measurable.pow_const _)
  have hfim : Integrable (fun x => far (x - y)) μ :=
    (integrable_const (1 : ℝ)).mono' hfm.aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf _)]; exact hfb _)
  have hfar : (∫ x, far (x - y) ∂μ) ≤ 1 := by
    simpa using integral_mono hfim (integrable_const (1 : ℝ)) (fun x => hfb (x - y))
  have he (x : OneParticle d) : RieszKernel s 0 (x - y) =
      (near (x - y) + far (x - y)) / s := by
    simp only [RieszKernel, near, far]
    split_ifs <;> simp
  have hsing : Integrable (fun x => RieszKernel s 0 (x - y)) μ := by
    simp_rw [he]
    exact (hnim.add hfim).div_const s
  have hrow : (∫ x, RieszKernel s 0 (x - y) ∂μ) ≤ C := by
    simp_rw [he]
    rw [integral_div, integral_add hnim hfim]
    exact div_le_div_of_nonneg_right (add_le_add hnear hfar) hs.le
  let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hz : μ {y} = 0 := le_antisymm (by simpa using hdom {y}) zero_le
  have hne : ∀ᵐ x ∂μ, x ≠ y := by rw [ae_iff]; simpa using hz
  have hbound : ∀ᵐ x ∂μ, RieszKernel s ε (x - y) ≤ RieszKernel s 0 (x - y) :=
    hne.mono fun x hx => (RieszKernelBounds s ε hs hε).2 _ (sub_ne_zero.mpr hx)
  have hm : Measurable (fun x : OneParticle d => RieszKernel s ε (x - y)) := by
    unfold RieszKernel
    split_ifs <;> fun_prop
  have hi : Integrable (fun x => RieszKernel s ε (x - y)) μ :=
    hsing.mono' hm.aestronglyMeasurable (hbound.mono fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg ((RieszKernelBounds s ε hs hε).1 _)]; exact hx)
  exact ⟨hi, (integral_mono_ae hi hsing hbound).trans hrow⟩
