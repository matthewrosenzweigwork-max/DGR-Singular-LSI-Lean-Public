import Tablet.CommonReferenceDensity
import Tablet.ReferenceLawProbability
import Tablet.RieszProbabilityRows
import Mathlib.Tactic
open MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000

-- [TABLET NODE: ReferenceOffsetDensity]
theorem ReferenceOffsetDensity (d : ℕ) (hd : 1 ≤ d) (s κ L M1 : ℝ)
    (hs : 0 < s) (hsd : s < (d : ℝ)) (hκ : 0 < κ) (hL : 1 ≤ L) :
    let Q := L * Real.exp M1 /
      (volume : Measure (OneParticle d)).real (Metric.ball 0 1)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V b : OneParticle d → ℝ), Continuous V →
      BoundedMultiplier d L b →
      (∀ x, κ / 2 * ‖x‖ ^ 2 ≤ V x - V 0) →
      (∀ x, ‖x‖ ≤ 1 → V x - V 0 ≤ M1) →
      let W := fun x => V x - V 0
      ReferencePartition W b = Real.exp (V 0) * ReferencePartition V b ∧
      ReferenceLaw W b = ReferenceLaw V b ∧
      IsProbabilityMeasure (ReferenceLaw V b) ∧
      ReferenceLaw V b ≤ ENNReal.ofReal Q • volume ∧
      (∀ ε : ℝ, 0 ≤ ε → ∀ y : OneParticle d,
        Integrable (fun x => RieszKernel s ε (x - y)) (ReferenceLaw V b) ∧
        (∫ x, RieszKernel s ε (x - y) ∂ReferenceLaw V b) ≤ C) := by
-- BODY
  dsimp only
  let v := (volume : Measure (OneParticle d)).real (Metric.ball 0 1)
  let Q := L * Real.exp M1 / v
  have hv : 0 < v := ENNReal.toReal_pos
    (ne_of_gt (Metric.measure_ball_pos volume (0 : OneParticle d) (by norm_num)))
    (ne_of_lt (lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
      (isCompact_closedBall (0 : OneParticle d) 1).measure_lt_top))
  have hQ : 0 ≤ Q := div_nonneg (mul_nonneg (by linarith) (Real.exp_pos _).le) hv.le
  obtain ⟨C, hC, hrow⟩ := RieszProbabilityRows d hd s Q hs hsd hQ
  refine ⟨C, hC, ?_⟩
  intro V b hV hb hquad hlocal
  let W := fun x => V x - V 0
  have hW : Continuous W := hV.sub continuous_const
  obtain ⟨m, bmax, hm, _, hratio, hbounds⟩ := hb.bounds
  have hmax : bmax ≤ L * m := (div_le_iff₀ hm).mp hratio
  have hbound (x) : m ≤ b x ∧ b x ≤ L * m :=
    ⟨(hbounds x).1, (hbounds x).2.trans hmax⟩
  have hnorm := ReferenceQuadraticNormalization W b κ 0 L hκ hW hb
    (fun x => by simpa [W] using hquad x)
  have hprob : IsProbabilityMeasure (ReferenceLaw W b) :=
    ReferenceLawProbability W b hnorm.1 (fun x => hm.le.trans (hbounds x).1) hnorm.2
  have hcap := (CommonReferenceDensity W b κ m L M1 hκ hm hL hW hb.measurable
    hbound hquad hlocal).2.2.2.2.2
  have hexp (x : OneParticle d) : Real.exp (-(W x)) =
      Real.exp (V 0) * Real.exp (-V x) := by
    dsimp [W]
    rw [neg_sub, sub_eq_add_neg, Real.exp_add]
  have hpart : ReferencePartition W b = Real.exp (V 0) * ReferencePartition V b := by
    unfold ReferencePartition
    simp_rw [hexp]
    have he : (fun x => b x * (Real.exp (V 0) * Real.exp (-V x))) =
        fun x => Real.exp (V 0) * (b x * Real.exp (-V x)) := by funext x; ring
    rw [he, integral_const_mul]
  have hlaw : ReferenceLaw W b = ReferenceLaw V b := by
    unfold ReferenceLaw
    congr 1
    funext x
    rw [hpart, hexp, mul_inv_rev]
    congr 1
    field_simp [Real.exp_ne_zero (V 0)]
  rw [hlaw] at hprob hcap
  refine ⟨hpart, hlaw, hprob, hcap, ?_⟩
  intro ε hε y
  exact hrow ε hε (ReferenceLaw V b) hprob hcap y
