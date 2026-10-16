import Tablet.RieszProbabilityRows
import Tablet.CommonReferenceDensity
import Tablet.ReferenceLawProbability
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic
open MeasureTheory Filter Set
open scoped ENNReal
set_option maxHeartbeats 1600000

-- [TABLET NODE: AtomicReferenceDensity]
theorem AtomicReferenceDensity (d : ℕ) (hd : 3 ≤ d) (s A κ M1 : ℝ)
    (hs : 0 < s) (hsd : s ≤ (d : ℝ) - 2) (hA : 0 ≤ A) (hκ : 0 < κ) :
    ∃ C H : ℝ, 0 ≤ C ∧ 0 < H ∧
    ∀ (V : OneParticle d → ℝ), Continuous V →
      (∀ x, κ / 2 * ‖x‖ ^ 2 ≤ V x) →
      (∀ x, ‖x‖ ≤ 1 → V x ≤ M1) →
    ∀ {ι : Type*} (J : Finset ι) (a : ι → ℝ) (y : ι → OneParticle d)
      (ε : ℝ), 0 < ε → (∀ j ∈ J, 0 ≤ a j) → (∑ j ∈ J, a j ≤ A) →
      let U := fun x => ∑ j ∈ J, a j * RieszKernel s ε (x - y j)
      let μ := ReferenceLaw V (fun _ => 1)
      let Z := ∫ x, Real.exp (-U x) ∂μ
      let W := fun x => V x + U x
      let p := fun x => (ReferencePartition W (fun _ => 1))⁻¹ * Real.exp (-W x)
      Integrable U μ ∧ (∫ x, U x ∂μ) ≤ A * C ∧
      Real.exp (-(A * C)) ≤ Z ∧ Z ≤ 1 ∧
      Z = (ReferencePartition V (fun _ => 1))⁻¹ * ReferencePartition W (fun _ => 1) ∧
      Integrable (fun x => Real.exp (-W x)) ∧
      0 < ReferencePartition W (fun _ => 1) ∧
      Measurable p ∧ IsProbabilityMeasure (ReferenceLaw W (fun _ => 1)) ∧
      volume.withDensity (fun x => ENNReal.ofReal (p x)) = ReferenceLaw W (fun _ => 1) ∧
      (∀ x, p x ≤ H * Real.exp (-(κ / 2) * ‖x‖ ^ 2)) ∧
      (∀ R MR T : ℝ, (∀ x, ‖x‖ ≤ R → V x ≤ MR) →
        ∀ x, ‖x‖ ≤ R → U x ≤ T →
        Real.exp (-MR - T) / (∫ z : OneParticle d, Real.exp (-(κ / 2) * ‖z‖ ^ 2)) ≤ p x) := by
-- BODY
  let v := (volume : Measure (OneParticle d)).real (Metric.ball 0 1)
  have hv : 0 < v := ENNReal.toReal_pos
    (ne_of_gt (Metric.measure_ball_pos volume (0 : OneParticle d) (by norm_num)))
    (ne_of_lt (lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
      (isCompact_closedBall (0 : OneParticle d) 1).measure_lt_top))
  let Q := Real.exp M1 / v
  have hQ : 0 < Q := div_pos (Real.exp_pos _) hv
  obtain ⟨C, hC, hrow⟩ := RieszProbabilityRows d (by omega) s Q hs (by linarith) hQ.le
  let H := Real.exp (A * C) * Q
  refine ⟨C, H, hC, mul_pos (Real.exp_pos _) hQ, ?_⟩
  intro V hV hquad hlocal ι J a y ε hε ha hmass
  dsimp only
  let U := fun x => ∑ j ∈ J, a j * RieszKernel s ε (x - y j)
  let μ := ReferenceLaw V (fun _ => 1)
  let Z := ∫ x, Real.exp (-U x) ∂μ
  let W := fun x => V x + U x
  let ZV := ReferencePartition V (fun _ => 1)
  let ZW := ReferencePartition W (fun _ => 1)
  let r := fun x => ZV⁻¹ * Real.exp (-V x)
  let p := fun x => ZW⁻¹ * Real.exp (-W x)
  have hb : BoundedMultiplier d 1 (fun _ => 1) :=
    ⟨measurable_const, 1, 1, by norm_num, le_rfl, by norm_num, fun _ => ⟨le_rfl, le_rfl⟩⟩
  obtain ⟨hiV, hZV⟩ := ReferenceQuadraticNormalization V (fun _ => 1) κ 0 1 hκ hV hb
    (fun x => by simpa using hquad x)
  have hiV' : Integrable (fun x => Real.exp (-V x)) := by simpa using hiV
  letI : IsProbabilityMeasure μ := ReferenceLawProbability V (fun _ => 1) hiV
    (fun _ => by norm_num) hZV
  have hdens := CommonReferenceDensity V (fun _ => 1) κ 1 1 M1 hκ
    (by norm_num) le_rfl hV measurable_const (fun _ => by norm_num) hquad hlocal
  have hdom : μ ≤ ENNReal.ofReal Q • volume := by simpa [μ, Q, v] using hdens.2.2.2.2.2
  have hUn (x) : 0 ≤ U x := Finset.sum_nonneg fun j hj =>
    mul_nonneg (ha j hj) ((RieszKernelBounds s ε hs hε.le).1 _)
  have hUm : Measurable U := by
    apply Finset.measurable_sum
    intro j hj
    have hm : Measurable (fun x : OneParticle d => RieszKernel s ε (x - y j)) := by
      unfold RieszKernel
      split_ifs <;> fun_prop
    exact hm.const_mul _
  have rows (j : ι) := hrow ε hε.le μ inferInstance hdom (y j)
  have hiU : Integrable U μ := integrable_finsetSum J (fun j hj => (rows j).1.const_mul (a j))
  have hmean : (∫ x, U x ∂μ) ≤ A * C := by
    rw [integral_finsetSum J (fun j hj => (rows j).1.const_mul (a j))]
    simp_rw [integral_const_mul]
    calc
      _ ≤ ∑ j ∈ J, a j * C := Finset.sum_le_sum
        (fun j hj => mul_le_mul_of_nonneg_left (rows j).2 (ha j hj))
      _ = (∑ j ∈ J, a j) * C := by rw [Finset.sum_mul]
      _ ≤ A * C := mul_le_mul_of_nonneg_right hmass hC
  have hiZ : Integrable (fun x => Real.exp (-U x)) μ :=
    (integrable_const (1 : ℝ)).mono' hUm.neg.exp.aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hUn x)))
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Eventually.of_forall fun _ => Set.mem_univ _) hiU.neg hiZ
  simp only [Pi.neg_apply] at hj
  rw [integral_neg] at hj
  have hZlower : Real.exp (-(A * C)) ≤ Z :=
    (Real.exp_le_exp.mpr (neg_le_neg hmean)).trans hj
  have hZone : Z ≤ 1 := by
    simpa [Z] using integral_mono hiZ (integrable_const (1 : ℝ))
      (fun x => Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hUn x)))
  have hZ : 0 < Z := (Real.exp_pos _).trans_le hZlower
  have hident : Z = ZV⁻¹ * ZW := by
    dsimp [Z, μ]
    unfold ReferenceLaw
    have hm : Measurable (fun x : OneParticle d => ENNReal.ofReal
        ((ReferencePartition V (fun _ => 1))⁻¹ * (1 * Real.exp (-V x)))) := by
      fun_prop
    rw [integral_withDensity_eq_integral_toReal_smul hm
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp_rw [ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.mpr hZV.le)
      (mul_nonneg zero_le_one (Real.exp_pos _).le)), smul_eq_mul, one_mul]
    have he : (fun x : OneParticle d => ZV⁻¹ * Real.exp (-V x) * Real.exp (-U x)) =
        fun x => ZV⁻¹ * Real.exp (-W x) := by
      funext x
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      dsimp [W]; ring
    rw [he, integral_const_mul]
    simp [ZW, ReferencePartition]
  have hZW : 0 < ZW := by
    rw [hident] at hZ
    exact (mul_pos_iff.mp hZ).elim (fun h => h.2)
      (fun h => False.elim (not_lt_of_ge (inv_nonneg.mpr hZV.le) h.1))
  have hiW : Integrable (fun x => Real.exp (-W x)) := hiV'.mono'
    (hV.measurable.add hUm).neg.exp.aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (by dsimp [W]; linarith [hUn x]))
  have hpident (x) : p x = Z⁻¹ * (r x * Real.exp (-U x)) := by
    dsimp [p, r]
    rw [hident, mul_inv_rev, inv_inv]
    have he : Real.exp (-W x) = Real.exp (-V x) * Real.exp (-U x) := by
      rw [← Real.exp_add]; congr 1; dsimp [W]; ring
    rw [he]
    field_simp [show ZV ≠ 0 from ne_of_gt hZV]
  refine ⟨hiU, hmean, hZlower, hZone, hident, hiW, hZW,
    (measurable_const.mul (hV.measurable.add hUm).neg.exp),
    ReferenceLawProbability W (fun _ => 1) (by simpa using hiW) (fun _ => by norm_num) hZW,
    by simp [ReferenceLaw, p], ?_, ?_⟩
  · intro x
    change p x ≤ H * Real.exp (-(κ / 2) * ‖x‖ ^ 2)
    have hr : 0 ≤ r x := mul_nonneg (inv_nonneg.mpr hZV.le) (Real.exp_pos _).le
    have hupper : r x ≤ Q * Real.exp (-(κ / 2) * ‖x‖ ^ 2) := by
      simpa [r, ZV, Q, v] using hdens.2.2.2.1 x
    have hnum : r x * Real.exp (-U x) ≤ Q * Real.exp (-(κ / 2) * ‖x‖ ^ 2) :=
      (mul_le_of_le_one_right hr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hUn x)))).trans hupper
    have hh := div_le_div₀ (by positivity : 0 ≤ Q * Real.exp (-(κ / 2) * ‖x‖ ^ 2))
      hnum (Real.exp_pos (-(A * C))) hZlower
    rw [hpident]
    simpa [H, div_eq_mul_inv, Real.exp_neg, mul_assoc, mul_comm, mul_left_comm] using hh
  · intro R MR T hloc x hx hUx
    let G := ∫ z : OneParticle d, Real.exp (-(κ / 2) * ‖z‖ ^ 2)
    have hG : 0 < G := (GaussianConfinementIntegral (ι := Fin d) κ hκ).2.2
    have hr : 0 ≤ r x := mul_nonneg (inv_nonneg.mpr hZV.le) (Real.exp_pos _).le
    have hlower : Real.exp (-MR) / G ≤ r x := by
      simpa [r, ZV, G] using hdens.2.2.2.2.1 R MR hloc x hx
    have hn := mul_le_mul hlower (Real.exp_le_exp.mpr (neg_le_neg hUx))
      (Real.exp_pos (-T)).le hr
    have hh := div_le_div₀ (mul_nonneg hr (Real.exp_pos _).le) hn hZ hZone
    change Real.exp (-MR - T) / G ≤ p x
    rw [hpident]
    have he : Real.exp (-MR - T) / G = (Real.exp (-MR) / G) * Real.exp (-T) := by
      rw [sub_eq_add_neg, Real.exp_add]; ring
    rw [he]
    simpa [div_eq_mul_inv, mul_comm] using hh
