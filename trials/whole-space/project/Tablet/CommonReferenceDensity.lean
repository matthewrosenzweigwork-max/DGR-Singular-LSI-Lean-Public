import Tablet.ReferenceQuadraticNormalization
import Tablet.ReferenceLaw
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
open MeasureTheory Filter
open scoped ENNReal
set_option maxHeartbeats 800000

-- [TABLET NODE: CommonReferenceDensity]
theorem CommonReferenceDensity {d : ℕ} (V b : OneParticle d → ℝ)
    (κ m L M1 : ℝ) (hκ : 0 < κ) (hm : 0 < m) (hL : 1 ≤ L)
    (hV : Continuous V) (hb : Measurable b)
    (hbound : ∀ x, m ≤ b x ∧ b x ≤ L * m)
    (hquad : ∀ x, κ / 2 * ‖x‖ ^ 2 ≤ V x)
    (hlocal : ∀ x, ‖x‖ ≤ 1 → V x ≤ M1) :
    let v := (volume : Measure (OneParticle d)).real (Metric.ball 0 1)
    let G := ∫ x : OneParticle d, Real.exp (-(κ / 2) * ‖x‖ ^ 2)
    let q := fun x => (ReferencePartition V b)⁻¹ * (b x * Real.exp (-V x))
    0 < v ∧
    m * Real.exp (-M1) * v ≤ ReferencePartition V b ∧
    ReferencePartition V b ≤ L * m * G ∧
    (∀ x, q x ≤ (L * Real.exp M1 / v) * Real.exp (-(κ / 2) * ‖x‖ ^ 2)) ∧
    (∀ R MR : ℝ, (∀ x, ‖x‖ ≤ R → V x ≤ MR) →
      ∀ x, ‖x‖ ≤ R → Real.exp (-MR) / (L * G) ≤ q x) ∧
    ReferenceLaw V b ≤ ENNReal.ofReal (L * Real.exp M1 / v) • volume := by
-- BODY
  let gaussianIntegral (d : ℕ) (κ : ℝ) : ℝ :=
    ∫ x : OneParticle d, Real.exp (-(κ / 2) * ‖x‖ ^ 2)
  
  let unitBallVolume (d : ℕ) : ℝ :=
    (volume : Measure (OneParticle d)).real (Metric.ball 0 1)
  
  let referenceDensity {d : ℕ} (V b : OneParticle d → ℝ) (x : OneParticle d) : ℝ :=
    (ReferencePartition V b)⁻¹ * (b x * Real.exp (-V x))
  
  have unitBallVolume_finite (d : ℕ) :
      (volume : Measure (OneParticle d)) (Metric.ball 0 1) < ⊤ :=
    lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
      (isCompact_closedBall (0 : OneParticle d) 1).measure_lt_top
  
  have unitBallVolume_positive (d : ℕ) : 0 < unitBallVolume d := by
    unfold unitBallVolume Measure.real
    exact ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos volume (0 : OneParticle d) (by norm_num)))
      (ne_of_lt (unitBallVolume_finite d))
  
  have scaled_bounds_multiplier {d : ℕ} (b : OneParticle d → ℝ)
      (m L : ℝ) (hm : 0 < m) (hL : 1 ≤ L) (hb : Measurable b)
      (hbound : ∀ x, m ≤ b x ∧ b x ≤ L * m) : BoundedMultiplier d L b := by
    refine ⟨hb, m, L * m, hm, ?_, ?_, hbound⟩
    · nlinarith
    · have he : L * m / m = L := by field_simp
      exact he.le
  
  have reference_integrable_positive {d : ℕ} (V b : OneParticle d → ℝ)
      (κ m L : ℝ) (hκ : 0 < κ) (hm : 0 < m) (hL : 1 ≤ L)
      (hV : Continuous V) (hb : Measurable b)
      (hbound : ∀ x, m ≤ b x ∧ b x ≤ L * m)
      (hquad : ∀ x, κ / 2 * ‖x‖ ^ 2 ≤ V x) :
      Integrable (fun x => b x * Real.exp (-V x)) ∧ 0 < ReferencePartition V b := by
    apply ReferenceQuadraticNormalization V b κ 0 L hκ hV
      (scaled_bounds_multiplier b m L hm hL hb hbound)
    intro x
    simpa using hquad x
  
  have reference_partition_upper {d : ℕ} (V b : OneParticle d → ℝ)
      (κ m L : ℝ) (hκ : 0 < κ) (hm : 0 < m) (hL : 1 ≤ L)
      (hV : Continuous V) (hb : Measurable b)
      (hbound : ∀ x, m ≤ b x ∧ b x ≤ L * m)
      (hquad : ∀ x, κ / 2 * ‖x‖ ^ 2 ≤ V x) :
      ReferencePartition V b ≤ L * m * gaussianIntegral d κ := by
    have hi := (reference_integrable_positive V b κ m L hκ hm hL hV hb hbound hquad).1
    have hG := (GaussianConfinementIntegral (ι := Fin d) κ hκ).2.1
    calc
      ReferencePartition V b ≤ ∫ x : OneParticle d, (L * m) * Real.exp (-(κ / 2) * ‖x‖ ^ 2) := by
        apply integral_mono hi (hG.const_mul _)
        intro x
        have hLm : 0 ≤ L * m := by nlinarith
        simpa only [neg_mul] using mul_le_mul (hbound x).2
          (Real.exp_le_exp.mpr (neg_le_neg (hquad x))) (Real.exp_pos _).le hLm
      _ = L * m * gaussianIntegral d κ := by rw [integral_const_mul]
  
  have reference_partition_lower {d : ℕ} (V b : OneParticle d → ℝ)
      (κ m L M1 : ℝ) (hκ : 0 < κ) (hm : 0 < m) (hL : 1 ≤ L)
      (hV : Continuous V) (hb : Measurable b)
      (hbound : ∀ x, m ≤ b x ∧ b x ≤ L * m)
      (hquad : ∀ x, κ / 2 * ‖x‖ ^ 2 ≤ V x)
      (hlocal : ∀ x, ‖x‖ ≤ 1 → V x ≤ M1) :
      m * Real.exp (-M1) * unitBallVolume d ≤ ReferencePartition V b := by
    have hi := (reference_integrable_positive V b κ m L hκ hm hL hV hb hbound hquad).1
    have hc : IntegrableOn (fun _ : OneParticle d => m * Real.exp (-M1)) (Metric.ball 0 1) :=
      integrableOn_const (ne_of_lt (unitBallVolume_finite d))
    have hmon : (∫ _x in Metric.ball (0 : OneParticle d) 1, m * Real.exp (-M1)) ≤
        ∫ x in Metric.ball (0 : OneParticle d) 1, b x * Real.exp (-V x) := by
      apply setIntegral_mono_on hc hi.integrableOn Metric.isOpen_ball.measurableSet
      intro x hx
      have hnorm : ‖x‖ ≤ 1 := le_of_lt (by simpa using hx)
      apply mul_le_mul (hbound x).1
        (Real.exp_le_exp.mpr (neg_le_neg (hlocal x hnorm))) (Real.exp_pos _).le
      exact (hm.le.trans (hbound x).1)
    calc
      m * Real.exp (-M1) * unitBallVolume d =
          ∫ _x in Metric.ball (0 : OneParticle d) 1, m * Real.exp (-M1) := by
        rw [setIntegral_const, smul_eq_mul]
        dsimp [unitBallVolume]
        ring
      _ ≤ ∫ x in Metric.ball (0 : OneParticle d) 1, b x * Real.exp (-V x) := hmon
      _ ≤ ReferencePartition V b := by
        exact setIntegral_le_integral hi (Eventually.of_forall (fun x =>
          mul_nonneg (hm.le.trans (hbound x).1) (Real.exp_pos _).le))
  
  let commonDensityBound (d : ℕ) (L M1 : ℝ) : ℝ :=
    L * Real.exp M1 / unitBallVolume d
  
  have commonDensityBound_positive (d : ℕ) (L M1 : ℝ) (hL : 1 ≤ L) :
      0 < commonDensityBound d L M1 := by
    unfold commonDensityBound
    exact div_pos (mul_pos (by linarith) (Real.exp_pos _)) (unitBallVolume_positive d)
  
  have reference_density_gaussian_upper {d : ℕ} (V b : OneParticle d → ℝ)
      (κ m L M1 : ℝ) (hκ : 0 < κ) (hm : 0 < m) (hL : 1 ≤ L)
      (hV : Continuous V) (hb : Measurable b)
      (hbound : ∀ x, m ≤ b x ∧ b x ≤ L * m)
      (hquad : ∀ x, κ / 2 * ‖x‖ ^ 2 ≤ V x)
      (hlocal : ∀ x, ‖x‖ ≤ 1 → V x ≤ M1) (x : OneParticle d) :
      referenceDensity V b x ≤ commonDensityBound d L M1 * Real.exp (-(κ / 2) * ‖x‖ ^ 2) := by
    have hZm := reference_partition_lower V b κ m L M1 hκ hm hL hV hb hbound hquad hlocal
    have hden : 0 < m * Real.exp (-M1) * unitBallVolume d :=
      mul_pos (mul_pos hm (Real.exp_pos _)) (unitBallVolume_positive d)
    have hLm : 0 ≤ L * m := by nlinarith
    have hnum : b x * Real.exp (-V x) ≤ L * m * Real.exp (-(κ / 2) * ‖x‖ ^ 2) := by
      simpa only [neg_mul] using mul_le_mul (hbound x).2
        (Real.exp_le_exp.mpr (neg_le_neg (hquad x))) (Real.exp_pos _).le hLm
    have hratio := div_le_div₀ (mul_nonneg hLm (Real.exp_pos _).le) hnum hden hZm
    have heq : (L * m * Real.exp (-(κ / 2) * ‖x‖ ^ 2)) /
        (m * Real.exp (-M1) * unitBallVolume d) =
        commonDensityBound d L M1 * Real.exp (-(κ / 2) * ‖x‖ ^ 2) := by
      unfold commonDensityBound
      rw [Real.exp_neg]
      field_simp [ne_of_gt hm, ne_of_gt (unitBallVolume_positive d), Real.exp_ne_zero]
    rw [heq] at hratio
    simpa [referenceDensity, div_eq_mul_inv, mul_comm] using hratio
  
  have reference_density_local_lower {d : ℕ} (V b : OneParticle d → ℝ)
      (κ m L R MR : ℝ) (hκ : 0 < κ) (hm : 0 < m) (hL : 1 ≤ L)
      (hV : Continuous V) (hb : Measurable b)
      (hbound : ∀ x, m ≤ b x ∧ b x ≤ L * m)
      (hquad : ∀ x, κ / 2 * ‖x‖ ^ 2 ≤ V x)
      (hlocal : ∀ x, ‖x‖ ≤ R → V x ≤ MR) (x : OneParticle d) (hx : ‖x‖ ≤ R) :
      Real.exp (-MR) / (L * gaussianIntegral d κ) ≤ referenceDensity V b x := by
    have hZ := (reference_integrable_positive V b κ m L hκ hm hL hV hb hbound hquad).2
    have hZu := reference_partition_upper V b κ m L hκ hm hL hV hb hbound hquad
    have hbpos : 0 ≤ b x := hm.le.trans (hbound x).1
    have hnum : m * Real.exp (-MR) ≤ b x * Real.exp (-V x) :=
      mul_le_mul (hbound x).1 (Real.exp_le_exp.mpr (neg_le_neg (hlocal x hx)))
        (Real.exp_pos _).le hbpos
    have hratio := div_le_div₀ (mul_nonneg hbpos (Real.exp_pos _).le) hnum hZ hZu
    have hG : 0 < gaussianIntegral d κ := (GaussianConfinementIntegral (ι := Fin d) κ hκ).2.2
    have hLp : 0 < L := by linarith
    have heq : (m * Real.exp (-MR)) / (L * m * gaussianIntegral d κ) =
        Real.exp (-MR) / (L * gaussianIntegral d κ) := by
      field_simp [ne_of_gt hm, ne_of_gt hG, ne_of_gt hLp]
    rw [heq] at hratio
    simpa [referenceDensity, div_eq_mul_inv, mul_comm] using hratio
  
  have reference_density_global_upper {d : ℕ} (V b : OneParticle d → ℝ)
      (κ m L M1 : ℝ) (hκ : 0 < κ) (hm : 0 < m) (hL : 1 ≤ L)
      (hV : Continuous V) (hb : Measurable b)
      (hbound : ∀ x, m ≤ b x ∧ b x ≤ L * m)
      (hquad : ∀ x, κ / 2 * ‖x‖ ^ 2 ≤ V x)
      (hlocal : ∀ x, ‖x‖ ≤ 1 → V x ≤ M1) (x : OneParticle d) :
      referenceDensity V b x ≤ commonDensityBound d L M1 := by
    have h := reference_density_gaussian_upper V b κ m L M1 hκ hm hL hV hb hbound hquad hlocal x
    have hg : Real.exp (-(κ / 2) * ‖x‖ ^ 2) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith [sq_nonneg ‖x‖]
    have hmul := mul_le_mul_of_nonneg_left hg (commonDensityBound_positive d L M1 hL).le
    simpa using h.trans hmul
  
  have referenceLaw_common_volume_domination {d : ℕ} (V b : OneParticle d → ℝ)
      (κ m L M1 : ℝ) (hκ : 0 < κ) (hm : 0 < m) (hL : 1 ≤ L)
      (hV : Continuous V) (hb : Measurable b)
      (hbound : ∀ x, m ≤ b x ∧ b x ≤ L * m)
      (hquad : ∀ x, κ / 2 * ‖x‖ ^ 2 ≤ V x)
      (hlocal : ∀ x, ‖x‖ ≤ 1 → V x ≤ M1) :
      ReferenceLaw V b ≤ ENNReal.ofReal (commonDensityBound d L M1) • (volume : Measure (OneParticle d)) := by
    unfold ReferenceLaw
    rw [← withDensity_const]
    apply withDensity_mono
    exact Eventually.of_forall (fun x => ENNReal.ofReal_le_ofReal
      (reference_density_global_upper V b κ m L M1 hκ hm hL hV hb hbound hquad hlocal x))
  exact ⟨unitBallVolume_positive d,
    reference_partition_lower V b κ m L M1 hκ hm hL hV hb hbound hquad hlocal,
    reference_partition_upper V b κ m L hκ hm hL hV hb hbound hquad,
    reference_density_gaussian_upper V b κ m L M1 hκ hm hL hV hb hbound hquad hlocal,
    fun R MR hR x hx => reference_density_local_lower V b κ m L R MR
      hκ hm hL hV hb hbound hquad hR x hx,
    referenceLaw_common_volume_domination V b κ m L M1
      hκ hm hL hV hb hbound hquad hlocal⟩
