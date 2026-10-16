module

public import Tablet.ReferenceLaw

@[expose] public section

-- [TABLET NODE: ReferenceLawProbability]
theorem ReferenceLawProbability {d : ℕ} (V b : OneParticle d → ℝ)
    (hi : MeasureTheory.Integrable (fun x => b x * Real.exp (-V x)))
    (hnonneg : ∀ x, 0 ≤ b x) (hZ : 0 < ReferencePartition V b) :
    MeasureTheory.IsProbabilityMeasure (ReferenceLaw V b) := by
-- BODY
  constructor
  unfold ReferenceLaw
  rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ, MeasureTheory.Measure.restrict_univ]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
  · rw [MeasureTheory.integral_const_mul]
    change ENNReal.ofReal ((ReferencePartition V b)⁻¹ * ReferencePartition V b) = 1
    simp [ne_of_gt hZ]
  · exact hi.const_mul _
  · exact Filter.Eventually.of_forall (fun x =>
      mul_nonneg (inv_nonneg.mpr hZ.le) (mul_nonneg (hnonneg x) (Real.exp_pos _).le))
