module

public import Tablet.QuadraticGaussianClass
public import Tablet.ConvexReferenceNormalization
public import Tablet.GaussianConfinementIntegral
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Data.ENNReal.BigOperators

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter Metric
open scoped ContDiff ENNReal NNReal
open ProbabilityTheory
noncomputable section

-- [TABLET NODE: QuadraticGaussianReference]
theorem QuadraticGaussianReference (d : ℕ) :
    let V : OneParticle d → ℝ := fun x => ‖x‖^2/2
    ReferencePartition V (fun _ => 1) = Real.sqrt (2*Real.pi)^d ∧
    ReferenceLaw V (fun _ => 1) = ProbabilityTheory.stdGaussian (OneParticle d) ∧
    (∀ (L : ℝ) (b : OneParticle d → ℝ), BoundedMultiplier d L b →
      Integrable (fun x => b x*Real.exp (-V x)) ∧ 0 < ReferencePartition V b ∧
      IsProbabilityMeasure (ReferenceLaw V b)) := by
-- BODY
  let V : OneParticle d → ℝ := fun x => ‖x‖^2/2
  obtain ⟨hreg,hgrad,hhess,hlap,htwo,hzero,hmin,hclass⟩ := QuadraticGaussianClass d 0
  have hpartition : ReferencePartition V (fun _ => 1) = Real.sqrt (2*Real.pi)^d := by
    have hexp : (fun x : OneParticle d => Real.exp (-V x)) = fun x => Real.exp (-(1/2:ℝ)*‖x‖^2) := by
      funext x
      congr 1
      dsimp only [V]
      ring
    unfold ReferencePartition
    simp only [one_mul]
    rw [hexp]
    simpa only [div_one,Fintype.card_fin] using (GaussianConfinementIntegral (ι := Fin d) 1 zero_lt_one).1
  have hdensity : ReferenceLaw V (fun _ => 1) =
      volume.withDensity (fun x : OneParticle d => ENNReal.ofReal (Real.exp (-‖x‖^2/2)/Real.sqrt (2*Real.pi)^d)) := by
    unfold ReferenceLaw
    rw [hpartition]
    congr 1
    funext x
    congr 1
    dsimp only [V]
    ring_nf
  have gaussianPotential_exp_factor (x : OneParticle d) :
      Real.exp (-‖x‖ ^ 2 / 2) = ∏ i : Fin d, Real.exp (-(1 / 2 : ℝ) * (x i) ^ 2) := by
    rw [EuclideanSpace.real_norm_sq_eq, ← Real.exp_sum]
    congr 1
    rw [← Finset.mul_sum]
    ring
  have gaussianPotential_normalizedPDF_factor (x : OneParticle d) :
      Real.exp (-‖x‖ ^ 2 / 2) / Real.sqrt (2 * Real.pi) ^ d =
        ∏ i : Fin d, gaussianPDFReal 0 1 (x i) := by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [gaussianPotential_exp_factor]
    simp only [inv_pow, div_eq_mul_inv]
    rw [mul_comm]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    congr 1
    ring
  have hreferencePDF : ReferenceLaw V (fun _ => 1) =
      volume.withDensity (fun x : OneParticle d => ENNReal.ofReal (∏ i : Fin d, gaussianPDFReal 0 1 (x i))) := by
    rw [hdensity]
    congr 1
    funext x
    rw [gaussianPotential_normalizedPDF_factor]
  have finiteProductStandardGaussianDensity :
      Measure.pi (fun _ : Fin d => gaussianReal 0 1) =
        (volume : Measure (Fin d → ℝ)).withDensity
          (fun Y => ENNReal.ofReal (∏ i : Fin d, gaussianPDFReal 0 1 (Y i))) := by
    let q : ℝ → ℝ := gaussianPDFReal 0 1
    have hqi : Integrable q volume := integrable_gaussianPDFReal _ _
    have hqn : ∀ x, 0 ≤ q x := gaussianPDFReal_nonneg _ _
    have hwi : Integrable (fun Y : Fin d → ℝ => ∏ i : Fin d, q (Y i)) volume :=
      Integrable.fintype_prod (fun _ => hqi)
    have hwn : ∀ Y : Fin d → ℝ, 0 ≤ ∏ i : Fin d, q (Y i) :=
      fun Y => Finset.prod_nonneg (fun i _ => hqn (Y i))
    apply Measure.pi_eq
    intro S hS
    rw [withDensity_apply _ (MeasurableSet.univ_pi hS)]
    rw [← ofReal_integral_eq_lintegral_ofReal hwi.restrict (Eventually.of_forall hwn)]
    have hrestrict : (volume : Measure (Fin d → ℝ)).restrict (univ.pi S) =
        Measure.pi (fun i : Fin d => (volume : Measure ℝ).restrict (S i)) :=
      Measure.restrict_pi_pi (fun _ : Fin d => (volume : Measure ℝ)) S
    rw [hrestrict, integral_fintype_prod_eq_prod]
    rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ => integral_nonneg hqn)]
    apply Finset.prod_congr rfl
    intro i _
    rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0),
      withDensity_apply _ (hS i)]
    exact ofReal_integral_eq_lintegral_ofReal hqi.restrict (Eventually.of_forall hqn)
  have measurableEquiv_density_map
      (e : (Fin d → ℝ) ≃ᵐ OneParticle d) (μ : Measure (Fin d → ℝ)) (w : (Fin d → ℝ) → ℝ≥0∞) :
      (μ.withDensity w).map e = (μ.map e).withDensity (fun y => w (e.symm y)) := by
    apply Measure.ext
    intro S hS
    rw [Measure.map_apply e.measurable hS, withDensity_apply _ (e.measurable hS),
      withDensity_apply _ hS]
    rw [← lintegral_indicator (e.measurable hS), ← lintegral_indicator hS,
      lintegral_map_equiv]
    apply lintegral_congr
    intro x
    by_cases hx : e x ∈ S <;> simp [hx]
  have hstandard : ReferenceLaw V (fun _ => 1) = stdGaussian (OneParticle d) := by
    rw [← map_pi_eq_stdGaussian, finiteProductStandardGaussianDensity]
    rw [show (WithLp.toLp 2 : (Fin d → ℝ) → OneParticle d) =
      MeasurableEquiv.toLp 2 (Fin d → ℝ) from rfl, measurableEquiv_density_map]
    have hmap : (volume : Measure (Fin d → ℝ)).map (MeasurableEquiv.toLp 2 (Fin d → ℝ)) =
        (volume : Measure (OneParticle d)) := by
      simpa using (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).symm.map_eq
    rw [hmap]
    exact hreferencePDF
  refine ⟨hpartition,hstandard,?_⟩
  intro L b hb
  exact ConvexReferenceNormalization V b 1 L zero_lt_one htwo.toPotentialBounds hb
