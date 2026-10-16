module

public import Tablet.ConfigurationTranslationGeometry
public import Tablet.ReferenceTranslation
public import Tablet.ConvexReferenceNormalization
public import Tablet.GibbsLaw
public import Tablet.LawVariance
public import Tablet.PhysicalEnergy
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Dynamics.Ergodic.MeasurePreserving

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped ContDiff ENNReal
noncomputable section

-- [TABLET NODE: ConfigurationLawTranslation]
theorem ConfigurationLawTranslation {d N : ℕ} (V b : OneParticle d → ℝ)
    (κ L : ℝ) (hκ : 0 < κ) (hV : PotentialBounds d κ V)
    (hb : BoundedMultiplier d L b) (a : OneParticle d) (s coupling ε : ℝ) :
    let μ := ReferenceLaw V b
    let μc := ReferenceLaw (ShiftedReference V b a).1 (ShiftedReference V b a).2
    let e := (ConfigurationTranslation (N := N) a).toMeasurableEquiv
    (ConfigurationReference d N μ).map e = ConfigurationReference d N μc ∧
    GibbsPartition (N := N) μc s coupling ε = GibbsPartition (N := N) μ s coupling ε ∧
    (GibbsLaw (N := N) μ s coupling ε).map e = GibbsLaw (N := N) μc s coupling ε ∧
    (∀ f : ParticleConfig d N → ℝ, LawVariance (GibbsLaw (N := N) μc s coupling ε) f =
      LawVariance (GibbsLaw (N := N) μ s coupling ε) (fun X => f (e X))) ∧
    (∀ f : ParticleConfig d N → ℝ, PhysicalEnergy (GibbsLaw (N := N) μc s coupling ε) f =
      PhysicalEnergy (GibbsLaw (N := N) μ s coupling ε) (fun X => f (e X))) := by
-- BODY
  let μ := ReferenceLaw V b
  let e := (ConfigurationTranslation (N := N) a).toMeasurableEquiv
  let oneShift (a : OneParticle d) : OneParticle d ≃ᵐ OneParticle d := MeasurableEquiv.addRight (-a)
  letI : IsProbabilityMeasure μ := (ConvexReferenceNormalization V b κ L hκ hV hb).2.2
  have interactionWeight_shift (a : OneParticle d) (s coupling ε : ℝ) (X : ParticleConfig d N) :
      InteractionWeight s coupling ε ((ConfigurationTranslation a).toMeasurableEquiv X) = InteractionWeight s coupling ε X :=
    (ConfigurationTranslationGeometry a s coupling ε).2.2.1 X
  have measurableEquiv_density_map
      (e : ParticleConfig d N ≃ᵐ ParticleConfig d N) (μ : Measure (ParticleConfig d N)) (w : ParticleConfig d N → ℝ≥0∞) :
      (μ.withDensity w).map e = (μ.map e).withDensity (fun y => w (e.symm y)) := by
    apply Measure.ext
    intro S hS
    rw [Measure.map_apply e.measurable hS, withDensity_apply _ (e.measurable hS), withDensity_apply _ hS]
    rw [← lintegral_indicator (e.measurable hS), ← lintegral_indicator hS]
    rw [lintegral_map_equiv]
    apply lintegral_congr
    intro x
    by_cases hx : e x ∈ S <;> simp [Set.indicator_apply, hx]
  have measurableEquiv_integral_map
      (e : ParticleConfig d N ≃ᵐ ParticleConfig d N) (μ : Measure (ParticleConfig d N)) (f : ParticleConfig d N → ℝ) :
      (∫ y, f y ∂μ.map e) = ∫ x, f (e x) ∂μ :=
    e.measurableEmbedding.integral_map f
  have flatten_shift_commutes (a : OneParticle d) (Y : Fin N → OneParticle d) :
      (WithLp.toLp 2 (fun ik : Fin N × Fin d => oneShift a (Y ik.1) ik.2) : ParticleConfig d N) =
        (ConfigurationTranslation a).toMeasurableEquiv (WithLp.toLp 2 (fun ik : Fin N × Fin d => Y ik.1 ik.2)) := by
    apply PiLp.ext
    intro ik
    rfl
  have configurationReference_shift (a : OneParticle d)
      (μ : Measure (OneParticle d)) [IsProbabilityMeasure μ] :
      (ConfigurationReference d N μ).map ((ConfigurationTranslation a).toMeasurableEquiv) =
        ConfigurationReference d N (μ.map (oneShift a)) := by
    letI : IsProbabilityMeasure (μ.map (oneShift a)) :=
      Measure.isProbabilityMeasure_map (oneShift a).measurable.aemeasurable
    unfold ConfigurationReference
    rw [← Measure.pi_map_pi (fun _ : Fin N => (oneShift a).measurable.aemeasurable)]
    have hF : Measurable (fun Y : Fin N → OneParticle d =>
        (WithLp.toLp 2 (fun ik : Fin N × Fin d => Y ik.1 ik.2) : ParticleConfig d N)) := by fun_prop
    have hR : Measurable (fun Y : Fin N → OneParticle d => fun i => oneShift a (Y i)) := by fun_prop
    rw [Measure.map_map ((ConfigurationTranslation a).toMeasurableEquiv).measurable hF, Measure.map_map hF hR]
    congr 1
  have gibbsPartition_shift (a : OneParticle d)
      (μ : Measure (OneParticle d)) [IsProbabilityMeasure μ] (s coupling ε : ℝ) :
      GibbsPartition (N := N) (μ.map (oneShift a)) s coupling ε = GibbsPartition (N := N) μ s coupling ε := by
    unfold GibbsPartition
    rw [← configurationReference_shift a μ, measurableEquiv_integral_map]
    simp only [interactionWeight_shift]
  have gibbsLaw_shift (a : OneParticle d)
      (μ : Measure (OneParticle d)) [IsProbabilityMeasure μ] (s coupling ε : ℝ) :
      (GibbsLaw (N := N) μ s coupling ε).map ((ConfigurationTranslation a).toMeasurableEquiv) =
        GibbsLaw (N := N) (μ.map (oneShift a)) s coupling ε := by
    unfold GibbsLaw
    rw [measurableEquiv_density_map, configurationReference_shift, gibbsPartition_shift]
    congr 1
    funext X
    have h := interactionWeight_shift a s coupling ε (((ConfigurationTranslation a).toMeasurableEquiv).symm X)
    simpa only [MeasurableEquiv.apply_symm_apply] using congrArg
      (fun w => ENNReal.ofReal ((GibbsPartition (N := N) μ s coupling ε)⁻¹ * w)) h.symm
  have hRef : μ.map (oneShift a) = ReferenceLaw (ShiftedReference V b a).1 (ShiftedReference V b a).2 :=
    (ReferenceTranslation V b a).2
  have hConfig := configurationReference_shift a μ
  have hPart := gibbsPartition_shift a μ s coupling ε
  have hLaw := gibbsLaw_shift a μ s coupling ε
  rw [hRef] at hConfig hPart hLaw
  refine ⟨hConfig, hPart, hLaw, ?_, ?_⟩
  · intro f
    rw [← hLaw]
    exact ProbabilityTheory.variance_map_equiv f e
  · intro f
    rw [← hLaw]
    unfold PhysicalEnergy
    rw [measurableEquiv_integral_map]
    apply integral_congr_ae
    exact Eventually.of_forall (fun X => by
      change ‖EuclideanGradient f (ConfigurationTranslation a X)‖ ^ 2 =
        ‖EuclideanGradient (fun Y => f (ConfigurationTranslation a Y)) X‖ ^ 2
      rw [(ConfigurationTranslationGeometry a s coupling ε).2.2.2.1 f X])
