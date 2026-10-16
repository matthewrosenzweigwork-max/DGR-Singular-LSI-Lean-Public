module

public import Tablet.ConfigurationReference
public import Tablet.ParticlePosition
public import Tablet.RowFlattenVolumePreserving
public import Mathlib.Data.ENNReal.BigOperators

@[expose] public section
open MeasureTheory Set Filter
open scoped BigOperators

-- [TABLET NODE: ProductReferenceDensity]
theorem ProductReferenceDensity (d N : ℕ) (q : OneParticle d → ℝ)
    (hq : Measurable q) (hn : ∀ x, 0 ≤ q x) (hi : Integrable q volume)
    (hm : ∫ x, q x = 1) :
    ConfigurationReference d N
      ((volume : Measure (OneParticle d)).withDensity (fun x => ENNReal.ofReal (q x))) =
    (volume : Measure (ParticleConfig d N)).withDensity
      (fun X => ENNReal.ofReal (∏ i : Fin N, q (ParticlePosition X i))) := by
-- BODY
  classical
  let μ : Measure (OneParticle d) := volume.withDensity (fun x => ENNReal.ofReal (q x))
  let : IsProbabilityMeasure μ := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hn), hm]
    simp
  have hprod : Measure.pi (fun _ : Fin N => μ) =
      (volume : Measure (Fin N → OneParticle d)).withDensity
        (fun Y => ENNReal.ofReal (∏ i : Fin N, q (Y i))) := by
    have hwi : Integrable (fun Y : Fin N → OneParticle d => ∏ i : Fin N, q (Y i)) volume :=
      Integrable.fintype_prod (fun _ => hi)
    have hwn : ∀ Y : Fin N → OneParticle d, 0 ≤ ∏ i : Fin N, q (Y i) :=
      fun Y => Finset.prod_nonneg (fun i _ => hn (Y i))
    apply Measure.pi_eq
    intro S hS
    rw [withDensity_apply _ (MeasurableSet.univ_pi hS)]
    rw [← ofReal_integral_eq_lintegral_ofReal hwi.restrict (Eventually.of_forall hwn)]
    have hrestrict : (volume : Measure (Fin N → OneParticle d)).restrict (univ.pi S) =
        Measure.pi (fun i : Fin N => (volume : Measure (OneParticle d)).restrict (S i)) :=
      Measure.restrict_pi_pi (fun _ : Fin N => (volume : Measure (OneParticle d))) S
    rw [hrestrict, integral_fintype_prod_eq_prod]
    rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ => integral_nonneg hn)]
    apply Finset.prod_congr rfl
    intro i _
    rw [withDensity_apply _ (hS i)]
    exact ofReal_integral_eq_lintegral_ofReal hi.restrict (Eventually.of_forall hn)
  let F := fun Y : Fin N → OneParticle d =>
    WithLp.toLp 2 (fun ik : Fin N × Fin d => Y ik.1 ik.2)
  let r := fun X : ParticleConfig d N => ENNReal.ofReal (∏ i : Fin N, q (ParticlePosition X i))
  have hr : Measurable r := by
    apply Measurable.ennreal_ofReal
    apply Finset.measurable_prod
    intro i _
    have hp : Continuous (fun X : ParticleConfig d N => ParticlePosition X i) := by
      unfold ParticlePosition
      fun_prop
    exact hq.comp hp.measurable
  have hp : MeasurePreserving F (volume : Measure (Fin N → OneParticle d))
      (volume : Measure (ParticleConfig d N)) := RowFlattenVolumePreserving d N
  have hpd : MeasurePreserving F
      ((volume : Measure (Fin N → OneParticle d)).withDensity (r ∘ F))
      ((volume : Measure (ParticleConfig d N)).withDensity r) := by
    refine ⟨hp.measurable, ?_⟩
    ext S hS
    rw [Measure.map_apply hp.measurable hS, withDensity_apply _ (hp.measurable hS),
      withDensity_apply _ hS]
    exact hp.setLIntegral_comp_preimage hS hr
  have hid : r ∘ F = (fun Y : Fin N → OneParticle d => ENNReal.ofReal (∏ i : Fin N, q (Y i))) := by
    funext Y
    change ENNReal.ofReal (∏ i : Fin N, q (WithLp.toLp 2 (fun k => Y i k))) = _
    congr 1
  unfold ConfigurationReference
  rw [hprod, ← hid]
  exact hpd.map_eq
