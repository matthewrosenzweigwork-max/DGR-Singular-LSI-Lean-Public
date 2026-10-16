import Tablet.ProductBackgroundFacts
import Tablet.TiltNormalization
import Mathlib.Data.ENNReal.BigOperators
open MeasureTheory
-- [TABLET NODE: ProductBackgroundMeasureIdentity]
theorem ProductBackgroundMeasureIdentity (d N : ℕ) (l u : ℝ)
    (q : BoundedBackground d l u) :
    Measure.pi (fun _ : Fin N => (volume : Measure (UnitAddTorus (Fin d))).withDensity
      (fun x => ENNReal.ofReal (q.density x))) =
    (volume : Measure (Configuration d N)).withDensity
      (fun X => ENNReal.ofReal (ProductDensity q.density X)) := by
-- BODY
  classical
  let m : Measure (UnitAddTorus (Fin d)) := volume
  let ν : Measure (UnitAddTorus (Fin d)) := m.withDensity fun x => ENNReal.ofReal (q.density x)
  have hqn : 0 ≤ᵐ[m] q.density := q.bounds.mono fun x hx => q.lower_pos.le.trans hx.1
  have hqi : Integrable q.density m := integrable_of_integral_eq_one q.mass
  have htilt := (TiltNormalization m q.density q.measurable hqn hqi
    (by rw [q.mass]; norm_num)).1
  have heq : NormalizedTilt m q.density = ν := by
    dsimp [NormalizedTilt, ν, m]
    rw [q.mass]
    simp only [div_one]
  letI : IsProbabilityMeasure ν := heq ▸ htilt
  have hp := ProductBackgroundFacts d N l u q
  have hpn : 0 ≤ᵐ[(volume : Measure (Configuration d N))] ProductDensity q.density :=
    hp.2.2.2.mono fun X hx => (pow_nonneg q.lower_pos.le N).trans hx.1
  apply Measure.pi_eq
  intro S hS
  rw [withDensity_apply _ (MeasurableSet.univ_pi hS)]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (hp.2.1.mono_measure Measure.restrict_le_self) (ae_restrict_of_ae hpn)]
  have hrestrict : (volume : Measure (Configuration d N)).restrict (Set.univ.pi S) =
      Measure.pi (fun i => m.restrict (S i)) := by
    exact Measure.restrict_pi_pi (fun _ : Fin N => m) S
  rw [hrestrict]
  simp only [ProductDensity]
  rw [integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg_of_ae (ae_restrict_of_ae hqn))]
  apply Finset.prod_congr rfl
  intro i _
  rw [withDensity_apply _ (hS i)]
  exact ofReal_integral_eq_lintegral_ofReal
    (hqi.mono_measure Measure.restrict_le_self) (ae_restrict_of_ae hqn)
