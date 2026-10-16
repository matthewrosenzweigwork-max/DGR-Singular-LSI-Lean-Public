import Tablet.SummableGramCentering
import Tablet.Preamble
import Tablet.CenteredPairEnergy
open MeasureTheory
open scoped ComplexConjugate
-- [TABLET NODE: TorusSummableGramCenteredEnergy]
theorem TorusSummableGramCenteredEnergy (d : ℕ) (g r : UnitAddTorus (Fin d) → ℝ)
    (hr : Measurable r) (hrn : ∀ᵐx∂volume, 0 ≤ r x) (hri : Integrable r volume)
    (hrmass : ∫x, r x∂volume = 1) (w : (Fin d → ℤ) → ℝ)
    (hw : ∀k, 0 ≤ w k) (hws : Summable w)
    (hg : ∀x, g x = ∑'k, w k * (UnitAddTorus.mFourier k x).re) :
    ∀N : ℕ, 1 ≤ N → ∀X : Configuration d N,
      -2 * (∑'k, w k) ≤ CenteredPairEnergy g r X := by
-- BODY
  have hpot_integral (v w : UnitAddTorus (Fin d)→ℝ) :
      BackgroundPotential v w = fun x => ∫y,v (x-y)*w y := by
    funext x
    unfold BackgroundPotential convolution
    change (∫y,w y*v (x-y)) = ∫y,v (x-y)*w y
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => mul_comm _ _)
  classical
  let μ : Measure (UnitAddTorus (Fin d)) := volume.withDensity (fun x => ENNReal.ofReal (r x))
  haveI : IsProbabilityMeasure μ := by
    apply isProbabilityMeasure_iff.mpr
    rw [withDensity_apply _ MeasurableSet.univ]
    simp only [Measure.restrict_univ]
    rw [←ofReal_integral_eq_lintegral_ofReal hri hrn, hrmass]
    simp
  have hint (F : UnitAddTorus (Fin d) → ℝ) : (∫x, F x∂μ) = ∫x, F x * r x∂volume := by
    have hdf : ∀ᵐx∂(volume : Measure (UnitAddTorus (Fin d))), ENNReal.ofReal (r x) < ⊤ :=
      Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
    rw [integral_withDensity_eq_integral_toReal_smul hr.ennreal_ofReal hdf]
    apply integral_congr_ae
    filter_upwards [hrn] with x hx
    change (ENNReal.ofReal (r x)).toReal * F x = F x * r x
    rw [ENNReal.toReal_ofReal hx, mul_comm]
  have hchar (k : Fin d → ℤ) (x y : UnitAddTorus (Fin d)) :
      UnitAddTorus.mFourier k (x-y) = UnitAddTorus.mFourier k x * conj (UnitAddTorus.mFourier k y) := by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_apply,
      Pi.add_apply, Pi.neg_apply, zsmul_add, zsmul_neg, sub_eq_add_neg,
      AddCircle.toCircle_add, AddCircle.toCircle_neg, Circle.coe_mul,
      Circle.coe_inv_eq_conj, map_prod, Finset.prod_mul_distrib]
  have hfb (k : Fin d → ℤ) (x : UnitAddTorus (Fin d)) : ‖UnitAddTorus.mFourier k x‖ ≤ 1 := by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_apply,
      norm_prod, Circle.norm_coe, Finset.prod_const_one, le_refl]
  let G : UnitAddTorus (Fin d) → UnitAddTorus (Fin d) → ℝ :=
    fun x y => ∑'k, w k * (UnitAddTorus.mFourier k x * conj (UnitAddTorus.mFourier k y)).re
  have hG (x y : UnitAddTorus (Fin d)) : g (x-y) = G x y := by
    rw [hg]
    exact tsum_congr fun k => by rw [hchar]
  have hrow (x : UnitAddTorus (Fin d)) : BackgroundPotential g r x = ∫y, G x y∂μ := by
    rw [hint]
    simp only [hpot_integral]
    simp_rw [hG]
  have hmean : BackgroundPairMean g r = ∫x, ∫y, G x y∂μ∂μ := by
    rw [hint]
    unfold BackgroundPairMean
    simp_rw [hrow]
  have hc (x y : UnitAddTorus (Fin d)) : CenteredKernel g r x y =
      G x y - (∫z, G x z∂μ) - (∫z, G y z∂μ) + (∫z,∫z',G z z'∂μ∂μ) := by
    unfold CenteredKernel
    rw [hG, hrow, hrow, hmean]
  have hGram := SummableGramCentering μ w (fun k x => UnitAddTorus.mFourier k x)
    hw hws (fun k => (UnitAddTorus.mFourier k).continuous.measurable) hfb
  intro N hN X
  unfold CenteredPairEnergy
  simp_rw [hc]
  exact hGram.2.2 N hN X
