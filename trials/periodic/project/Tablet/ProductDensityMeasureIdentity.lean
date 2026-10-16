import Tablet.ProductDensity
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.MeasureTheory.Integral.Pi
open MeasureTheory
-- [TABLET NODE: ProductDensityMeasureIdentity]
theorem ProductDensityMeasureIdentity (d N : ℕ) (r : UnitAddTorus (Fin d)→ℝ)
    (hr : Measurable r) (hrn : ∀ᵐx∂(volume : Measure (UnitAddTorus (Fin d))),0≤r x)
    (hri : Integrable r volume) (hrmass : ∫x,r x∂volume=1) :
    Measure.pi (fun _:Fin N=>(volume : Measure (UnitAddTorus (Fin d))).withDensity (fun x=>ENNReal.ofReal (r x)))=
      (volume : Measure (Configuration d N)).withDensity (fun X=>ENNReal.ofReal (ProductDensity r X)) ∧
    ∀F:Configuration d N→ℝ,
      (∫X,F X∂Measure.pi (fun _:Fin N=>(volume : Measure (UnitAddTorus (Fin d))).withDensity (fun x=>ENNReal.ofReal (r x))))=
        ∫X,F X*ProductDensity r X∂volume := by
-- BODY
  have hlaw : Measure.pi (fun _:Fin N=>(volume : Measure (UnitAddTorus (Fin d))).withDensity (fun x=>ENNReal.ofReal (r x)))=
      (volume : Measure (Configuration d N)).withDensity (fun X=>ENNReal.ofReal (ProductDensity r X)) := by
    classical
    haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=by
      rw [AddCircle.volume_eq_smul_haarAddCircle];simp;infer_instance
    haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) :=inferInstance
    let m:Measure (UnitAddTorus (Fin d)):=volume
    let ν:=m.withDensity (fun x=>ENNReal.ofReal (r x))
    haveI : IsProbabilityMeasure ν :=by
      apply isProbabilityMeasure_iff.mpr
      rw [withDensity_apply _ MeasurableSet.univ]
      simp only [Measure.restrict_univ]
      rw [←ofReal_integral_eq_lintegral_ofReal hri hrn,hrmass]
      simp
    have hwi : Integrable (ProductDensity (N:=N) r) volume :=Integrable.fintype_prod (fun _:Fin N=>hri)
    have hcoords:∀ᵐX∂(volume : Measure (Configuration d N)),∀i:Fin N,0≤r (X i) :=by
      rw [ae_all_iff]
      intro i
      exact (measurePreserving_eval (fun _:Fin N=>m) i).quasiMeasurePreserving.tendsto_ae hrn
    have hwn:∀ᵐX∂(volume : Measure (Configuration d N)),0≤ProductDensity r X :=
      hcoords.mono fun X hX=>Finset.prod_nonneg (fun i _=>hX i)
    apply Measure.pi_eq
    intro S hS
    rw [withDensity_apply _ (MeasurableSet.univ_pi hS)]
    rw [←ofReal_integral_eq_lintegral_ofReal (hwi.mono_measure Measure.restrict_le_self) (ae_restrict_of_ae hwn)]
    have hrestrict : (volume : Measure (Configuration d N)).restrict (Set.univ.pi S)=Measure.pi (fun i=>m.restrict (S i)) :=
      Measure.restrict_pi_pi (fun _:Fin N=>m) S
    rw [hrestrict]
    simp only [ProductDensity]
    rw [integral_fintype_prod_eq_prod]
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _=>integral_nonneg_of_ae (ae_restrict_of_ae hrn))]
    apply Finset.prod_congr rfl
    intro i _
    rw [withDensity_apply _ (hS i)]
    exact ofReal_integral_eq_lintegral_ofReal (hri.mono_measure Measure.restrict_le_self) (ae_restrict_of_ae hrn)
  refine ⟨hlaw,?_⟩
  classical
  haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=by
    rw [AddCircle.volume_eq_smul_haarAddCircle];simp;infer_instance
  haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) :=inferInstance
  have hwm:Measurable (ProductDensity (N:=N) r):=Finset.measurable_prod _ (fun i _=>hr.comp (measurable_pi_apply i))
  have hcoords:∀ᵐX∂(volume : Measure (Configuration d N)),∀i:Fin N,0≤r (X i) :=by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval (fun _:Fin N=>(volume : Measure (UnitAddTorus (Fin d)))) i).quasiMeasurePreserving.tendsto_ae hrn
  have hwn:∀ᵐX∂(volume : Measure (Configuration d N)),0≤ProductDensity r X :=
    hcoords.mono fun X hX=>Finset.prod_nonneg (fun i _=>hX i)
  have hdf:∀ᵐX∂(volume : Measure (Configuration d N)),ENNReal.ofReal (ProductDensity r X)<⊤ :=
    Filter.Eventually.of_forall fun _=>ENNReal.ofReal_lt_top
  intro F
  rw [hlaw,
    integral_withDensity_eq_integral_toReal_smul hwm.ennreal_ofReal hdf]
  apply integral_congr_ae
  filter_upwards [hwn] with X hX
  change (ENNReal.ofReal (ProductDensity r X)).toReal*F X=F X*ProductDensity r X
  rw [ENNReal.toReal_ofReal hX,mul_comm]
