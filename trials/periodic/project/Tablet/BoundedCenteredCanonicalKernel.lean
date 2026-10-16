import Tablet.CenteredKernelSquareBounds
import Tablet.CenteredDeletionEnergySum
open MeasureTheory
-- [TABLET NODE: BoundedCenteredCanonicalKernel]
theorem BoundedCenteredCanonicalKernel (d : ℕ) (g r : UnitAddTorus (Fin d) → ℝ)
    (hg : Measurable g) (heven : ∀z,g (-z)=g z)
    (hr : Measurable r) (M A η : ℝ) (hM : 1≤M) (hA : 0<A)
    (hrb : ∀ᵐx ∂(volume : Measure (UnitAddTorus (Fin d))),0≤r x ∧ r x≤M)
    (hrmass : ∫x,r x ∂volume=1) (hgb : ∀x,|g x|≤A)
    (hg2 : Integrable (fun x=>(g x)^2) volume) (hη : (∫x,(g x)^2 ∂volume)≤η) :
    let μ : Measure (UnitAddTorus (Fin d)) := volume.withDensity (fun x=>ENNReal.ofReal (r x))
    let q := CenteredKernel g r
    Measurable (fun v : UnitAddTorus (Fin d) × UnitAddTorus (Fin d)=>q v.1 v.2) ∧ (∀x y,|q x y|≤4*A) ∧
    (∀x,∫y,q x y ∂μ=0) ∧ (∀y,∫x,q x y ∂μ=0) ∧
    (∀x,∫y,(q x y)^2 ∂μ≤16*M*η) ∧ (∀y,∫x,(q x y)^2 ∂μ≤16*M*η) := by
-- BODY
  have hpot_integral (v w : UnitAddTorus (Fin d)→ℝ) :
      BackgroundPotential v w = fun x => ∫y,v (x-y)*w y := by
    funext x
    unfold BackgroundPotential convolution
    change (∫y,w y*v (x-y)) = ∫y,v (x-y)*w y
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => mul_comm _ _)
  haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1:ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp; infer_instance
  haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := inferInstance
  let μ : Measure (UnitAddTorus (Fin d)) := volume.withDensity (fun x=>ENNReal.ofReal (r x))
  have hgi : Integrable g volume := Integrable.of_bound hg.aestronglyMeasurable A
    (Filter.Eventually.of_forall fun x=>by simpa only [Real.norm_eq_abs] using hgb x)
  have hgl : ∀x,-A≤g x := fun x=>(abs_le.mp (hgb x)).1
  obtain ⟨hpm,hpf,hpri,hJ,hqm,hqmean,hql⟩ :=
    CenteredKernelBounds d g r hg hgi hr M A hM hA.le hrb hrmass hgl
  have hrn := hrb.mono fun x hx=>hx.1
  have hrnorm : ∀ᵐx ∂(volume : Measure (UnitAddTorus (Fin d))),‖r x‖≤M :=
    hrb.mono fun x hx=>by simpa [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2
  have hri : Integrable r volume := Integrable.of_bound hr.aestronglyMeasurable M hrnorm
  have intμ (f : UnitAddTorus (Fin d)→ℝ) : (∫x,f x ∂μ)=∫x,f x*r x ∂volume := by
    rw [integral_withDensity_eq_integral_toReal_smul hr.ennreal_ofReal
      (Filter.Eventually.of_forall fun _=>ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards [hrn] with x hx
    change (ENNReal.ofReal (r x)).toReal*f x=f x*r x
    rw [ENNReal.toReal_ofReal hx,mul_comm]
  have hpA (x : UnitAddTorus (Fin d)) : |BackgroundPotential g r x|≤A := by
    calc
      _ ≤ ∫y,‖g (x-y)*r y‖ ∂volume := by
        simpa only [hpot_integral,Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y=>g (x-y)*r y)
      _ ≤ ∫y,A*r y ∂volume := by
        apply integral_mono_ae (hpf x).1.norm (hri.const_mul A)
        filter_upwards [hrb] with y hy
        rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hy.1]
        exact mul_le_mul_of_nonneg_right (hgb _) hy.1
      _ = A := by rw [integral_const_mul,hrmass,mul_one]
  have hJA : |BackgroundPairMean g r|≤A := by
    calc
      _ ≤ ∫x,‖BackgroundPotential g r x*r x‖ ∂volume := by
        simpa only [BackgroundPairMean,Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x=>BackgroundPotential g r x*r x)
      _ ≤ ∫x,A*r x ∂volume := by
        apply integral_mono_ae hpri.norm (hri.const_mul A)
        filter_upwards [hrb] with x hx
        rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hx.1]
        exact mul_le_mul_of_nonneg_right (hpA x) hx.1
      _ = A := by rw [integral_const_mul,hrmass,mul_one]
  have hsym (x y : UnitAddTorus (Fin d)) : CenteredKernel g r y x=CenteredKernel g r x y := by
    have hh:=heven (x-y)
    rw [neg_sub] at hh
    unfold CenteredKernel
    rw [hh]; ring
  have hsq := (CenteredKernelSquareBounds d g r hg hgi hg2 hr M A hM hA.le hrb hrmass hgl).2.2
  refine ⟨hqm,?_,?_,?_,?_,?_⟩
  · intro x y
    have ha1:=norm_sub_le (g (x-y)) (BackgroundPotential g r x)
    have ha2:=norm_sub_le (g (x-y)-BackgroundPotential g r x) (BackgroundPotential g r y)
    have ha3:=abs_add_le (g (x-y)-BackgroundPotential g r x-BackgroundPotential g r y) (BackgroundPairMean g r)
    simp only [Real.norm_eq_abs] at ha1 ha2
    unfold CenteredKernel
    linarith [hgb (x-y),hpA x,hpA y,hJA]
  · intro x
    rw [intμ]
    exact (hqmean x).2
  · intro y
    have he : (fun x=>CenteredKernel g r x y)=(fun x=>CenteredKernel g r y x) := by
      funext x; exact hsym y x
    rw [he,intμ]
    exact (hqmean y).2
  · intro x
    rw [intμ]
    exact (hsq x).2.trans (by nlinarith [mul_le_mul_of_nonneg_left hη (show 0≤16*M by positivity)])
  · intro y
    have he : (fun x=>(CenteredKernel g r x y)^2)=(fun x=>(CenteredKernel g r y x)^2) := by
      funext x; rw [hsym y x]
    rw [he,intμ]
    exact (hsq y).2.trans (by nlinarith [mul_le_mul_of_nonneg_left hη (show 0≤16*M by positivity)])
