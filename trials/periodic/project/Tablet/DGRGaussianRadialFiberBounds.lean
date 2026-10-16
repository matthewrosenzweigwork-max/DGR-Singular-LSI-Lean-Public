import Tablet.DGRGaussianCanonicalWitness
import Tablet.RieszMellinRadialCenteredFiberBound
import Tablet.ProbabilityBoundedKernelSquare
open MeasureTheory Filter
open scoped BigOperators
-- [TABLET NODE: DGRGaussianRadialFiberBounds]
theorem DGRGaussianRadialFiberBounds (d : ℕ) (hd : 2≤d) (s a M t : ℝ)
    (hs : 0≤s) (hL : s<(d:ℝ)/2) (ha : 0<a) (hM : 1≤M) (ht : 0<t) :
    ∃CF : ℝ,0<CF ∧ ∀κ : ℝ,1≤κ →
      ∀K : Finset (Fin d→ℤ),(∀k,k∈K↔(∑j,(k j:ℝ)^2)≤κ^2) →
      ∀η : ℝ,0<η → η≤1 → ∀r : UnitAddTorus (Fin d)→ℝ,Measurable r →
        (∀ᵐx∂volume,0≤r x ∧ r x≤M) → (∫x,r x=1) →
      let V := fun x => DGRGaussianPhysicalLong d s a η x-
        ∑k∈K,RieszMellinCoefficient d s a (η^2) 0 k*(UnitAddTorus.mFourier k x).re
      let μ := volume.withDensity (fun x => ENNReal.ofReal (r x))
      let q := fun x y => 2*t*CenteredKernel V r x y
      (∀x,∫y,(q x y)^2∂μ≤CF*κ^(2*s-(d:ℝ))) ∧
      (∀y,∫x,(q x y)^2∂μ≤CF*κ^(2*s-(d:ℝ))) ∧
      (∫x,∫y,(q x y)^2∂μ∂μ)≤CF*κ^(2*s-(d:ℝ)) ∧
      Integrable (fun p : UnitAddTorus (Fin d)×UnitAddTorus (Fin d) => (q p.1 p.2)^2) (μ.prod μ) := by
-- BODY
  have hdp : 0<(d:ℝ) := by exact_mod_cast (show 0<d by omega)
  have hsd : s<(d:ℝ) := by linarith
  obtain ⟨CF,hCF,hfiber⟩ := RieszMellinRadialCenteredFiberBound d s a hL ha
  refine ⟨4*t^2*M*CF,by positivity,?_⟩
  intro κ hκ K hK η hη hη1 r hr hrb hrmass
  let μ := volume.withDensity (fun x => ENNReal.ofReal (r x))
  let V := fun x => DGRGaussianPhysicalLong d s a η x-
    ∑k∈K,RieszMellinCoefficient d s a (η^2) 0 k*(UnitAddTorus.mFourier k x).re
  let q := fun x y => 2*t*CenteredKernel V r x y
  have hδ : 0<η^2 := sq_pos_of_pos hη
  have hlong := (DGRGaussianTruncationIdentification d s a η hη).2.1
  have htail := hfiber (η^2) 0 κ hδ le_rfl hκ K hK r hr M hM hrb hrmass
  dsimp only at htail
  rw [←hlong] at htail
  change Integrable (fun x => V x^2) volume ∧ (∫x,V x^2)≤_ ∧
    (∀x,∫y,(CenteredKernel V r x y)^2∂μ≤_) ∧ (∀y,∫x,(CenteredKernel V r x y)^2∂μ≤_) at htail
  have hrow (x) : (∫y,(q x y)^2∂μ)≤4*t^2*M*CF*κ^(2*s-(d:ℝ)) := by
    change (∫y,(2*t*CenteredKernel V r x y)^2∂μ)≤_
    simp_rw [mul_pow]
    rw [integral_const_mul]
    have hh := mul_le_mul_of_nonneg_left (htail.2.2.1 x) (sq_nonneg (2*t))
    nlinarith only [hh]
  have hcol (y) : (∫x,(q x y)^2∂μ)≤4*t^2*M*CF*κ^(2*s-(d:ℝ)) := by
    change (∫x,(2*t*CenteredKernel V r x y)^2∂μ)≤_
    simp_rw [mul_pow]
    rw [integral_const_mul]
    have hh := mul_le_mul_of_nonneg_left (htail.2.2.2 y) (sq_nonneg (2*t))
    nlinarith only [hh]
  haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1:ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp; infer_instance
  haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := inferInstance
  have hri : Integrable r volume := Integrable.of_bound hr.aestronglyMeasurable M
    (hrb.mono fun x hx => by simpa only [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2)
  haveI : IsProbabilityMeasure μ := by
    apply isProbabilityMeasure_iff.mpr
    rw [withDensity_apply _ MeasurableSet.univ]
    simp only [Measure.restrict_univ]
    rw [←ofReal_integral_eq_lintegral_ofReal hri (hrb.mono fun _ hx => hx.1), hrmass]
    simp
  have hcan := DGRGaussianCanonicalWitness d 2 hd le_rfl s a η M t hs hsd ha hη hη1 hM ht K r hr hrb hrmass
  dsimp only at hcan
  obtain ⟨hVc,hVe,hV2,hV0,hqm,hqb,_⟩ := hcan
  change Measurable (fun p : UnitAddTorus (Fin d)×UnitAddTorus (Fin d) => q p.1 p.2) at hqm
  change ∀x y : UnitAddTorus (Fin d),|q x y|≤8*t*(V 0+1) at hqb
  obtain ⟨hHS,hqi⟩ := ProbabilityBoundedKernelSquare μ q (8*t*(V 0+1))
    (4*t^2*M*CF*κ^(2*s-(d:ℝ))) hqm hqb hrow
  exact ⟨hrow,hcol,hHS,hqi⟩
