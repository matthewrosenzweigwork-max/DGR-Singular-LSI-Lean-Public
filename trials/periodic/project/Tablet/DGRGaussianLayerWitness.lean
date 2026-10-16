import Tablet.DGRGaussianCanonicalWitness
import Tablet.DGRGaussianLayerM1M2
open MeasureTheory Filter
open scoped BigOperators ComplexConjugate
-- [TABLET NODE: DGRGaussianLayerWitness]
theorem DGRGaussianLayerWitness (d N : ℕ) (hd : 2≤d) (hN : 2≤N)
    (s a η M t : ℝ) (hs : 0≤s) (hsd : s<(d:ℝ)) (ha : 0<a)
    (hη : 0<η) (hη1 : η≤1) (hM : 1≤M) (ht : 0<t)
    (K : Finset (Fin d→ℤ))
    (r : UnitAddTorus (Fin d)→ℝ) (hr : Measurable r)
    (hrb : ∀ᵐ x ∂volume,0≤r x ∧ r x≤M) (hrmass : ∫x,r x=1) :
    let μ := volume.withDensity (fun x => ENNReal.ofReal (r x))
    let m := (a/Real.Gamma (((d:ℝ)-s)/2))*η^((d:ℝ)-s)/(((d:ℝ)-s)/2)
    let c := RieszMellinCoefficient d s a (η^2) 0
    let S := ∑ k∈K,c k
    let V := fun x => DGRGaussianPhysicalLong d s a η x-
      ∑ k∈K,c k*(UnitAddTorus.mFourier k x).re
    let q := fun x y => 2*t*CenteredKernel V r x y
    let R := fun X : Configuration d N =>
      ∑ i,∑ j,if i=j then (0:ℝ) else q (X i) (X j)
    Continuous V ∧ (∀x,V (-x)=V x) ∧ Integrable (fun x => V x^2) volume ∧
    0≤V 0 ∧
    Measurable (fun p : UnitAddTorus (Fin d)×UnitAddTorus (Fin d) => q p.1 p.2) ∧
    (∀x y,|q x y|≤8*t*(V 0+1)) ∧
    (∀x,∫y,q x y∂μ=0) ∧ (∀y,∫x,q x y∂μ=0) ∧
    (∀x,∫y,(q x y)^2∂μ≤64*t^2*M*(∫z,V z^2)) ∧
    (∀y,∫x,(q x y)^2∂μ≤64*t^2*M*(∫z,V z^2)) ∧
    (∀ X, R X/(2*(N:ℝ))=2*t*CenteredPairEnergy V r X) ∧
    (∀ X, -R X/(2*(N:ℝ))≤4*t*V 0) ∧
    (∀u:ℝ,0≤u → t*((N:ℝ)-1)*M*m≤u/8 → 2*t*S≤u/3 →
      ∀ᵐ X ∂Measure.pi (fun _:Fin N=>μ),
        u≤-t*CenteredPairEnergy (RieszKernel d s a 0) r X →
        u≤-R X/(2*(N:ℝ))) := by
-- BODY
  obtain ⟨hVc,hVe,hV2,hV0,hqm,hqb,hqr,hqc,hfr,hfc,hid⟩ := DGRGaussianCanonicalWitness d N hd hN s a η M t hs hsd ha hη hη1 hM ht K r hr hrb hrmass
  obtain ⟨_,hcap,hM1⟩ := DGRGaussianLayerM1M2 d N hd hN s a η M t hs hsd ha hη hη1 hM ht K r hr hrb hrmass
  exact ⟨hVc,hVe,hV2,hV0,hqm,hqb,hqr,hqc,hfr,hfc,hid,hcap,hM1⟩
