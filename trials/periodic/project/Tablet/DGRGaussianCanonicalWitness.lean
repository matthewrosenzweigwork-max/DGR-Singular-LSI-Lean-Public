module

public import Tablet.DGRGaussianHighSeries
public import Tablet.ScaledBoundedCenteredCanonicalKernel
public import Tablet.CenteredDeletionEnergySum

@[expose] public section
open MeasureTheory Filter
open scoped BigOperators ComplexConjugate
-- [TABLET NODE: DGRGaussianCanonicalWitness]
theorem DGRGaussianCanonicalWitness (d N : ℕ) (hd : 2≤d) (hN : 2≤N)
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
    (∀ X, R X/(2*(N:ℝ))=2*t*CenteredPairEnergy V r X) := by
-- BODY
  have high_regularity (d : ℕ) (s a η M : ℝ)
    (hsd : s<(d:ℝ)) (ha : 0<a) (hη : 0<η)
    (K : Finset (Fin d→ℤ))
    (r : UnitAddTorus (Fin d)→ℝ) (hr : Measurable r)
    (hrb : ∀ᵐ x ∂volume,0≤r x ∧ r x≤M) (hrmass : ∫x,r x=1) :
    let V := fun x => DGRGaussianPhysicalLong d s a η x-
      ∑ k∈K,RieszMellinCoefficient d s a (η^2) 0 k*(UnitAddTorus.mFourier k x).re
    Continuous V ∧ (∀x,V (-x)=V x) ∧ Integrable (fun x => V x^2) volume ∧
    0≤V 0 ∧ (∀x,|V x|≤V 0+1) := by
    classical
    let c := RieszMellinCoefficient d s a (η^2) 0
    let low := fun x : UnitAddTorus (Fin d) => ∑ k∈K,c k*(UnitAddTorus.mFourier k x).re
    let V := fun x => DGRGaussianPhysicalLong d s a η x-low x
    have hδ : 0<η^2 := sq_pos_of_pos hη
    have hhigh := DGRGaussianHighSeries d s a η M hsd ha hη K r hr hrb hrmass
    dsimp only at hhigh
    rcases hhigh with ⟨hws,hwn,hwbound,hrep,hdiag,hcap⟩
    change ∀x,V x=∑'k,(if k∈K then 0 else c k)*(UnitAddTorus.mFourier k x).re at hrep
    change V 0=∑'k,if k∈K then 0 else c k at hdiag
    change ∀ N : ℕ, 1≤N → ∀ X : Configuration d N, -2*V 0≤CenteredPairEnergy V r X at hcap
    have hV0 : 0≤V 0 := by rw [hdiag]; exact tsum_nonneg hwn
    have hf := RieszMellinFourier d s a hsd ha (η^2) 0 hδ le_rfl
    have hlong := (DGRGaussianTruncationIdentification d s a η hη).2.1
    have hlc : Continuous low := continuous_finsetSum K (fun k _ => continuous_const.mul
      (Complex.continuous_re.comp (UnitAddTorus.mFourier k).continuous))
    have hVc : Continuous V := by
      dsimp [V]; rw [hlong]; exact hf.2.2.2.sub hlc
    have hV2 : Integrable (fun x => V x^2) volume :=
      (hVc.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hchar (k : Fin d→ℤ) (x : UnitAddTorus (Fin d)) :
        (UnitAddTorus.mFourier k (-x)).re=(UnitAddTorus.mFourier k x).re := by
      have hh : UnitAddTorus.mFourier k (-x)=conj (UnitAddTorus.mFourier k x) := by
        simp only [UnitAddTorus.mFourier,ContinuousMap.coe_mk,Pi.neg_apply,fourier_apply,
          smul_neg,fourier_neg',map_prod]
      rw [hh,Complex.conj_re]
    have hVe : ∀x,V (-x)=V x := by intro x; rw [hrep,hrep]; simp only [hchar]
    have hVb : ∀x,|V x|≤V 0+1 := by
      intro x
      have hcharbound (k : Fin d→ℤ) : |(UnitAddTorus.mFourier k x).re|≤1 := by
        apply (Complex.abs_re_le_norm _).trans_eq
        simp only [UnitAddTorus.mFourier,ContinuousMap.coe_mk,fourier_apply,norm_prod,
          Circle.norm_coe,Finset.prod_const_one]
      have hterm (k) : ‖(if k∈K then 0 else c k)*(UnitAddTorus.mFourier k x).re‖≤
          (if k∈K then 0 else c k) := by
        rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hwn k)]
        exact mul_le_of_le_one_right (hwn k) (hcharbound k)
      rw [hrep]
      have hb := norm_tsum_le_tsum_norm
        (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hws)
      have ht' := Summable.tsum_le_tsum (fun k => hterm k)
        (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hws) hws
      rw [Real.norm_eq_abs] at hb
      have hdg : (∑'k,if k∈K then 0 else c k)=V 0 := hdiag.symm
      rw [hdg] at ht'
      linarith
    exact ⟨hVc,hVe,hV2,hV0,hVb⟩

  classical
  let μ := volume.withDensity (fun x => ENNReal.ofReal (r x))
  let m := (a/Real.Gamma (((d:ℝ)-s)/2))*η^((d:ℝ)-s)/(((d:ℝ)-s)/2)
  let c := RieszMellinCoefficient d s a (η^2) 0
  let low := fun x : UnitAddTorus (Fin d) => ∑ k∈K,c k*(UnitAddTorus.mFourier k x).re
  let V := fun x => DGRGaussianPhysicalLong d s a η x-low x
  let q := fun x y => 2*t*CenteredKernel V r x y
  let R := fun X : Configuration d N => ∑ i,∑ j,if i=j then (0:ℝ) else q (X i) (X j)
  have hδ : 0<η^2 := sq_pos_of_pos hη
  obtain ⟨hVc,hVe,hV2,hV0,hVb⟩ := high_regularity d s a η M hsd ha hη K r hr hrb hrmass
  change Continuous V at hVc
  change ∀x,V (-x)=V x at hVe
  change Integrable (fun x => V x^2) volume at hV2
  change 0≤V 0 at hV0
  change ∀x,|V x|≤V 0+1 at hVb
  have hc := ScaledBoundedCenteredCanonicalKernel d N V r hVc.measurable hVe hr M (V 0+1) (∫z,V z^2) t hM (by linarith only [hV0]) ht hrb hrmass hVb hV2 le_rfl
  exact ⟨hVc,hVe,hV2,hV0,hc⟩
