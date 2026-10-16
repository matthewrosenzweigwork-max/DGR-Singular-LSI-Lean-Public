module

public import Tablet.DGRGaussianCenteredTruncation
public import Tablet.DGRGaussianHighSeries
public import Tablet.RieszMellinLowCenteredEnergyBound
public import Tablet.CenteredDeletionEnergySum

@[expose] public section
open MeasureTheory Filter
open scoped BigOperators ComplexConjugate
-- [TABLET NODE: DGRGaussianLayerM1M2]
theorem DGRGaussianLayerM1M2 (d N : ℕ) (hd : 2≤d) (hN : 2≤N)
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
    (∀ X, R X/(2*(N:ℝ))=2*t*CenteredPairEnergy V r X) ∧
    (∀ X, -R X/(2*(N:ℝ))≤4*t*V 0) ∧
    (∀u:ℝ,0≤u → t*((N:ℝ)-1)*M*m≤u/8 → 2*t*S≤u/3 →
      ∀ᵐ X ∂Measure.pi (fun _:Fin N=>μ),
        u≤-t*CenteredPairEnergy (RieszKernel d s a 0) r X →
        u≤-R X/(2*(N:ℝ))) := by
-- BODY
  have ordered_count {d N:ℕ} (g r:UnitAddTorus (Fin d)→ℝ)
    (hg:∀z,g (-z)=g z)(X:Configuration d N):
    CenteredPairEnergy g r X=
      ((∑i:Fin N,∑j:Fin N,if i=j then (0:ℝ) else CenteredKernel g r (X i) (X j))/(N:ℝ))/2 := by
    have h:=(CenteredDeletionEnergySum g r hg X 1).1
    have hi (i j:Fin N):
        (if j≠i then CenteredKernel g r (X i) (X j) else 0)=
        (if i=j then (0:ℝ) else CenteredKernel g r (X i) (X j)) := by
      by_cases he:i=j
      · subst j; simp
      · simp [he,Ne.symm he]
    simp_rw [hi,←Finset.mul_sum] at h
    simp only [one_div] at h
    simp only [div_eq_mul_inv]
    norm_num at h ⊢
    nlinarith only [h]

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
  have hlc : Continuous low := continuous_finsetSum K (fun k _ => continuous_const.mul
    (Complex.continuous_re.comp (UnitAddTorus.mFourier k).continuous))
  have hcap := (DGRGaussianHighSeries d s a η M hsd ha hη K r hr hrb hrmass).2.2.2.2.2
  change ∀ N : ℕ, 1≤N → ∀ X : Configuration d N, -2*V 0≤CenteredPairEnergy V r X at hcap
  have hid (X : Configuration d N) : R X/(2*(N:ℝ))=2*t*CenteredPairEnergy V r X := by
    have hterm (i j : Fin N) : (if i=j then (0:ℝ) else q (X i) (X j))=
      2*t*(if i=j then 0 else CenteredKernel V r (X i) (X j)) := by
      dsimp [q]; split_ifs <;> ring
    dsimp [R]
    simp_rw [hterm,← Finset.mul_sum]
    rw [ordered_count V r hVe X]
    ring
  have hbcap (X : Configuration d N) : -R X/(2*(N:ℝ))≤4*t*V 0 := by
    have hb := hcap N (by omega) X
    have hh := mul_le_mul_of_nonneg_left hb (show 0≤2*t by positivity)
    rw [neg_div, hid]
    nlinarith only [hh]
  refine ⟨hid,hbcap,?_⟩
  · intro u hu hnearbudget hlowbudget
    have hn := DGRGaussianCenteredTruncation d hd s a η M hs hsd ha hη hη1 hM r hr hrb hrmass
    dsimp only at hn
    obtain ⟨hGm,hGi,hGn,hGmass,hGpot,hGmean,hLm,hLi,hLmass,_,_,_,_,henergies⟩ := hn
    obtain ⟨hnearcap,hlongcap,hdecomp⟩ := henergies N (by omega)
    have hVi : Integrable V volume := hVc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hlowi : Integrable low volume := hlc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hsplit : DGRGaussianPhysicalLong d s a η =ᵐ[volume] fun x => low x+V x-0 :=
      Eventually.of_forall fun x => by dsimp [V]; ring
    have hdecompL := (CenteredPairEnergyAEDecomposition d N (DGRGaussianPhysicalLong d s a η)
      low V r hLm hlc.measurable hVc.measurable hLi hlowi hVi hr M 0
      (zero_le_one.trans hM) hrb hrmass hsplit).2.2.2
    have hlowcap := (RieszMellinLowCenteredEnergyBound d s a hsd ha (η^2) 0 hδ le_rfl
      K M r hr hrb hrmass).1 N (by omega)
    filter_upwards [hdecomp,hdecompL] with X hEg hEL
    intro hXi
    change CenteredPairEnergy (RieszKernel d s a 0) r X=_ at hEg
    change CenteredPairEnergy (DGRGaussianPhysicalLong d s a η) r X=_ at hEL
    have hGn := mul_le_mul_of_nonneg_left (hnearcap X) ht.le
    have hLn := mul_le_mul_of_nonneg_left (hlowcap X) ht.le
    change t*(-((N:ℝ)-1)*M*m)≤t*CenteredPairEnergy (DGRGaussianPhysicalNear d s a η) r X at hGn
    change t*((N:ℝ)-1)*M*m≤u/8 at hnearbudget
    rw [neg_div,hid]
    change 2*t*(∑k∈K,c k)≤u/3 at hlowbudget
    change t*(-2*(∑k∈K,c k))≤t*CenteredPairEnergy low r X at hLn
    rw [hEg,hEL] at hXi
    nlinarith only [hXi,hGn,hLn,hnearbudget,hlowbudget,hu]
