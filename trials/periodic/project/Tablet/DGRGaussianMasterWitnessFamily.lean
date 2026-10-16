module

public import Tablet.DGRGaussianLayerWitness
public import Tablet.DGRGaussianFixedM3Witness
public import Tablet.DGRGaussianMasterGrowth
public import Tablet.DGRPhysicalAdaptiveCutoff

@[expose] public section
open MeasureTheory
open scoped BigOperators
-- [TABLET NODE: DGRGaussianMasterWitnessFamily]
theorem DGRGaussianMasterWitnessFamily (d : ℕ) (hd : 2≤d) (s a M t L : ℝ)
    (hs : 0≤s) (hL : s<(d:ℝ)/2) (ha : 0<a) (hM : 1≤M) (ht : 0<t) (hLL : 1≤L) :
    ∃(κ : ℝ)(K : Finset (Fin d→ℤ))(U F D C : ℝ),
      1≤κ ∧ (∀k,k∈K↔(∑j,(k j:ℝ)^2)≤κ^2) ∧ (∀k,k∈K↔-k∈K) ∧
      1≤U ∧ 0<F ∧ 0<D ∧ F^2≤1/L ∧ D≤1/L ∧ 0<C ∧
      ∀N : ℕ,2≤N → ∀u : ℝ,U≤u → ∀r : UnitAddTorus (Fin d)→ℝ,Measurable r →
        (∀ᵐx∂volume,0≤r x ∧ r x≤M) → (∫x,r x=1) →
      let b := (a/Real.Gamma (((d:ℝ)-s)/2))/(((d:ℝ)-s)/2)
      let η := min 1 ((u/(8*t*(N:ℝ)*M*b))^(1/((d:ℝ)-s)))
      let V := fun x => DGRGaussianPhysicalLong d s a η x-
        ∑k∈K,RieszMellinCoefficient d s a (η^2) 0 k*(UnitAddTorus.mFourier k x).re
      let μ := volume.withDensity (fun x => ENNReal.ofReal (r x))
      let q := fun x y => 2*t*CenteredKernel V r x y
      let R := fun X : Configuration d N => ∑i,∑j,if i=j then (0:ℝ) else q (X i) (X j)
      0<8*t*(V 0+1) ∧ 0≤4*t*V 0 ∧
      Measurable (fun p : UnitAddTorus (Fin d)×UnitAddTorus (Fin d) => q p.1 p.2) ∧
      (∀x y,|q x y|≤8*t*(V 0+1)) ∧ (∀x,∫y,q x y∂μ=0) ∧ (∀y,∫x,q x y∂μ=0) ∧
      (∀x,∫y,(q x y)^2∂μ≤F^2) ∧ (∀y,∫x,(q x y)^2∂μ≤F^2) ∧
      (∫x,∫y,(q x y)^2∂μ∂μ)≤F^2 ∧
      Integrable (fun p : UnitAddTorus (Fin d)×UnitAddTorus (Fin d) => (q p.1 p.2)^2) (μ.prod μ) ∧
      (∀f g : UnitAddTorus (Fin d)→ℝ,Measurable f → Measurable g →
        ∀hf : MemLp f 2 μ,∀hg : MemLp g 2 μ,
        |∫x,∫y,q x y*f x*g y∂μ∂μ|≤D*‖hf.toLp f‖*‖hg.toLp g‖) ∧
      (∀X,R X/(2*(N:ℝ))=2*t*CenteredPairEnergy V r X) ∧
      (∀X,-R X/(2*(N:ℝ))≤4*t*V 0) ∧
      (∀ᵐX∂Measure.pi (fun _:Fin N=>μ),u≤-t*CenteredPairEnergy (RieszKernel d s a 0) r X →u≤-R X/(2*(N:ℝ))) ∧
      min u (4*t*V 0)*(1+8*t*(V 0+1))≤
        C*(if s=0 then (Real.log (Real.exp 1+(N:ℝ)))^2 else (N:ℝ)^(2*s/(d:ℝ))) := by
-- BODY
  obtain ⟨κ,K,F,D,hκ,hK,hKs,hF,hD,hFs,hDs,hfixed⟩ :=
    DGRGaussianFixedM3Witness d hd s a M t L hs hL ha hM ht hLL
  obtain ⟨C,hC,hgrowth⟩ := DGRGaussianMasterGrowth d hd s a M t hs hL ha hM ht
  let B := ∑k∈K,if k=0 then (0:ℝ) else a*(4*Real.pi^2*∑j,(k j:ℝ)^2)^(-((d:ℝ)-s)/2)
  let U := max 1 (6*t*B)
  have hU : 1≤U := le_max_left _ _
  refine ⟨κ,K,U,F,D,C,hκ,hK,hKs,hU,hF,hD,hFs,hDs,hC,?_⟩
  intro N hN u hu r hr hrb hrmass
  have hu1 : 1≤u := hU.trans hu
  have hdp : 0<(d:ℝ) := by exact_mod_cast (show 0<d by omega)
  have hsd : s<(d:ℝ) := by linarith
  let b := (a/Real.Gamma (((d:ℝ)-s)/2))/(((d:ℝ)-s)/2)
  let η := min 1 ((u/(8*t*(N:ℝ)*M*b))^(1/((d:ℝ)-s)))
  have hc := DGRPhysicalAdaptiveCutoff d N (by omega) s a M t 1 hsd ha hM ht (by norm_num) le_rfl K
  dsimp only at hc
  obtain ⟨hη,hη0,hη1,hnear,hlow⟩ := hc.2 u hu
  change 0<η at hη
  change η≤1 at hη1
  have hm : b*η^((d:ℝ)-s)=(a/Real.Gamma (((d:ℝ)-s)/2))*η^((d:ℝ)-s)/(((d:ℝ)-s)/2) := by
    dsimp [b]; ring
  change t*((N:ℝ)-1)*M*(b*η^((d:ℝ)-s))≤u/8 at hnear
  rw [hm] at hnear
  have hw := DGRGaussianLayerWitness d N hd hN s a η M t hs hsd ha hη hη1 hM ht K r hr hrb hrmass
  dsimp only at hw
  obtain ⟨hVc,hVe,hV2,hV0,hqm,hqb,hqr,hqc,_,_,hid,hcap,hM1⟩ := hw
  have hnorm := hfixed η hη hη1 r hr hrb hrmass
  dsimp only at hnorm
  obtain ⟨hfr,hfc,hHS,hqi,hop⟩ := hnorm
  have hM1' := hM1 u (zero_le_one.trans hu1) hnear hlow
  have hg := hgrowth N (by omega) u hu1 K
  dsimp only at hg
  dsimp only
  refine ⟨?_,?_,hqm,hqb,hqr,hqc,hfr,hfc,hHS,hqi,hop,hid,hcap,hM1',hg⟩
  · positivity
  · positivity
