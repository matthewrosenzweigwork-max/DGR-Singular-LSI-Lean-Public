import Tablet.DGRGaussianMasterWitnessFamily
import Tablet.DGRMasterGrowthEventually
import Tablet.DGRGaussianFiniteMasterCap
import Tablet.DGRCanonicalFiberMaster
import Tablet.CenteredProductMean
import Tablet.Preamble
open MeasureTheory
open scoped BigOperators
-- [TABLET NODE: DGRGaussianCoarsenedEndpointPartition]
theorem DGRGaussianCoarsenedEndpointPartition (d : ℕ) (hd : 2≤d) (s a M T : ℝ)
    (hs : 0≤s) (hL : s<(d:ℝ)/2) (ha : 0<a) (hM : 1≤M) (hT : 0<T) :
    ∃C : ℝ,1≤C ∧ ∀N : ℕ,2≤N → ∀r : UnitAddTorus (Fin d)→ℝ,Measurable r →
      (∀ᵐx∂volume,0≤r x ∧ r x≤M) → (∫x,r x=1) →
      let μ := volume.withDensity (fun x => ENNReal.ofReal (r x))
      let ν := Measure.pi (fun _:Fin N=>μ)
      Integrable (fun X : Configuration d N => Real.exp (-T*CenteredPairEnergy (RieszKernel d s a 0) r X)) ν ∧
      (∫X : Configuration d N,Real.exp (-T*CenteredPairEnergy (RieszKernel d s a 0) r X)∂ν)≤C := by
-- BODY
  classical
  obtain ⟨L,hLL,hmaster⟩ := DGRCanonicalFiberMaster.{0}
  have hLp : 0<L := zero_lt_one.trans_le hLL
  have hLL2 : 1≤L^2 := by nlinarith
  obtain ⟨κ,K,U,F,D,Cg,_,_,_,hU,hF,_,hFs,_,hCg,hfamily⟩ :=
    DGRGaussianMasterWitnessFamily d hd s a M T (L^2) hs hL ha hM hT hLL2
  have hFsmall : F≤1/L := by
    have heq : 1/(L^2)=(1/L)^2 := by field_simp
    rw [heq] at hFs
    exact (sq_le_sq₀ hF.le (one_div_pos.mpr hLp).le).mp hFs
  obtain ⟨N₀,hN₀,heventual⟩ := DGRMasterGrowthEventually d hd s (2*L^2*Cg) hs hL (by positivity)
  have hsd : s<(d:ℝ) := by
    have hdp : 0<(d:ℝ) := by exact_mod_cast (show 0<d by omega)
    linarith
  obtain ⟨Cf,hCf,hfinite⟩ := DGRGaussianFiniteMasterCap d hd s a M T hs hsd ha hM hT.le N₀
  refine ⟨max Cf (Real.exp U+L),hCf.trans (le_max_left _ _),?_⟩
  intro N hN r hr hrb hrmass
  dsimp only
  by_cases hlarge : N₀≤N
  · let μ := volume.withDensity (fun x => ENNReal.ofReal (r x))
    let ν := Measure.pi (fun _:Fin N=>μ)
    let Xi := fun X : Configuration d N => -T*CenteredPairEnergy (RieszKernel d s a 0) r X
    let b := (a/Real.Gamma (((d:ℝ)-s)/2))/(((d:ℝ)-s)/2)
    let η := fun u : ℝ => min 1 ((u/(8*T*(N:ℝ)*M*b))^(1/((d:ℝ)-s)))
    let V := fun u x => DGRGaussianPhysicalLong d s a (η u) x-
      ∑k∈K,RieszMellinCoefficient d s a ((η u)^2) 0 k*(UnitAddTorus.mFourier k x).re
    let q := fun u x y => 2*T*CenteredKernel (V u) r x y
    let A := fun u => 8*T*(V u 0+1)
    let m := fun u => 4*T*V u 0
    have hri : Integrable r volume := Integrable.of_bound hr.aestronglyMeasurable M (by
      filter_upwards [hrb] with x hx
      simpa only [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2)
    haveI : IsProbabilityMeasure μ := by
      apply isProbabilityMeasure_iff.mpr
      rw [withDensity_apply _ MeasurableSet.univ]
      simp only [Measure.restrict_univ]
      rw [←ofReal_integral_eq_lintegral_ofReal hri (hrb.mono fun _ hx => hx.1), hrmass]
      simp
    obtain ⟨c,hc,hg⟩ := RieszL1Foundation d hd s a hs hsd ha
    obtain ⟨hgm,hgi,_,_,hgl,_,_⟩ := hg 0 le_rfl
    have hEm := (CenteredProductMean d N (RieszKernel d s a 0) r hgm hgi hr M c hM hc hrb hrmass hgl).1
    have hXi : Measurable Xi := measurable_const.mul hEm
    have hcan : ∀u,U≤u → 0<A u ∧
        Measurable (fun p : UnitAddTorus (Fin d)×UnitAddTorus (Fin d) => q u p.1 p.2) ∧
        (∀x y,|q u x y|≤A u) ∧ (∀x,∫y,q u x y∂μ=0) ∧
        (∀y,∫x,q u x y∂μ=0) ∧ (∀x,∫y,(q u x y)^2∂μ≤F^2) ∧
        (∀y,∫x,(q u x y)^2∂μ≤F^2) := by
      intro u hu
      have hw := hfamily N hN u hu r hr hrb hrmass
      dsimp only at hw
      exact ⟨hw.1,hw.2.2.1,hw.2.2.2.1,hw.2.2.2.2.1,hw.2.2.2.2.2.1,hw.2.2.2.2.2.2.1,hw.2.2.2.2.2.2.2.1⟩
    have hM1 : ∀u,U≤u → ∀ᵐX∂ν,u≤Xi X →
        u≤-(∑i,∑j,if i=j then (0:ℝ) else q u (X i) (X j))/(2*(N:ℝ)) := by
      intro u hu
      have hw := hfamily N hN u hu r hr hrb hrmass
      dsimp only at hw
      exact hw.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hM2 : ∀u,U≤u → ∀ᵐX∂ν,
        -(∑i,∑j,if i=j then (0:ℝ) else q u (X i) (X j))/(2*(N:ℝ))≤m u := by
      intro u hu
      have hw := hfamily N hN u hu r hr hrb hrmass
      dsimp only at hw
      exact Filter.Eventually.of_forall hw.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hgrowth : ∀u,U≤u → 2*L^2*min u (m u)*(1+A u)≤(N:ℝ) := by
      intro u hu
      have hw := hfamily N hN u hu r hr hrb hrmass
      dsimp only at hw
      have hbound := hw.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      change min u (m u)*(1+A u)≤Cg*(if s=0 then (Real.log (Real.exp 1+(N:ℝ)))^2 else (N:ℝ)^(2*s/(d:ℝ))) at hbound
      have hh := mul_le_mul_of_nonneg_left hbound (show 0≤2*L^2 by positivity)
      have he := heventual N hlarge
      calc
        2*L^2*min u (m u)*(1+A u)=2*L^2*(min u (m u)*(1+A u)) := by ring
        _≤2*L^2*(Cg*(if s=0 then (Real.log (Real.exp 1+(N:ℝ)))^2 else (N:ℝ)^(2*s/(d:ℝ)))) := hh
        _≤(N:ℝ) := by convert he using 1 <;> ring
    have hm := hmaster μ N (by omega) Xi hXi q A m F U hU hF hFsmall hcan hM1 hM2 hgrowth
    exact ⟨hm.2.2.1,hm.2.2.2.trans (le_max_right _ _)⟩
  · have hf := hfinite N hN (by omega) r hr hrb hrmass
    exact ⟨hf.1,hf.2.trans (le_max_left _ _)⟩
