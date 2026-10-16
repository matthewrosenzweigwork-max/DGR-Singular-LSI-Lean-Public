module

public import Tablet.DGRGaussianRadialM3Bounds
public import Tablet.DGRRadialTailTolerance
public import Tablet.RadialFrequencyCutoff

@[expose] public section
open MeasureTheory
open scoped BigOperators
-- [TABLET NODE: DGRGaussianFixedM3Witness]
theorem DGRGaussianFixedM3Witness (d : ℕ) (hd : 2≤d) (s a M t L : ℝ)
    (hs : 0≤s) (hL : s<(d:ℝ)/2) (ha : 0<a) (hM : 1≤M) (ht : 0<t) (hLL : 1≤L) :
    ∃(κ : ℝ)(K : Finset (Fin d→ℤ))(F D : ℝ),
      1≤κ ∧ (∀k,k∈K↔(∑j,(k j:ℝ)^2)≤κ^2) ∧ (∀k,k∈K↔-k∈K) ∧
      0<F ∧ 0<D ∧ F^2≤1/L ∧ D≤1/L ∧
      ∀η : ℝ,0<η → η≤1 → ∀r : UnitAddTorus (Fin d)→ℝ,Measurable r →
        (∀ᵐx∂volume,0≤r x ∧ r x≤M) → (∫x,r x=1) →
      let V := fun x => DGRGaussianPhysicalLong d s a η x-
        ∑k∈K,RieszMellinCoefficient d s a (η^2) 0 k*(UnitAddTorus.mFourier k x).re
      let μ := volume.withDensity (fun x => ENNReal.ofReal (r x))
      let q := fun x y => 2*t*CenteredKernel V r x y
      (∀x,∫y,(q x y)^2∂μ≤F^2) ∧ (∀y,∫x,(q x y)^2∂μ≤F^2) ∧
      (∫x,∫y,(q x y)^2∂μ∂μ)≤F^2 ∧
      Integrable (fun p : UnitAddTorus (Fin d)×UnitAddTorus (Fin d) => (q p.1 p.2)^2) (μ.prod μ) ∧
      (∀f g : UnitAddTorus (Fin d)→ℝ,Measurable f → Measurable g →
        ∀hf : MemLp f 2 μ,∀hg : MemLp g 2 μ,
        |∫x,∫y,q x y*f x*g y∂μ∂μ|≤D*‖hf.toLp f‖*‖hg.toLp g‖) := by
-- BODY
  obtain ⟨CF,CD,hCF,hCD,hbounds⟩ := DGRGaussianRadialM3Bounds d hd s a M t hs hL ha hM ht
  have hdp : 0<(d:ℝ) := by exact_mod_cast (show 0<d by omega)
  have hp : 0<(d:ℝ)-2*s := by linarith
  have hq : 0<(d:ℝ)-s := by linarith
  obtain ⟨κ,hκ,hCp,hDp,hCs,hDs⟩ := DGRRadialTailTolerance ((d:ℝ)-2*s) ((d:ℝ)-s) CF CD L hp hq hCF hCD hLL
  rw [show -((d:ℝ)-2*s)=2*s-(d:ℝ) by ring] at hCp hCs
  rw [show -((d:ℝ)-s)=s-(d:ℝ) by ring] at hDp hDs
  obtain ⟨K,hK,hKs,hK0,hKcard⟩ := RadialFrequencyCutoff d κ hκ
  let F := Real.sqrt (CF*κ^(2*s-(d:ℝ)))
  let D := CD*κ^(s-(d:ℝ))
  have hF : 0<F := Real.sqrt_pos.mpr hCp
  have hFsq : F^2=CF*κ^(2*s-(d:ℝ)) := Real.sq_sqrt hCp.le
  refine ⟨κ,K,F,D,hκ,hK,hKs,hF,hDp,?_,hDs,?_⟩
  · rw [hFsq]; exact hCs
  · intro η hη hη1 r hr hrb hrmass
    have hh := hbounds κ hκ K hK η hη hη1 r hr hrb hrmass
    rw [←hFsq] at hh
    exact hh
