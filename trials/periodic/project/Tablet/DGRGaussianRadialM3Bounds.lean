module

public import Tablet.DGRGaussianRadialFiberBounds
public import Tablet.DGRGaussianRadialOperatorBound

@[expose] public section
open MeasureTheory Filter
open scoped BigOperators
-- [TABLET NODE: DGRGaussianRadialM3Bounds]
theorem DGRGaussianRadialM3Bounds (d : ℕ) (hd : 2≤d) (s a M t : ℝ)
    (hs : 0≤s) (hL : s<(d:ℝ)/2) (ha : 0<a) (hM : 1≤M) (ht : 0<t) :
    ∃CF CD : ℝ,0<CF ∧ 0<CD ∧ ∀κ : ℝ,1≤κ →
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
      Integrable (fun p : UnitAddTorus (Fin d)×UnitAddTorus (Fin d) => (q p.1 p.2)^2) (μ.prod μ) ∧
      (∀f g : UnitAddTorus (Fin d)→ℝ,Measurable f → Measurable g →
        ∀hf : MemLp f 2 μ,∀hg : MemLp g 2 μ,
        |∫x,∫y,q x y*f x*g y∂μ∂μ|≤CD*κ^(s-(d:ℝ))*‖hf.toLp f‖*‖hg.toLp g‖) := by
-- BODY
  obtain ⟨CF,hCF,hfiber⟩ := DGRGaussianRadialFiberBounds d hd s a M t hs hL ha hM ht
  obtain ⟨CD,hCD,hop⟩ := DGRGaussianRadialOperatorBound d hd s a M t hs hL ha hM ht
  refine ⟨CF,CD,hCF,hCD,?_⟩
  intro κ hκ K hK η hη hη1 r hr hrb hrmass
  obtain ⟨hrow,hcol,hHS,hqi⟩ := hfiber κ hκ K hK η hη hη1 r hr hrb hrmass
  exact ⟨hrow,hcol,hHS,hqi,hop κ hκ K hK η hη hη1 r hr hrb hrmass⟩
