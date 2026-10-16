module

public import Tablet.DGRGaussianCoarsenedEndpointPartition
public import Tablet.ProbabilityExponentialInterpolation
public import Tablet.RieszCenteredHeatPartitionComparison
public import Tablet.ProductDensityMeasureIdentity
public import Tablet.CenteredPartitionFinite

@[expose] public section
open MeasureTheory
-- [TABLET NODE: RieszCenteredPartitionUniform]
theorem RieszCenteredPartitionUniform (d:ℕ)(hd:2≤d)(s a:ℝ)
    (hs:0≤s)(hL:s<(d:ℝ)/2)(ha:0<a)(T M:ℝ)(hT:0≤T)(hM:1≤M) :
    ∃K:ℝ,1≤K ∧ ∀N:ℕ,2≤N→∀t ε:ℝ,0≤t→t≤T→0≤ε→
      ∀r:UnitAddTorus (Fin d)→ℝ,Measurable r→
      (∀ᵐx∂(volume:Measure (UnitAddTorus (Fin d))),0≤r x∧r x≤M)→(∫x,r x)=1→
      Integrable (fun X:Configuration d N=>
        Real.exp (-t*CenteredPairEnergy (RieszKernel d s a ε) r X)*ProductDensity r X) volume ∧
      1≤CenteredPartition (N:=N) (RieszKernel d s a ε) r t ∧
      CenteredPartition (N:=N) (RieszKernel d s a ε) r t≤K := by
-- BODY
  have productReferenceIntegral (n : ℕ) (v : UnitAddTorus (Fin d)→ℝ)
      (hv : Measurable v) (hvn : ∀ᵐx∂(volume : Measure (UnitAddTorus (Fin d))),0≤v x)
      (hvi : Integrable v volume) (hvmass : ∫x,v x∂volume=1)
      (F : Configuration d n→ℝ) :
      (∫X,F X∂Measure.pi (fun _:Fin n=>(volume : Measure (UnitAddTorus (Fin d))).withDensity (fun x=>ENNReal.ofReal (v x))))=
        ∫X,F X*ProductDensity v X∂volume := by
    exact (ProductDensityMeasureIdentity d n v hv hvn hvi hvmass).2 F
  have hsd : s<(d:ℝ) := by
    have hdp : 0<(d:ℝ) := by exact_mod_cast (show 0<d by omega)
    linarith
  obtain ⟨C,hC,hendpoint⟩ := DGRGaussianCoarsenedEndpointPartition d hd s a M (T+1) hs hL ha hM (by linarith)
  refine ⟨C,hC,?_⟩
  intro N hN t ε ht htT hε r hr hrb hrmass
  obtain ⟨c,hc,hg⟩ := RieszL1Foundation d hd s a hs hsd ha
  obtain ⟨hgm,hgi,_,_,hgl,_,_⟩ := hg ε hε
  have hfinite := CenteredPartitionFinite d N hN (RieszKernel d s a ε) r hgm hgi hr M c hM hc hrb hrmass hgl t ht
  refine ⟨hfinite.1,hfinite.2.1,?_⟩
  let rε := if ε=0 then r else HeatSemigroup d (ε/2) r
  have hh := RieszCenteredHeatPartitionComparison d N hd s a ε t M hs hsd ha hε ht hM r hr hrb hrmass
  dsimp only at hh
  obtain ⟨hrε,hriε,hrbε,hrmassε,hheat⟩ := hh
  have he := hendpoint N hN rε hrε hrbε hrmassε
  dsimp only at he
  let μ := volume.withDensity (fun x => ENNReal.ofReal (rε x))
  let ν := Measure.pi (fun _:Fin N=>μ)
  haveI : IsProbabilityMeasure μ := by
    apply isProbabilityMeasure_iff.mpr
    rw [withDensity_apply _ MeasurableSet.univ]
    simp only [Measure.restrict_univ]
    rw [←ofReal_integral_eq_lintegral_ofReal hriε (hrbε.mono fun _ hx => hx.1), hrmassε]
    simp
  haveI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  obtain ⟨hgm0,hgi0,_,_,hgl0,_,_⟩ := hg 0 le_rfl
  have hEm := (CenteredProductMean d N (RieszKernel d s a 0) rε hgm0 hgi0 hrε M c hM hc hrbε hrmassε hgl0).1
  have hi := ProbabilityExponentialInterpolation ν (CenteredPairEnergy (N:=N) (RieszKernel d s a 0) rε)
    hEm (T+1) C (by linarith) hC he.1 he.2 t ht (by linarith)
  have hid := productReferenceIntegral N rε hrε (hrbε.mono fun _ hx => hx.1) hriε hrmassε
    (fun X => Real.exp (-t*CenteredPairEnergy (RieszKernel d s a 0) rε X))
  calc
    CenteredPartition (N:=N) (RieszKernel d s a ε) r t≤CenteredPartition (N:=N) (RieszKernel d s a 0) rε t := hheat
    _≤C := by rw [CenteredPartition, ←hid]; exact hi.2
