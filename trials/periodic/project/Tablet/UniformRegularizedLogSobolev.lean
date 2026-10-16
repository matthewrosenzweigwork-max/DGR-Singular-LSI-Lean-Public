import Tablet.UniformLogSobolevFromPartitionBounds
import Tablet.RieszCenteredPartitionUniform
open MeasureTheory
-- [TABLET NODE: UniformRegularizedLogSobolev]
theorem UniformRegularizedLogSobolev (d:ℕ)(hd:2≤d)(s a B l u:ℝ)
    (hs:0≤s)(hsd:s≤(d:ℝ)-2)(hL:s<(d:ℝ)/2)(ha:0<a)(hB:0≤B)
    (hl:0<l)(hl1:l≤1)(hu:1≤u) :
    ∃rate:ℝ,0<rate ∧∀N:ℕ,2≤N→∀β:ℝ,0≤β→β≤B→
      ∀q:BoundedBackground d l u,∀ε:ℝ,0<ε→∀f:Configuration d N→ℝ,f∈SmoothCore d N→
        Entropy (CanonicalLaw (N:=N) (RieszKernel d s a ε) q.density β) (fun X=>f X^2)
        ≤(2/rate)*PhysicalEnergy (CanonicalLaw (N:=N) (RieszKernel d s a ε) q.density β) f := by
-- BODY
  have productReferenceIntegral (n : ℕ) (v : UnitAddTorus (Fin d)→ℝ)
      (hv : Measurable v) (hvn : ∀ᵐx∂(volume : Measure (UnitAddTorus (Fin d))),0≤v x)
      (hvi : Integrable v volume) (hvmass : ∫x,v x∂volume=1)
      (F : Configuration d n→ℝ) :
      (∫X,F X∂Measure.pi (fun _:Fin n=>(volume : Measure (UnitAddTorus (Fin d))).withDensity (fun x=>ENNReal.ofReal (v x))))=
        ∫X,F X*ProductDensity v X∂volume := by
    exact (ProductDensityMeasureIdentity d n v hv hvn hvi hvmass).2 F
  haveI:IsProbabilityMeasure (volume:Measure (AddCircle (1:ℝ))):=by
    rw[AddCircle.volume_eq_smul_haarAddCircle];simp;infer_instance
  haveI:IsProbabilityMeasure (volume:Measure (UnitAddTorus (Fin d))):=inferInstance
  apply UniformLogSobolevFromPartitionBounds d hd s a B l u hs hsd hL ha hB hl hl1 hu
  intro T M hT hM
  obtain ⟨K,hK,hpart⟩:=RieszCenteredPartitionUniform d hd s a hs hL ha T M hT hM
  refine ⟨K,hK,?_⟩
  intro N hN t ε ht htT hε rl r
  have hrn:∀ᵐx∂(volume:Measure (UnitAddTorus (Fin d))),0≤r.density x:=
    r.bounds.mono fun x hx=>r.lower_pos.le.trans hx.1
  have hrb:∀ᵐx∂(volume:Measure (UnitAddTorus (Fin d))),0≤r.density x∧r.density x≤M:=
    r.bounds.mono fun x hx=>⟨r.lower_pos.le.trans hx.1,hx.2⟩
  have hri:Integrable r.density volume:=by
    apply Integrable.of_bound r.measurable.aestronglyMeasurable M
    filter_upwards[hrb] with x hx
    simpa only[Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2
  have hid := productReferenceIntegral N r.density r.measurable hrn hri r.mass
    (fun X => Real.exp (-t*CenteredPairEnergy (RieszKernel d s a ε) r.density X))
  rw[hid]
  exact (hpart N hN t ε ht htT hε r.density r.measurable hrb r.mass).2
