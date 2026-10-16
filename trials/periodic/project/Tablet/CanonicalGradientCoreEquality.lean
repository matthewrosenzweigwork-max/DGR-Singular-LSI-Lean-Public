import Tablet.CanonicalCollisionFreeGraphApproximation
import Tablet.CanonicalGradientClosability
import Tablet.GradientFormDomain
open MeasureTheory Set
-- [TABLET NODE: CanonicalGradientCoreEquality]
theorem CanonicalGradientCoreEquality (d N:ℕ) (hd:2≤d) (hN:2≤N)
    (s a l u β:ℝ) (hs:0≤s) (hsd:s<(d:ℝ)) (ha:0<a)
    (q:BoundedBackground d l u) (hβ:0≤β) (ε:ℝ) (hε:0≤ε) :
    let P:=CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β
    GradientGraphClosure P false=GradientGraphClosure P true ∧
    GradientFormDomain P false=GradientFormDomain P true ∧
    ∀f:Lp ℝ 2 P,f∈GradientFormDomain P false →
      ∃!v:Lp (EuclideanSpace ℝ (Fin N×Fin d)) 2 P,(f,v)∈GradientGraphClosure P false := by
-- BODY
  let P:=CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β
  have happrox := CanonicalCollisionFreeGraphApproximation d N hd hN s a l u β hs hsd ha q hβ ε hε
  have hsubset:GradientGraphClosure P true⊆GradientGraphClosure P false := by
    apply closure_mono
    rintro v ⟨f,hf,hD,hs,rfl⟩
    refine ⟨f,hf,hD,?_,rfl⟩
    exact (show f∈CollisionFreeCore d N from hs).1
  have hother:GradientGraphClosure P false⊆GradientGraphClosure P true := by
    apply closure_minimal _ isClosed_closure
    rintro v ⟨f,hf,hD,hs,rfl⟩
    exact happrox f hs hf hD
  have he:=Set.Subset.antisymm hother hsubset
  refine ⟨he,?_,?_⟩
  · unfold GradientFormDomain
    rw [he]
  · intro f hf
    obtain ⟨v,hv⟩:=hf
    refine ⟨v,hv,?_⟩
    intro w hw
    exact CanonicalGradientClosability d N hd hN s a l u β hs hsd ha q hβ ε hε f w v hw hv
