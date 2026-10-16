module

public import Tablet.TorusConvolutionAssociativity
public import Tablet.HeatKernelFacts

@[expose] public section
open MeasureTheory
-- [TABLET NODE: HeatSemigroupComposition]
theorem HeatSemigroupComposition (d : ℕ) (t u : ℝ) (ht : 0<t) (hu : 0<u)
    (f : UnitAddTorus (Fin d)→ℝ) (hf : Integrable f volume) :
    ∀x, HeatSemigroup d t (HeatSemigroup d u f) x=HeatSemigroup d (t+u) f x := by
-- BODY
  let T:=UnitAddTorus (Fin d)
  let L:=ContinuousLinearMap.mul ℝ ℝ
  have hcomm (f g:T→ℝ) : convolution f g L volume=convolution g f L volume := by
    have hflip : L.flip=L := by
      apply ContinuousLinearMap.ext
      intro a
      apply ContinuousLinearMap.ext
      intro b
      change b*a=a*b
      ring
    have hh:=convolution_flip (f:=f) (g:=g) (L:=L) (μ:=volume)
    rw [hflip] at hh
    exact hh.symm
  have hkernel (v:ℝ)(hv:0<v) : Integrable (HeatKernel d v) volume ∧
      ∃C:ℝ,∀ᵐx∂(volume:Measure T),‖HeatKernel d v x‖≤C := by
    have hp:Continuous (HeatKernel d v):=(HeatKernelFacts d v hv).1
    obtain ⟨C,hC⟩:=(isCompact_univ:IsCompact (Set.univ:Set T)).exists_bound_of_continuousOn hp.continuousOn
    have hb:∀ᵐx∂(volume:Measure T),‖HeatKernel d v x‖≤C:=Filter.Eventually.of_forall fun x=>hC x (Set.mem_univ x)
    exact ⟨Integrable.of_bound hp.measurable.aestronglyMeasurable C hb,C,hb⟩
  obtain ⟨hpti,C,hptb⟩:=hkernel t ht
  obtain ⟨hpui,D,hpub⟩:=hkernel u hu
  have hassoc:=TorusConvolutionAssociativity d f (HeatKernel d u) (HeatKernel d t) C hf hpui
    (HeatKernelFacts d t ht).1.measurable hptb
  have hKK : convolution (HeatKernel d u) (HeatKernel d t) L volume=HeatKernel d (u+t) := by
    funext x;exact (HeatKernelFacts d u hu).2.2.2.2.2 t ht x
  intro x
  change convolution (HeatKernel d t) (convolution (HeatKernel d u) f L volume) L volume x=
    convolution (HeatKernel d (t+u)) f L volume x
  rw [hcomm (HeatKernel d u) f,hcomm (HeatKernel d t) (convolution f (HeatKernel d u) L volume),
    hassoc,hKK,hcomm f (HeatKernel d (u+t)),add_comm u t]
