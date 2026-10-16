module

public import Tablet.HeatOperatorBounds
public import Tablet.HeatSemigroupComposition
public import Tablet.CenteredKernelBounds

@[expose] public section
open MeasureTheory
-- [TABLET NODE: HeatBoundedCenteredBackgroundIdentity]
theorem HeatBoundedCenteredBackgroundIdentity (d : ℕ) (t : ℝ) (ht : 0<t)
    (r : UnitAddTorus (Fin d)→ℝ) (u : ℝ) (hu : 1≤u) (hr : Measurable r)
    (hrb0 : ∀ᵐx∂(volume : Measure (UnitAddTorus (Fin d))),0≤r x∧r x≤u)
    (hrmass : ∫x,r x∂volume=1) (g : UnitAddTorus (Fin d)→ℝ)
    (hg : Measurable g) (hgi : Integrable g volume) (c : ℝ) (hc : 0≤c)
    (hgl : ∀x,-c≤g x) :
    let r' := HeatSemigroup d t r
    (∀x, HeatSemigroup d t (BackgroundPotential g r') x=
      BackgroundPotential (HeatSemigroup d (t+t) g) r x) ∧
    BackgroundPairMean g r'=BackgroundPairMean (HeatSemigroup d (t+t) g) r := by
-- BODY
  haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp; infer_instance
  haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := inferInstance
  let T:=UnitAddTorus (Fin d)
  let L:=ContinuousLinearMap.mul ℝ ℝ
  have hcomm (f h:T→ℝ) : convolution f h L volume=convolution h f L volume :=by
    have hflip:L.flip=L:=by
      apply ContinuousLinearMap.ext
      intro a
      apply ContinuousLinearMap.ext
      intro b
      change b*a=a*b
      ring
    have hh:=convolution_flip (f:=f) (g:=h) (L:=L) (μ:=volume)
    rw [hflip]at hh
    exact hh.symm
  have hrb:∀ᵐx∂(volume : Measure T),‖r x‖≤u :=by
    filter_upwards [hrb0] with x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2
  have hri : Integrable r volume := Integrable.of_bound hr.aestronglyMeasurable u hrb
  have hP:=HeatOperatorBounds d t ht r hr hri
  let r':T→ℝ:=HeatSemigroup d t r
  have hr' : ∀x,r' x=HeatSemigroup d t r x:=fun _=>rfl
  have hb' : ∀x,0≤r' x∧r' x≤u:=hP.2.2.2.2.1 0 u hrb0
  have hr'm:Measurable r':=hP.1
  have hr'mass : ∫x,r' x∂volume=1:=hP.2.2.1.trans hrmass
  have hp:Continuous (HeatKernel d t):=(HeatKernelFacts d t ht).1
  have hpi:Integrable (HeatKernel d t) volume:=hp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hback (f q:T→ℝ) : BackgroundPotential f q=convolution f q L volume := by
    change convolution q f L volume=convolution f q L volume
    exact hcomm q f
  have hr'b:∀ᵐx∂(volume:Measure T),0≤r' x∧r' x≤u:=Filter.Eventually.of_forall hb'
  have hgb:=CenteredKernelBounds d g r' hg hgi hr'm u c hu hc hr'b hr'mass hgl
  have hgr' := hback g r'
  have hbody : ∀x, HeatSemigroup d t (BackgroundPotential g r') x=
      BackgroundPotential (HeatSemigroup d (t+t) g) r x := by
    have hPgi := (HeatOperatorBounds d t ht g hg hgi).2.1
    have hr'bNorm : ∀ᵐx∂(volume : Measure T),‖r' x‖≤u:=by
      filter_upwards [hr'b] with x hx
      simpa only [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2
    have ha1 := TorusConvolutionAssociativity d (HeatKernel d t) g r' u hpi hgi hr'm hr'bNorm
    have ha2 := TorusConvolutionAssociativity d (HeatSemigroup d t g) (HeatKernel d t) r u hPgi hpi hr hrb
    have hrg : r'=convolution (HeatKernel d t) r L volume := funext hr'
    have hP2 : convolution (HeatSemigroup d t g) (HeatKernel d t) L volume = HeatSemigroup d (t+t) g := by
      rw [hcomm (HeatSemigroup d t g) (HeatKernel d t)]
      exact funext (HeatSemigroupComposition d t t ht ht g hgi)
    intro x
    change convolution (HeatKernel d t) (BackgroundPotential g r') L volume x=_
    rw [hgr',←funext ha1]
    change convolution (HeatSemigroup d t g) r' L volume x=_
    rw [hrg,←funext ha2,hP2]
    exact congrFun (hback (HeatSemigroup d (t+t) g) r).symm x
  have hre := funext hr'
  constructor
  · change ∀x,HeatSemigroup d t (BackgroundPotential g (HeatSemigroup d t r)) x=_
    rw [←hre]
    exact hbody
  · change BackgroundPairMean g (HeatSemigroup d t r)=_
    rw [←hre]
    unfold BackgroundPairMean
    have hm:=(HeatOperatorBounds d t ht r hr hri).2.2.2.2.2 (BackgroundPotential g r') hgb.1 ⟨_,fun x=>(hgb.2.1 x).2⟩
    rw [←hre] at hm
    rw [hm]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x=>by
      dsimp only
      rw [hbody]
      ring
