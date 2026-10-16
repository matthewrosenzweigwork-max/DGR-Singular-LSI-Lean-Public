module

public import Tablet.HeatCenteredEnergyAveraging
public import Tablet.HeatBoundedReferencePushforward
public import Tablet.IndependentShiftPushforward
public import Tablet.ProbabilityJensenTransport
public import Tablet.ProductDensityMeasureIdentity
public import Tablet.CenteredPartition

@[expose] public section
open MeasureTheory
-- [TABLET NODE: HeatCenteredPartitionComparison]
theorem HeatCenteredPartitionComparison (d N : ℕ) (t : ℝ) (ht : 0<t)
    (r : UnitAddTorus (Fin d)→ℝ) (M : ℝ) (hM : 1≤M) (hr : Measurable r)
    (hrb : ∀ᵐx∂(volume : Measure (UnitAddTorus (Fin d))),0≤r x∧r x≤M)
    (hrmass : ∫x,r x∂volume=1) (g : UnitAddTorus (Fin d)→ℝ)
    (hg : Measurable g) (hgi : Integrable g volume) (c : ℝ) (hc : 0≤c) (hgl : ∀x,-c≤g x)
    (β : ℝ) (hβ : 0≤β) :
    CenteredPartition (N:=N) (HeatSemigroup d (t+t) g) r β ≤
      CenteredPartition (N:=N) g (HeatSemigroup d t r) β := by
-- BODY
  have productReferenceIntegral (n : ℕ) (v : UnitAddTorus (Fin d)→ℝ)
      (hv : Measurable v) (hvn : ∀ᵐx∂(volume : Measure (UnitAddTorus (Fin d))),0≤v x)
      (hvi : Integrable v volume) (hvmass : ∫x,v x∂volume=1)
      (F : Configuration d n→ℝ) :
      (∫X,F X∂Measure.pi (fun _:Fin n=>(volume : Measure (UnitAddTorus (Fin d))).withDensity (fun x=>ENNReal.ofReal (v x))))=
        ∫X,F X*ProductDensity v X∂volume := by
    exact (ProductDensityMeasureIdentity d n v hv hvn hvi hvmass).2 F
  classical
  haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle];simp;infer_instance
  haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) :=inferInstance
  let T:=UnitAddTorus (Fin d)
  let m:Measure T:=volume
  let r':T→ℝ:=HeatSemigroup d t r
  have hrn:∀ᵐx∂m,0≤r x:=hrb.mono fun x hx=>hx.1
  have hrNorm:∀ᵐx∂m,‖r x‖≤M:=by
    filter_upwards [hrb] with x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2
  have hri:Integrable r m:=Integrable.of_bound hr.aestronglyMeasurable M hrNorm
  have hP:=HeatOperatorBounds d t ht r hr hri
  have hr'b:∀ᵐx∂m,0≤r' x∧r' x≤M:=Filter.Eventually.of_forall (hP.2.2.2.2.1 0 M hrb)
  have hr'n:∀ᵐx∂m,0≤r' x:=hr'b.mono fun x hx=>hx.1
  have hr'mass:∫x,r' x∂m=1:=hP.2.2.1.trans hrmass
  let μ:=m.withDensity (fun x=>ENNReal.ofReal (r x))
  let ν:=HeatIncrementLaw d t
  let μ':=m.withDensity (fun x=>ENNReal.ofReal (r' x))
  have probDensity (f:T→ℝ) (hi:Integrable f m) (hn:∀ᵐx∂m,0≤f x) (hm:∫x,f x∂m=1) :
      IsProbabilityMeasure (m.withDensity (fun x=>ENNReal.ofReal (f x))) :=by
    apply isProbabilityMeasure_iff.mpr
    rw [withDensity_apply _ MeasurableSet.univ]
    simp only [Measure.restrict_univ]
    rw [←ofReal_integral_eq_lintegral_ofReal hi hn,hm]
    simp
  haveI : IsProbabilityMeasure μ:=probDensity r hri hrn hrmass
  haveI : IsProbabilityMeasure μ':=probDensity r' hP.2.1 hr'n hr'mass
  haveI : IsProbabilityMeasure ν:=(HeatIncrementAveraging d t ht).1
  let P:=Measure.pi (fun _:Fin N=>μ)
  let Q:=Measure.pi (fun _:Fin N=>ν)
  let P':=Measure.pi (fun _:Fin N=>μ')
  let S:Configuration d N×Configuration d N→Configuration d N:=fun p i=>p.1 i+p.2 i
  have hSm:Measurable S:=by fun_prop
  have hmap : Measure.map S (P.prod Q)=P' :=IndependentShiftPushforward N μ ν μ'
    (HeatBoundedReferencePushforward d t ht r M (zero_le_one.trans hM) hr hrb)
  have hB:=CenteredKernelBounds d g r' hg hgi hP.1 M c hM hc hr'b hr'mass hgl
  let E:Configuration d N→ℝ:=CenteredPairEnergy g r'
  let A:Configuration d N→ℝ:=CenteredPairEnergy (HeatSemigroup d (t+t) g) r
  have hEm:Measurable E :=by
    unfold E CenteredPairEnergy
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i _
    apply Finset.measurable_sum
    intro j _
    by_cases hij:i<j
    · simp only [if_pos hij]
      have heval : Measurable (fun X:Configuration d N=>(X i,X j)) :=
        (measurable_pi_apply i).prodMk (measurable_pi_apply j)
      exact hB.2.2.2.2.1.comp heval
    · simp only [if_neg hij]
      exact measurable_const
  have havg := HeatCenteredEnergyAveraging d N t ht r M hM hr hrb hrmass g hg hgi c hc hgl
  have hAm:Measurable A :=by
    have hfn:(fun X:Configuration d N=>∫Y:Configuration d N,E (S (X,Y))∂Q)=A:=funext fun X=>(havg X).2
    rw [←hfn]
    have hj : StronglyMeasurable (Function.uncurry (fun X Y:Configuration d N=>E (S (X,Y)))) := (hEm.comp hSm).stronglyMeasurable
    exact hj.integral_prod_right.measurable
  let C:=c+3*M*(∫x,|g x|∂volume)
  have hC:0≤C:=by dsimp [C];positivity
  have hElo (X:Configuration d N) : -((N:ℝ)⁻¹*(N:ℝ)*(N:ℝ)*C)≤E X :=by
    calc
      _=(N:ℝ)⁻¹*∑i:Fin N,∑j:Fin N,(-C):=by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        ring
      _≤E X:=by
        unfold E CenteredPairEnergy
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg N))
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        by_cases hij:i<j
        · simp only [if_pos hij]
          dsimp [C]
          linarith [hB.2.2.2.2.2.2 (X i) (X j)]
        · simp only [if_neg hij]
          linarith
  have hJ:=ProbabilityJensenTransport P Q P' S hSm hmap E A hEm hAm
    ((N:ℝ)⁻¹*(N:ℝ)*(N:ℝ)*C) β hβ hElo havg
  have hIR:=productReferenceIntegral N r hr hrn hri hrmass (fun X=>Real.exp (-β*A X))
  have hIR':=productReferenceIntegral N r' hP.1 hr'n hP.2.1 hr'mass (fun X=>Real.exp (-β*E X))
  change (∫X,Real.exp (-β*A X)*ProductDensity r X∂volume)≤
    ∫X,Real.exp (-β*E X)*ProductDensity r' X∂volume
  rw [←hIR,←hIR']
  exact hJ.2.2
