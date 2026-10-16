module

public import Tablet.ConditionalSquareEntropyIdentity
public import Tablet.KernelWeightedFirstMarginal
public import Tablet.SquareDensityRelativeEntropy
public import Mathlib.InformationTheory.KullbackLeibler.ChainRule
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel

@[expose] public section
universe u
open MeasureTheory InformationTheory ProbabilityTheory
-- [TABLET NODE: ConditionalSquareRelativeEntropy]
theorem ConditionalSquareRelativeEntropy {X Y:Type u}[MeasurableSpace X][MeasurableSpace Y]
    [StandardBorelSpace Y][Nonempty Y]
    (μ:Measure X)[IsProbabilityMeasure μ](κ:Kernel X Y)[IsMarkovKernel κ]
    (f:X×Y→ℝ)(hf:Measurable f)(R:ℝ)(hR:∀p,|f p|≤R)
    (ha:0<∫p,f p^2∂μ⊗ₘκ) :
    let a:=∫p,f p^2∂μ⊗ₘκ
    let S:=(μ⊗ₘκ).withDensity (fun p=>ENNReal.ofReal (f p^2/a))
    IsProbabilityMeasure S ∧ klDiv S (S.fst⊗ₘκ)≠⊤ ∧
      a*(klDiv S (S.fst⊗ₘκ)).toReal=(∫x,Entropy (κ x) (fun y=>f (x,y)^2)∂μ) := by
-- BODY
  let P:=μ⊗ₘκ
  let a:=∫p,f p^2∂P
  let m:=fun x=>∫y,f (x,y)^2∂κ x
  let S:=P.withDensity (fun p=>ENNReal.ofReal (f p^2/a))
  have hu:Measurable (fun p=>f p^2):=hf.pow_const 2
  have hub:∀p,f p^2≤R^2:=fun p=>sq_le_sq.mpr ((hR p).trans (le_abs_self R))
  have hui:Integrable (fun p=>f p^2) P:=by
    apply (integrable_const (R^2)).mono' hu.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun p=>by rw[Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)];exact hub p
  have hmm:Measurable m:=(hu.stronglyMeasurable.integral_kernel_prod_right').measurable
  have hmi:∀x,Integrable (fun y=>f (x,y)^2) (κ x):=by
    intro x
    apply (integrable_const (R^2)).mono' (hu.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun y=>by
      change ‖f (x,y)^2‖≤R^2
      rw[Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)];exact hub (x,y)
  have hmb:∀x,0≤m x∧m x≤R^2:=by
    intro x
    refine ⟨integral_nonneg (fun y=>sq_nonneg _),?_⟩
    have hh:=integral_mono (hmi x) (integrable_const (R^2)) (fun y=>hub (x,y))
    simpa using hh
  have hmass:(∫x,m x∂μ)=a:=(Measure.integral_compProd hui).symm
  have hfull:=SquareDensityRelativeEntropy P f hf R hR ha
  haveI:IsProbabilityMeasure S:=hfull.1
  have hfirst:=KernelWeightedFirstMarginal μ κ (fun p=>f p^2/a) ((hf.pow_const 2).div_const a)
    (R^2/a) (fun p=>⟨div_nonneg (sq_nonneg _) ha.le,div_le_div_of_nonneg_right (hub p) ha.le⟩)
  simp_rw[integral_div] at hfirst
  change S.fst=μ.withDensity (fun x=>ENNReal.ofReal (m x/a)) at hfirst
  have hsq:∀x,(Real.sqrt (m x))^2=m x:=fun x=>Real.sq_sqrt (hmb x).1
  have hsm:Measurable (fun x=>Real.sqrt (m x)):=Real.continuous_sqrt.measurable.comp hmm
  have hsb:∀x,|Real.sqrt (m x)|≤|R|:=by
    intro x
    rw[abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (Real.sqrt_le_sqrt (hmb x).2).trans_eq (Real.sqrt_sq_eq_abs R)
  have has:0<∫x,(Real.sqrt (m x))^2∂μ:=by simp_rw[hsq,hmass];exact ha
  have hmar:=SquareDensityRelativeEntropy μ (fun x=>Real.sqrt (m x)) hsm |R| hsb has
  simp_rw[hsq] at hmar
  rw[hmass,←hfirst] at hmar
  have hc:=klDiv_compProd_eq_add S.fst μ S.condKernel κ
  rw[S.disintegrate S.condKernel] at hc
  change klDiv S P=klDiv S.fst μ+klDiv S (S.fst⊗ₘκ) at hc
  have hfin:klDiv S (S.fst⊗ₘκ)≠⊤:=by
    have hh:klDiv S.fst μ+klDiv S (S.fst⊗ₘκ)≠⊤:=by rw[←hc];exact hfull.2.1
    exact (ENNReal.add_ne_top.mp hh).2
  have hreal:(klDiv S P).toReal=(klDiv S.fst μ).toReal+(klDiv S (S.fst⊗ₘκ)).toReal:=by
    rw[hc,ENNReal.toReal_add hmar.2.1 hfin]
  have hid:=ConditionalSquareEntropyIdentity μ κ f hf R hR
  refine ⟨hfull.1,hfin,?_⟩
  have he:=hfull.2.2
  rw[hreal,mul_add,hmar.2.2] at he
  linarith[hid.2]
