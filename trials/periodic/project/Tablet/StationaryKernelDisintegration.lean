module

public import Tablet.Preamble
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.MeasurableIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section
universe u
open MeasureTheory ProbabilityTheory
-- [TABLET NODE: StationaryKernelDisintegration]
theorem StationaryKernelDisintegration {X Y:Type u}[MeasurableSpace X][MeasurableSpace Y]
    (P:Measure (X×Y))[IsProbabilityMeasure P](κ:Kernel X Y)[IsMarkovKernel κ]
    (hrow:∀F:X×Y→ℝ,Measurable F→(∃C:ℝ,∀p,|F p|≤C)→
      Integrable (fun p=>∫y,F (p.1,y)∂κ p.1) P ∧
      (∫p,∫y,F (p.1,y)∂κ p.1∂P)=(∫p,F p∂P)) :
    P=P.fst⊗ₘκ := by
-- BODY
  classical
  ext A hA
  let F:=A.indicator (fun _=> (1:ℝ))
  have hFm:Measurable F:=measurable_const.indicator hA
  have hFb:∀p,|F p|≤1:=by intro p;dsimp[F];by_cases hp:p∈A <;>simp[hp]
  have hFi:Integrable F (P.fst⊗ₘκ):=by
    apply (integrable_const (1:ℝ)).mono' hFm.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun p=>by simpa only[Real.norm_eq_abs] using hFb p
  have hGm:Measurable (fun x=>∫y,F (x,y)∂κ x):=
    hFm.stronglyMeasurable.integral_kernel_prod_right'.measurable
  have hmap:=integral_map (μ:=P) (φ:=Prod.fst) measurable_fst.aemeasurable hGm.aestronglyMeasurable
  change (∫x,∫y,F (x,y)∂κ x∂P.fst)=(∫p,∫y,F (p.1,y)∂κ p.1∂P) at hmap
  have he:(∫p,F p∂P)=(∫p,F p∂P.fst⊗ₘκ):=by
    rw[Measure.integral_compProd hFi,hmap]
    exact (hrow F hFm ⟨1,hFb⟩).2.symm
  change (∫p,A.indicator (fun _=>(1:ℝ)) p∂P)=
    (∫p,A.indicator (fun _=>(1:ℝ)) p∂P.fst⊗ₘκ) at he
  simp only[integral_indicator_const (1:ℝ) hA,smul_eq_mul,mul_one] at he
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top P A) (measure_ne_top (P.fst⊗ₘκ) A)).mp he
