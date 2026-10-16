import Tablet.Entropy
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
universe u
open MeasureTheory ProbabilityTheory
-- [TABLET NODE: ConditionalSquareEntropyIdentity]
theorem ConditionalSquareEntropyIdentity {X Y:Type u}[MeasurableSpace X][MeasurableSpace Y]
    (μ:Measure X)[IsProbabilityMeasure μ](κ:Kernel X Y)[IsMarkovKernel κ]
    (f:X×Y→ℝ)(hf:Measurable f)(R:ℝ)(hR:∀p,|f p|≤R) :
    let m:=fun x=>∫y,f (x,y)^2∂κ x
    Integrable (fun x=>Entropy (κ x) (fun y=>f (x,y)^2)) μ ∧
    Entropy (μ⊗ₘκ) (fun p=>f p^2)=Entropy μ m+
      (∫x,Entropy (κ x) (fun y=>f (x,y)^2)∂μ) := by
-- BODY
  have bi (α:Type u)[MeasurableSpace α](ν:Measure α)[IsFiniteMeasure ν]
      (g:α→ℝ)(hg:Measurable g)(C:ℝ)(hb:∀x,|g x|≤C):Integrable g ν:=by
    apply (integrable_const C).mono' hg.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x=>by simpa only[Real.norm_eq_abs] using hb x
  let m:=fun x=>∫y,f (x,y)^2∂κ x
  let A:=fun x=>∫y,f (x,y)^2*Real.log (f (x,y)^2)∂κ x
  have hu:Measurable (fun p=>f p^2):=hf.pow_const 2
  have hub:∀p,f p^2≤R^2:=fun p=>sq_le_sq.mpr ((hR p).trans (le_abs_self R))
  have hui:Integrable (fun p=>f p^2) (μ⊗ₘκ):=bi _ _ _ hu (R^2)
    (fun p=>by rw[abs_of_nonneg (sq_nonneg _)];exact hub p)
  have hmm:Measurable m:=(hu.stronglyMeasurable.integral_kernel_prod_right').measurable
  have hmrow:∀x,Integrable (fun y=>f (x,y)^2) (κ x):=by
    intro x
    exact bi _ _ _ (hu.comp (measurable_const.prodMk measurable_id)) (R^2)
      (fun y=>by rw[abs_of_nonneg (sq_nonneg _)];exact hub (x,y))
  have hmb:∀x,0≤m x∧m x≤R^2:=by
    intro x
    refine ⟨integral_nonneg (fun y=>sq_nonneg _),?_⟩
    have hh:=integral_mono (hmrow x) (integrable_const (R^2)) (fun y=>hub (x,y))
    simpa using hh
  have hmi:Integrable m μ:=bi _ _ m hmm (R^2) (fun x=>by rw[abs_of_nonneg (hmb x).1];exact (hmb x).2)
  obtain ⟨K,hK⟩:=(isCompact_Icc:IsCompact (Set.Icc (0:ℝ) (R^2))).exists_bound_of_continuousOn
    Real.continuous_mul_log.continuousOn
  have hlogm:Measurable (fun p=>f p^2*Real.log (f p^2)):=Real.continuous_mul_log.measurable.comp hu
  have hlogb:∀p,|f p^2*Real.log (f p^2)|≤K:=by
    intro p
    simpa only[Real.norm_eq_abs] using hK (f p^2) ⟨sq_nonneg _,hub p⟩
  have hlogi:Integrable (fun p=>f p^2*Real.log (f p^2)) (μ⊗ₘκ):=bi _ _ _ hlogm K hlogb
  have hAm:Measurable A:=(hlogm.stronglyMeasurable.integral_kernel_prod_right').measurable
  have hAb:∀x,|A x|≤K:=by
    intro x
    have hrm:Measurable (fun y=>f (x,y)^2*Real.log (f (x,y)^2)):=
      hlogm.comp (measurable_const.prodMk measurable_id)
    have hri:=bi _ (κ x) _ hrm K (fun y=>hlogb (x,y))
    have hh:=abs_integral_le_integral_abs (μ:=κ x) (f:=fun y=>f (x,y)^2*Real.log (f (x,y)^2))
    have hb:=integral_mono hri.abs (integrable_const K) (fun y=>hlogb (x,y))
    exact hh.trans (by simpa using hb)
  have hAi:Integrable A μ:=bi _ _ A hAm K hAb
  have hmli:Integrable (fun x=>m x*Real.log (m x)) μ:=bi _ _ _
    (Real.continuous_mul_log.measurable.comp hmm) K (fun x=>by
      simpa only[Real.norm_eq_abs] using hK (m x) (hmb x))
  have he:(fun x=>Entropy (κ x) (fun y=>f (x,y)^2))=(fun x=>A x-m x*Real.log (m x)):=rfl
  rw[he]
  refine ⟨hAi.sub hmli,?_⟩
  change ((∫p,f p^2*Real.log (f p^2)∂μ⊗ₘκ)-(∫p,f p^2∂μ⊗ₘκ)*Real.log (∫p,f p^2∂μ⊗ₘκ))=
    ((∫x,m x*Real.log (m x)∂μ)-(∫x,m x∂μ)*Real.log (∫x,m x∂μ))+
      (∫x,A x-m x*Real.log (m x)∂μ)
  rw[Measure.integral_compProd hlogi,Measure.integral_compProd hui,integral_sub hAi hmli]
  change (∫x,A x∂μ)-(∫x,m x∂μ)*Real.log (∫x,m x∂μ)=
    ((∫x,m x*Real.log (m x)∂μ)-(∫x,m x∂μ)*Real.log (∫x,m x∂μ))+
      ((∫x,A x∂μ)-(∫x,m x*Real.log (m x)∂μ))
  ring
