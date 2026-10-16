import Tablet.IndependentPairEvenMoment
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
universe u
open MeasureTheory
open scoped BigOperators
-- [TABLET NODE: IndependentCenteredEvenMoment]
theorem IndependentCenteredEvenMoment {Ω:Type u}[MeasurableSpace Ω]
    (N:ℕ)(μ:Fin N→Measure Ω)[∀i,IsProbabilityMeasure (μ i)]
    (Z:Fin N→Ω→ℝ)(hZ:∀i,Measurable (Z i))
    (hbound:∃B:ℝ,∀i x,|Z i x|≤B)(hmean:∀i,∫x,Z i x∂μ i=0)
    (m:ℕ)(hm:1≤m) :
    (∫X:Fin N→Ω,(∑i:Fin N,Z i (X i))^(2*m)∂Measure.pi μ)≤
    (6*(m:ℝ))^m*(∫v:Fin N→Ω×Ω,(∑i:Fin N,(Z i (v i).1-Z i (v i).2)^2)^m
      ∂Measure.pi (fun i=>(μ i).prod (μ i))) := by
-- BODY
  classical
  have bounded_integrable (α:Type u)[MeasurableSpace α](ν:Measure α)[IsFiniteMeasure ν]
      (f:α→ℝ)(hf:Measurable f)(C:ℝ)(hb:∀x,|f x|≤C):Integrable f ν:=by
    apply (integrable_const C).mono' hf.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x=>by simpa only[Real.norm_eq_abs] using hb x
  obtain ⟨B,hB⟩:=hbound
  let P:=Measure.pi μ
  let Q:=Measure.pi (fun i=>(μ i).prod (μ i))
  let F:=fun X:Fin N→Ω=>∑i:Fin N,Z i (X i)
  let C:ℝ:=(N:ℝ)*|B|
  have hFm:Measurable F:=Finset.measurable_fun_sum _ fun i _=>(hZ i).comp (measurable_pi_apply i)
  have hFb:∀X,|F X|≤C:=by
    intro X
    have hh:|F X|≤∑i:Fin N,|Z i (X i)|:=Finset.abs_sum_le_sum_abs _ _
    exact hh.trans (by simpa[C] using Finset.sum_le_sum (s:=Finset.univ) fun i _=>(hB i (X i)).trans (le_abs_self B))
  have hZi:∀i,Integrable (fun X:Fin N→Ω=>Z i (X i)) P:=by
    intro i
    exact bounded_integrable _ P _ ((hZ i).comp (measurable_pi_apply i)) |B| (fun X=>(hB i (X i)).trans (le_abs_self B))
  have hFmean:(∫X,F X∂P)=0:=by
    rw[integral_finset_sum _ fun i _=>hZi i]
    have he:∀i,(∫X:Fin N→Ω,Z i (X i)∂P)=0:=by
      intro i
      have hp:=measurePreserving_eval μ i
      have hh:=integral_map (μ:=P) hp.measurable.aemeasurable (hZ i).aestronglyMeasurable
      rw[hp.map_eq,hmean] at hh
      exact hh.symm
    simp_rw[he]
    simp
  have hCn:0≤C:=mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
  have hpowi:Integrable (fun X=>F X^(2*m)) P:=
    bounded_integrable _ P _ (hFm.pow_const _) (C^(2*m)) (fun X=>by
      rw[abs_pow];exact pow_le_pow_left₀ (abs_nonneg _) (hFb X) _)
  let H:=fun p:(Fin N→Ω)×(Fin N→Ω)=>(F p.1-F p.2)^(2*m)
  have hHm:Measurable H:=((hFm.comp measurable_fst).sub (hFm.comp measurable_snd)).pow_const _
  have hHb:∀p,|H p|≤(2*C)^(2*m):=by
    intro p
    rw[abs_pow]
    apply pow_le_pow_left₀ (abs_nonneg _)
    exact (abs_sub _ _).trans (by nlinarith[hFb p.1,hFb p.2])
  have hHi:Integrable H (P.prod P):=bounded_integrable _ _ _ hHm _ hHb
  have hjensen:∀X,F X^(2*m)≤∫Y,(F X-F Y)^(2*m)∂P:=by
    intro X
    have hdiffm:Measurable (fun Y=>F X-F Y):=measurable_const.sub hFm
    have hdiffb:∀Y,|F X-F Y|≤2*C:=fun Y=>(abs_sub _ _).trans (by nlinarith[hFb X,hFb Y])
    have hdiffi:=bounded_integrable _ P _ hdiffm (2*C) hdiffb
    have hpowdi:=bounded_integrable _ P _ (hdiffm.pow_const (2*m)) ((2*C)^(2*m))
      (fun Y=>by rw[abs_pow];exact pow_le_pow_left₀ (abs_nonneg _) (hdiffb Y) _)
    have heven:Even (2*m):=⟨m,by omega⟩
    have hh:=heven.convexOn_pow (𝕜:=ℝ)
    have hj:=hh.map_integral_le (continuous_id.pow (2*m)).continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun _=>Set.mem_univ _) hdiffi hpowdi
    have he:(∫Y,F X-F Y∂P)=F X:=by
      rw[integral_sub (integrable_const _) (bounded_integrable _ P F hFm C hFb),hFmean]
      simp
    rwa[he] at hj
  have hJ: (∫X,F X^(2*m)∂P)≤∫X,∫Y,(F X-F Y)^(2*m)∂P∂P:=
    integral_mono hpowi hHi.integral_prod_left hjensen
  let E:=MeasurableEquiv.arrowProdEquivProdArrow Ω Ω (Fin N)
  have hmp:MeasurePreserving E Q (P.prod P):=measurePreserving_arrowProdEquivProdArrow Ω Ω (Fin N) μ μ
  have heq:∀v:Fin N→Ω×Ω,H (E v)=(∑i:Fin N,(Z i (v i).1-Z i (v i).2))^(2*m):=by
    intro v
    dsimp[H,F,E,MeasurableEquiv.arrowProdEquivProdArrow]
    rw[Finset.sum_sub_distrib]
    rfl
  have hmap:=hmp.integral_comp E.measurableEmbedding H
  simp_rw[heq] at hmap
  have hRi:Integrable (fun v:Fin N→Ω×Ω=>(∑i:Fin N,(Z i (v i).1-Z i (v i).2)^2)^m) Q:=by
    have hb:∀v:Fin N→Ω×Ω,∀i:Fin N,(Z i (v i).1-Z i (v i).2)^2≤(2*|B|)^2:=by
      intro v i
      have hh:|Z i (v i).1-Z i (v i).2|≤2*|B|:=
        (abs_sub _ _).trans (by have h1:=(hB i (v i).1).trans (le_abs_self B);have h2:=(hB i (v i).2).trans (le_abs_self B);linarith)
      simpa only[sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hh 2
    apply bounded_integrable _ Q _ ?_ (((N:ℝ)*(2*|B|)^2)^m) ?_
    · apply Measurable.pow_const
      apply Finset.measurable_fun_sum
      intro i hi
      exact (((hZ i).comp (measurable_fst.comp (measurable_pi_apply i))).sub
        ((hZ i).comp (measurable_snd.comp (measurable_pi_apply i)))).pow_const 2
    · intro v
      have hn:0≤∑i:Fin N,(Z i (v i).1-Z i (v i).2)^2:=Finset.sum_nonneg fun i _=>sq_nonneg _
      rw[abs_of_nonneg (pow_nonneg hn m)]
      apply pow_le_pow_left₀ hn
      simpa using Finset.sum_le_sum (s:=Finset.univ) fun i _=>hb v i
  calc
    (∫X,F X^(2*m)∂P)≤∫X,∫Y,(F X-F Y)^(2*m)∂P∂P:=hJ
    _=∫p,H p∂P.prod P:=(integral_prod _ hHi).symm
    _=∫v:Fin N→Ω×Ω,(∑i:Fin N,(Z i (v i).1-Z i (v i).2))^(2*m)∂Q:=hmap.symm
    _≤(6*(m:ℝ))^m*(∫v:Fin N→Ω×Ω,(∑i:Fin N,(Z i (v i).1-Z i (v i).2)^2)^m∂Q):=
      IndependentPairEvenMoment N μ Z hZ m hm hRi
