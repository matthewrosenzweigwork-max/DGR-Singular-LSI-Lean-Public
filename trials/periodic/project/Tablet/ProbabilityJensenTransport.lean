import Tablet.Preamble
import Mathlib.MeasureTheory.Integral.Prod
open MeasureTheory
-- [TABLET NODE: ProbabilityJensenTransport]
theorem ProbabilityJensenTransport {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (η : Measure Y) (ν : Measure Z)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η] [IsProbabilityMeasure ν]
    (S : X×Y→Z) (hS : Measurable S) (hmap : Measure.map S (μ.prod η)=ν)
    (E : Z→ℝ) (A : X→ℝ) (hE : Measurable E) (hA : Measurable A)
    (C β : ℝ) (hβ : 0≤β) (hlower : ∀z,-C≤E z)
    (haverage : ∀x,Integrable (fun y=>E (S (x,y))) η ∧ (∫y,E (S (x,y))∂η)=A x) :
    Integrable (fun x=>Real.exp (-β*A x)) μ ∧
    Integrable (fun z=>Real.exp (-β*E z)) ν ∧
    (∫x,Real.exp (-β*A x)∂μ)≤∫z,Real.exp (-β*E z)∂ν := by
-- BODY
  let F:Z→ℝ:=fun z=>Real.exp (-β*E z)
  have hFm:Measurable F:=Real.measurable_exp.comp (hE.const_mul (-β))
  have hFb (z:Z) : ‖F z‖≤Real.exp (β*C) :=by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hh:=mul_le_mul_of_nonneg_left (hlower z) hβ
    nlinarith
  have hFi:Integrable F ν:=Integrable.of_bound hFm.aestronglyMeasurable _ (Filter.Eventually.of_forall hFb)
  have hFjoint : Integrable (fun p:X×Y=>F (S p)) (μ.prod η):=
    Integrable.of_bound (hFm.comp hS).aestronglyMeasurable _ (Filter.Eventually.of_forall fun p=>hFb _)
  have hsection (x:X) : Integrable (fun y=>F (S (x,y))) η:=
    Integrable.of_bound (hFm.comp (hS.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun y=>hFb _)
  have hJ (x:X) : Real.exp (-β*A x)≤∫y,F (S (x,y))∂η :=by
    have hh:=(convexOn_exp : ConvexOn ℝ Set.univ Real.exp).map_integral_le Real.continuous_exp.continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun _=>Set.mem_univ _) ((haverage x).1.const_mul (-β)) (hsection x)
    rw [integral_const_mul,(haverage x).2] at hh
    exact hh
  have hD (x:X) : (∫y,F (S (x,y))∂η)≤Real.exp (β*C) :=by
    calc
      _≤∫y,Real.exp (β*C)∂η:=by
        apply integral_mono (hsection x) (integrable_const _)
        intro y
        exact (le_abs_self _).trans (hFb _)
      _=Real.exp (β*C):=by simp
  have hAi:Integrable (fun x=>Real.exp (-β*A x)) μ:=by
    apply Integrable.of_bound (Real.measurable_exp.comp (hA.const_mul (-β))).aestronglyMeasurable _
    exact Filter.Eventually.of_forall fun x=>by
      change ‖Real.exp (-β*A x)‖≤Real.exp (β*C)
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact (hJ x).trans (hD x)
  refine ⟨hAi,hFi,?_⟩
  calc
    _≤∫x,∫y,F (S (x,y))∂η∂μ:=integral_mono hAi hFjoint.integral_prod_left hJ
    _=∫p,F (S p)∂μ.prod η:=(integral_prod _ hFjoint).symm
    _=∫z,F z∂ν:=by
      rw [←hmap]
      exact (integral_map hS.aemeasurable (by rw [hmap];exact hFm.aestronglyMeasurable)).symm
