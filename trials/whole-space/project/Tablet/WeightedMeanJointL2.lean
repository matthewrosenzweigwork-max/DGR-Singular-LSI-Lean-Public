module

public import Tablet.WeightedJointRowL2
public import Tablet.WeightedIntegralCauchySchwarz

@[expose] public section
open MeasureTheory Filter Set
open scoped ENNReal
set_option autoImplicit false

-- [TABLET NODE: WeightedMeanJointL2]
theorem WeightedMeanJointL2 {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure α) [IsProbabilityMeasure P] (μ : Measure β) [IsProbabilityMeasure μ]
    (r : α × β → ℝ) (hrm : Measurable r) (hr : ∀ p, 0 ≤ r p ∧ r p ≤ 1)
    (hZ : ∀ x, 0 < ∫ y, r (x,y) ∂μ) (ψ : α × β → ℝ)
    (hψ : MemLp ψ 2 ((P.prod μ).withDensity (fun p => ENNReal.ofReal (r p)))) :
    let m := fun x => (∫ y, r (x,y)*ψ (x,y) ∂μ)/(∫ y, r (x,y) ∂μ)
    MemLp (fun p : α × β => m p.1) 2
      ((P.prod μ).withDensity (fun p => ENNReal.ofReal (r p))) ∧
    Integrable (fun x => (∫ y, r (x,y) ∂μ)*(m x)^2) P := by
-- BODY
  classical
  let J := (P.prod μ).withDensity (fun p => ENNReal.ofReal (r p))
  let Z := fun x => ∫ y, r (x,y) ∂μ
  let T := fun x => ∫ y, r (x,y)*ψ (x,y) ∂μ
  let D := fun x => ∫ y, r (x,y)*(ψ (x,y))^2 ∂μ
  let m := fun x => T x/Z x
  have hw := WeightedJointRowL2 P μ r hrm hr ψ hψ
  have hDi : Integrable D P := hw.2.1.integral_prod_left
  have hZm : AEStronglyMeasurable Z P := hrm.aestronglyMeasurable.integral_prod_right'
  have hTm : AEStronglyMeasurable T P := hw.2.2.1.1
  have hmm : AEStronglyMeasurable m P := hTm.div₀ hZm
  have hri (x : α) : Integrable (fun y => r (x,y)) μ :=
    (integrable_const (1:ℝ)).mono' (hrm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        simpa only [Real.norm_eq_abs,abs_of_nonneg (hr (x,y)).1] using (hr (x,y)).2)
  have hpoint : ∀ᵐ x ∂P, Z x*(m x)^2 ≤ D x := by
    filter_upwards [hw.1.prod_right_ae,hw.2.1.prod_right_ae] with x hx hx2
    have h := WeightedIntegralCauchySchwarz μ (fun y => r (x,y)) (fun y => ψ (x,y))
      (Eventually.of_forall fun y => (hr (x,y)).1) (hri x) hx hx2
    have he : Z x*(m x)^2=(T x)^2/Z x := by
      dsimp [m]
      field_simp
    rw [he]
    apply (div_le_iff₀ (hZ x)).mpr
    simpa only [mul_comm] using h
  have hwi : Integrable (fun x => Z x*(m x)^2) P :=
    hDi.mono' (hZm.mul (hmm.pow 2)) (hpoint.mono fun x hx => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hZ x).le (sq_nonneg _))]
      exact hx)
  have hprod : Integrable (fun p : α × β => r p*(m p.1)^2) (P.prod μ) := by
    apply (integrable_prod_iff (hrm.aestronglyMeasurable.mul (hmm.comp_fst.pow 2))).mpr
    constructor
    · exact Eventually.of_forall fun x => (hri x).mul_const ((m x)^2)
    · have he : (fun x => ∫ y, ‖r (x,y)*(m x)^2‖ ∂μ) = fun x => Z x*(m x)^2 := by
        funext x
        simp_rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hr (x,_)).1 (sq_nonneg _))]
        exact integral_mul_const _ _
      simp only [Pi.mul_apply,Pi.pow_apply]
      rw [he]
      exact hwi
  have hm : Measurable (fun p => ENNReal.ofReal (r p)) := hrm.ennreal_ofReal
  have hfin : ∀ᵐ p ∂P.prod μ, ENNReal.ofReal (r p)<⊤ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hsq : Integrable (fun p : α × β => (m p.1)^2) J := by
    apply (integrable_withDensity_iff_integrable_smul' hm hfin).mpr
    simpa only [ENNReal.toReal_ofReal (hr _).1,smul_eq_mul] using hprod
  exact ⟨(memLp_two_iff_integrable_sq (hmm.comp_fst.mono_ac (withDensity_absolutelyContinuous _ _))).mpr hsq,hwi⟩
