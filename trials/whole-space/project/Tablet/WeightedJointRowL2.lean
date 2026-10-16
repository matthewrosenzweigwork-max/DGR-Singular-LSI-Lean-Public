import Tablet.WeightedIntegralCauchySchwarz
import Tablet.Preamble
import Mathlib.Tactic
open MeasureTheory Filter Set
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 2000000

-- [TABLET NODE: WeightedJointRowL2]
theorem WeightedJointRowL2 {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
     (P : Measure α) [IsProbabilityMeasure P] (μ : Measure β) [IsProbabilityMeasure μ]
     (r : α × β → ℝ) (hrm : Measurable r) (hr : ∀ p, 0 ≤ r p ∧ r p ≤ 1)
     (ψ : α × β → ℝ)
     (hψ : MemLp ψ 2 ((P.prod μ).withDensity (fun p => ENNReal.ofReal (r p)))) :
     Integrable (fun p => r p*ψ p) (P.prod μ) ∧
     Integrable (fun p => r p*(ψ p)^2) (P.prod μ) ∧
     MemLp (fun x => ∫ y, r (x,y)*ψ (x,y) ∂μ) 2 P ∧
     (∫ x, (∫ y, r (x,y)*ψ (x,y) ∂μ)^2 ∂P) ≤
       ∫ p, (ψ p)^2 ∂((P.prod μ).withDensity (fun p => ENNReal.ofReal (r p))) := by
-- BODY
  classical
  let J := (P.prod μ).withDensity (fun p => ENNReal.ofReal (r p))
  have hJle : J ≤ P.prod μ := by
    have h := withDensity_mono (μ := P.prod μ)
      (Eventually.of_forall fun p => by
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hr p).2)
    simpa only [withDensity_const,one_smul] using h
  have : IsFiniteMeasure J := isFiniteMeasure_of_le (P.prod μ) hJle
  have hm := hrm.ennreal_ofReal
  have hfin : ∀ᵐ p ∂P.prod μ, ENNReal.ofReal (r p) < ⊤ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hi : Integrable (fun p => r p*ψ p) (P.prod μ) := by
    have h := (integrable_withDensity_iff_integrable_smul' hm hfin).mp
      (hψ.integrable (by norm_num))
    simpa only [ENNReal.toReal_ofReal (hr _).1,smul_eq_mul] using h
  have hi2 : Integrable (fun p => r p*(ψ p)^2) (P.prod μ) := by
    have h := (integrable_withDensity_iff_integrable_smul' hm hfin).mp hψ.integrable_sq
    simpa only [ENNReal.toReal_ofReal (hr _).1,smul_eq_mul] using h
  let T := fun x => ∫ y, r (x,y)*ψ (x,y) ∂μ
  let D := fun x => ∫ y, r (x,y)*(ψ (x,y))^2 ∂μ
  have hDi : Integrable D P := hi2.integral_prod_left
  have hTm : AEStronglyMeasurable T P := hi.aestronglyMeasurable.integral_prod_right'
  have hpoint : ∀ᵐ x ∂P, (T x)^2 ≤ D x := by
    filter_upwards [hi.prod_right_ae,hi2.prod_right_ae] with x hx hx2
    have hrx : Measurable (fun y => r (x,y)) := hrm.comp (measurable_const.prodMk measurable_id)
    have hri : Integrable (fun y => r (x,y)) μ :=
      (integrable_const (1:ℝ)).mono' hrx.aestronglyMeasurable
        (Eventually.of_forall fun y => by
          simpa only [Real.norm_eq_abs,abs_of_nonneg (hr (x,y)).1] using (hr (x,y)).2)
    have hu : (∫ y, r (x,y) ∂μ) ≤ 1 := by
      simpa using integral_mono hri (integrable_const (1:ℝ)) (fun y => (hr (x,y)).2)
    have hd : 0 ≤ D x := integral_nonneg fun y => mul_nonneg (hr (x,y)).1 (sq_nonneg _)
    have h := WeightedIntegralCauchySchwarz μ (fun y => r (x,y)) (fun y => ψ (x,y))
      (Eventually.of_forall fun y => (hr (x,y)).1) hri hx hx2
    exact h.trans (by simpa using mul_le_mul_of_nonneg_right hu hd)
  have hTi : Integrable (fun x => (T x)^2) P := hDi.mono' (hTm.pow 2)
    (hpoint.mono fun x hx => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (T x))] using hx)
  refine ⟨hi,hi2,(memLp_two_iff_integrable_sq hTm).mpr hTi,?_⟩
  calc
    (∫ x, (T x)^2 ∂P) ≤ ∫ x, D x ∂P := integral_mono_ae hTi hDi hpoint
    _ = ∫ p, r p*(ψ p)^2 ∂P.prod μ := (integral_prod _ hi2).symm
    _ = ∫ p, (ψ p)^2 ∂J := by
      rw [integral_withDensity_eq_integral_toReal_smul hm hfin]
      simp only [ENNReal.toReal_ofReal (hr _).1,smul_eq_mul]
