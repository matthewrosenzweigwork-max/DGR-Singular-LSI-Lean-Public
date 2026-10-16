module

public import Tablet.SobolevExponent
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Tactic

@[expose] public section
open MeasureTheory Set Filter
open scoped ENNReal NNReal
set_option maxHeartbeats 800000

namespace CriticalNormControls
private theorem square_holder {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (ψ : α → ℝ) (p : ℝ) (hp : 2 < p)
    (hψ : MemLp (fun x => ψ x^2) (ENNReal.ofReal (p/2)) μ)
    (S : Set α) (hS : MeasurableSet S) (hfinite : μ S ≠ ∞) :
    (∫ x in S, ψ x^2 ∂μ) ≤
      (∫ x, |ψ x|^p ∂μ)^(2/p)*(μ.real S)^(1-2/p) := by
  have hp0 : 0 < p := by linarith
  have hpm : 0 < p-2 := by linarith
  have hpq : (p/2).HolderConjugate (p/(p-2)) := by
    apply Real.holderConjugate_iff.mpr
    refine ⟨by linarith, ?_⟩
    field_simp
    ring
  have hi : MemLp (S.indicator (fun _ : α => (1 : ℝ)))
      (ENNReal.ofReal (p/(p-2))) μ :=
    memLp_indicator_const _ hS _ (Or.inr hfinite)
  have hin : 0 ≤ᵐ[μ] S.indicator (fun _ : α => (1 : ℝ)) :=
    Eventually.of_forall (fun x => by simp only [Set.indicator]; split_ifs <;> norm_num)
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Eventually.of_forall (fun x => sq_nonneg (ψ x))) hin hψ hi
  have he : (fun x => ψ x^2*S.indicator (fun _ : α => (1 : ℝ)) x) =
      S.indicator (fun x => ψ x^2) := by
    funext x
    simp only [Set.indicator]
    split_ifs <;> simp
  have hexp : 1/(p/2) = 2/p := by field_simp
  have hexp' : 1/(p/(p-2)) = 1-2/p := by field_simp
  have hipow : (fun x => (S.indicator (fun _ : α => (1 : ℝ)) x)^(p/(p-2))) =
      S.indicator (fun _ : α => (1 : ℝ)) := by
    funext x
    simp only [Set.indicator]
    split_ifs <;> simp [Real.zero_rpow (ne_of_gt (div_pos hp0 hpm))]
  rw [he, integral_indicator hS, hipow, integral_indicator hS, setIntegral_const,
    smul_eq_mul, mul_one, hexp, hexp'] at h
  have hsquare (x : ℝ) : (x^2)^(p/2) = |x|^p := by
    rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg x)]
    congr 1
    ring
  simpa only [hsquare] using h
end CriticalNormControls

-- [TABLET NODE: CriticalNormControls]
theorem CriticalNormControls {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (p : ℝ≥0) (hp : 2 < (p : ℝ))
    (T : ℝ≥0∞) (hT : T < ⊤) (ψ : α → ℝ)
    (hψ : AEStronglyMeasurable ψ μ) (hcap : eLpNorm ψ p μ ≤ T) :
    Integrable (fun x => |ψ x|^(p : ℝ)) μ ∧
    MemLp (fun x => ψ x^2) (ENNReal.ofReal ((p : ℝ)/2)) μ ∧
    (∫ x, |ψ x|^(p : ℝ) ∂μ) ≤ T.toReal^(p : ℝ) ∧
    (∀ S : Set α, MeasurableSet S → μ S ≠ ⊤ →
      (∫ x in S, ψ x^2 ∂μ) ≤
        (T.toReal^(p : ℝ))^(2/(p : ℝ))*(μ.real S)^(1-2/(p : ℝ))) := by
-- BODY
  have hp' : 0 < (p : ℝ) := by linarith
  have hp0 : p ≠ 0 := by exact_mod_cast hp'.ne'
  have hpE : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast hp0
  have hmem : MemLp ψ p μ := hcap.trans_lt hT
  have hi : Integrable (fun x => |ψ x|^(p : ℝ)) μ := by
    simpa only [ENNReal.coe_toReal, Real.norm_eq_abs] using
      (integrable_norm_rpow_iff hψ hpE ENNReal.coe_ne_top).2 hmem
  have hsquare := hmem.norm_rpow_div 2
  have hsq : MemLp (fun x => ψ x^2) (ENNReal.ofReal ((p : ℝ)/2)) μ := by
    have heq : ENNReal.ofReal ((p : ℝ)/2) = (p : ℝ≥0∞)/2 := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      simp only [ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_ofNat]
    rw [heq]
    simpa [Real.rpow_natCast, Real.norm_eq_abs] using hsquare
  have H := ENNReal.rpow_le_rpow hcap hp'.le
  rw [eLpNorm_nnreal_pow_eq_lintegral hp0 hψ] at H
  have heq : (∫⁻ x, ‖ψ x‖ₑ^(p : ℝ) ∂μ) =
      ENNReal.ofReal (∫ x, |ψ x|^(p : ℝ) ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall (fun x => Real.rpow_nonneg (abs_nonneg _) _))]
    congr 1
    ext x
    rw [← ofReal_norm, Real.norm_eq_abs,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp'.le]
  rw [heq, ← ENNReal.ofReal_toReal hT.ne,
    ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp'.le] at H
  have hbound : (∫ x, |ψ x|^(p : ℝ) ∂μ) ≤ T.toReal^(p : ℝ) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp H
  refine ⟨hi, hsq, hbound, ?_⟩
  intro S hS hfinite
  apply (CriticalNormControls.square_holder μ ψ p hp hsq S hS hfinite).trans
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (integral_nonneg (fun _ => Real.rpow_nonneg (abs_nonneg _) _))
      hbound (by positivity)) (by positivity)
