module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Tactic
public import Tablet.Preamble

@[expose] public section

open MeasureTheory

-- [TABLET NODE: ConditionalMeanL2Bound]
theorem ConditionalMeanL2Bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (a : ℝ) (ha : 0 < a) (Z M T : Ω → ℝ)
    (hZm : AEStronglyMeasurable Z P) (hMi : Integrable M P) (hTi : Integrable T P)
    (hZ : ∀ᵐ X ∂P, a ≤ Z X ∧ Z X ≤ 1)
    (hCS : ∀ᵐ X ∂P, (M X)^2 ≤ Z X * T X) :
    MemLp (fun X => M X / Z X) 2 P ∧
      Integrable (fun X => (M X)^2 / Z X) P := by
-- BODY
  have hm : AEStronglyMeasurable (fun X => M X / Z X) P :=
    hMi.aestronglyMeasurable.div₀ hZm
  have hbounds : ∀ᵐ X ∂P,
      0 ≤ T X ∧ (M X / Z X)^2 ≤ T X / a ∧ (M X)^2 / Z X ≤ T X := by
    filter_upwards [hZ, hCS] with X hz hcs
    have hzp : 0 < Z X := ha.trans_le hz.1
    have htp : 0 ≤ T X := by
      by_contra h
      have hh := mul_neg_of_pos_of_neg hzp (lt_of_not_ge h)
      nlinarith [sq_nonneg (M X)]
    have hb : (M X)^2 / Z X ≤ T X := (div_le_iff₀ hzp).mpr (by nlinarith [hcs])
    refine ⟨htp, ?_, hb⟩
    calc
      (M X / Z X)^2 = ((M X)^2 / Z X) / Z X := by
        field_simp
        <;> ring
      _ ≤ T X / Z X := div_le_div_of_nonneg_right hb hzp.le
      _ ≤ T X / a := div_le_div_of_nonneg_left htp ha hz.1
  have hsq : Integrable (fun X => (M X / Z X)^2) P := by
    apply (hTi.div_const a).mono' (hm.pow 2)
    filter_upwards [hbounds] with X hx
    change ‖(M X / Z X)^2‖ ≤ T X / a
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (M X / Z X)),
      abs_of_nonneg (div_nonneg hx.1 ha.le)] using hx.2.1
  refine ⟨(memLp_two_iff_integrable_sq hm).mpr hsq, ?_⟩
  apply hTi.mono' ((hMi.aestronglyMeasurable.pow 2).div₀ hZm)
  filter_upwards [hZ, hbounds] with X hz hx
  change ‖(M X)^2 / Z X‖ ≤ T X
  simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1,
    abs_of_nonneg (div_nonneg (sq_nonneg (M X)) (ha.le.trans hz.1))] using hx.2.2
