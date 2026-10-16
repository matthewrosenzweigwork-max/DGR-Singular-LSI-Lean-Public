module

public import Tablet.RieszBackgroundConvolutionBounds
public import Tablet.ThermalDensityBounds
public import Tablet.TiltNormalization

@[expose] public section
open MeasureTheory
-- [TABLET NODE: RieszModulatedBackground]
theorem RieszModulatedBackground (d : ℕ) (hd : 2 ≤ d) (s a l u B : ℝ)
    (hs : 0 ≤ s) (hsd : s < (d : ℝ)) (ha : 0 < a)
    (hl : 0 < l) (hl1 : l ≤ 1) (hu1 : 1 ≤ u) (hB : 0 ≤ B) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (ε : ℝ), 0 ≤ ε →
      ∀ (q : BoundedBackground d l u) (β : ℝ), 0 ≤ β → β ≤ B →
      let h := fun x => ∫ y, RieszKernel d s a ε (x-y) * q.density y
      ∃ r : BoundedBackground d (l * Real.exp (-2*B*H)) (u * Real.exp (2*B*H)),
      ∀ x, r.density x = q.density x * Real.exp (β*h x) /
        (∫ y, q.density y * Real.exp (β*h y)) := by
-- BODY
  letI circle_probability : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
    infer_instance
  have hu : 0 < u := lt_of_lt_of_le zero_lt_one hu1
  obtain ⟨c, H, hc, hH, hh⟩ := RieszBackgroundConvolutionBounds d hd s a l u hs hsd ha hu.le
  refine ⟨H, hH, ?_⟩
  intro ε hε q β hβ hβB
  let h := fun x => ∫ y, RieszKernel d s a ε (x-y) * q.density y
  obtain ⟨hhm, _, _, hhb⟩ := hh ε hε q
  have hqn : ∀ᵐ y ∂volume, 0 ≤ q.density y :=
    q.bounds.mono fun y hy => hl.le.trans hy.1
  have hqb : ∀ᵐ y ∂volume, ‖q.density y‖ ≤ u := by
    filter_upwards [q.bounds, hqn] with y hy hn
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    exact hy.2
  have hqi : Integrable q.density volume :=
    (integrable_const (1 : ℝ)).bdd_mul q.measurable.aestronglyMeasurable hqb |>.congr
      (Filter.Eventually.of_forall fun _ => mul_one _)
  have hnH : ∀ᵐ x ∂volume, ‖-h x‖ ≤ H :=
    Filter.Eventually.of_forall fun x => by simpa only [norm_neg,Real.norm_eq_abs] using hhb x
  have hqhi : Integrable (fun x => q.density x * -h x) volume :=
    (hqi.bdd_mul hhm.neg.aestronglyMeasurable hnH).congr
      (Filter.Eventually.of_forall fun x => mul_comm _ _)
  have hmean : (∫ x, q.density x * -h x) ≤ u * (H/u) := by
    have hb : (fun x => q.density x * -h x) ≤ᵐ[volume]
        (fun x => H * q.density x) := by
      filter_upwards [hqn] with x hn
      have hx : -h x ≤ H := by have hx := (abs_le.mp (hhb x)).1; linarith
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hx hn
    have he := integral_mono_ae hqhi (hqi.const_mul H) hb
    rw [integral_const_mul, q.mass, mul_one] at he
    simpa only [mul_div_cancel₀ _ (ne_of_gt hu)] using he
  have hemeas : Measurable (fun x => Real.exp (-β * -h x)) :=
    (hhm.neg.const_mul (-β)).exp
  have heb : ∀ᵐ x ∂volume, ‖Real.exp (-β * -h x)‖ ≤ Real.exp (B*H) := by
    filter_upwards [Filter.Eventually.of_forall hhb] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hxl := (abs_le.mp hx).2
    nlinarith [mul_le_mul_of_nonneg_right hβB hH]
  have hw := hqi.mul_bdd hemeas.aestronglyMeasurable heb
  have hb := ThermalDensityBounds volume q.density (fun x => -h x) β B H l u (H/u) H
      hβ hβB hH hl (div_nonneg hH hu.le) hH q.bounds
      (Filter.Eventually.of_forall fun x => by have hx := (abs_le.mp (hhb x)).2; linarith)
      (Filter.Eventually.of_forall fun x => by simpa only [abs_neg] using hhb x)
      hqi q.mass hqhi hmean hw
  let w := fun x => q.density x * Real.exp (-β * -h x)
  let r := fun x => w x / (∫ y, w y)
  have hrm : Measurable r := (q.measurable.mul hemeas).div_const _
  have hrone : (∫ x, r x) = 1 := by
    dsimp [r]
    rw [integral_div, div_self hb.1.ne']
  have hwp : ∀ᵐ x ∂volume, 0 ≤ w x := hqn.mono fun x hx =>
    mul_nonneg hx (Real.exp_pos _).le
  have hprob := (TiltNormalization volume w (q.measurable.mul hemeas) hwp hw hb.1).1
  have hrb := hb.2.2.2
  have hexplo : Real.exp (-2*B*H) ≤ 1 := Real.exp_le_one_iff.mpr
    (by nlinarith [mul_nonneg hB hH])
  have hexphi : 1 ≤ Real.exp (2*B*H) := Real.one_le_exp_iff.mpr (by positivity)
  have hlo1 : l * Real.exp (-2*B*H) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hexplo hl.le).trans (by simpa using hl1)
  have hhi1 : 1 ≤ u * Real.exp (2*B*H) :=
    hu1.trans (by nlinarith [mul_le_mul_of_nonneg_left hexphi hu.le])
  have hmul : u * (H/u) = H := mul_div_cancel₀ _ (ne_of_gt hu)
  let background : BoundedBackground d (l*Real.exp (-2*B*H)) (u*Real.exp (2*B*H)) := {
    density := r
    measurable := hrm
    lower_pos := mul_pos hl (Real.exp_pos _)
    lower_le_one := hlo1
    one_le_upper := hhi1
    bounds := by
      filter_upwards [hrb] with x hx
      simpa only [hmul, show B*(H+H)=2*B*H by ring] using hx
    mass := hrone }
  refine ⟨background, ?_⟩
  intro x
  dsimp [background, r, w]
  simp only [neg_mul_neg, h]
