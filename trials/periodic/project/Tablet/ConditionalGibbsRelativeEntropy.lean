import Tablet.BoundedGibbsRelativeEntropy
import Tablet.BoundedTiltBounds
import Tablet.TiltNormalization
import Mathlib.MeasureTheory.Integral.Prod
open MeasureTheory InformationTheory

-- [TABLET NODE: ConditionalGibbsRelativeEntropy]
theorem ConditionalGibbsRelativeEntropy {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (T : Measure (X × Y)) [IsProbabilityMeasure T]
    (η : Measure Y) [IsProbabilityMeasure η]
    (U : X × Y → ℝ) (hU : Measurable U) (C : ℝ) (hC : ∀ p, |U p| ≤ C)
    (hT : klDiv T (T.fst.prod η) ≠ ⊤) :
    let z := fun x => ∫ y, Real.exp (-U (x,y)) ∂η
    let R := (T.fst.prod η).withDensity (fun p => ENNReal.ofReal (Real.exp (-U p) / z p.1))
    (∀ x, 0 < z x ∧ Real.exp (-C) ≤ z x ∧ z x ≤ Real.exp C) ∧
      IsProbabilityMeasure R ∧ klDiv T R ≠ ⊤ ∧
      (klDiv T R).toReal = (klDiv T (T.fst.prod η)).toReal +
        (∫ p, U p ∂T) + ∫ p, Real.log (z p.1) ∂T := by
-- BODY
  let z := fun x => ∫ y, Real.exp (-U (x,y)) ∂η
  have hb (x : X) : Integrable (fun y => Real.exp (-U (x,y))) η ∧
      Real.exp (-C) ≤ z x ∧ z x ≤ Real.exp C := by
    have hm : Measurable (fun y => Real.exp (-U (x,y))) :=
      (hU.comp (measurable_const.prodMk measurable_id)).neg.exp
    have he : ∀ᵐ y ∂η, Real.exp (-C) ≤ Real.exp (-U (x,y)) ∧ Real.exp (-U (x,y)) ≤ Real.exp C := by
      exact Filter.Eventually.of_forall fun y =>
        ⟨Real.exp_le_exp.mpr (by have := (abs_le.mp (hC (x,y))).2; linarith),
         Real.exp_le_exp.mpr (by have := (abs_le.mp (hC (x,y))).1; linarith)⟩
    obtain ⟨hi,hlo,hhi,_⟩ := BoundedTiltBounds η _ (Real.exp (-C)) (Real.exp C) (Real.exp_pos _) hm he
    exact ⟨hi,hlo,hhi⟩
  have hz (x : X) : 0 < z x := (Real.exp_pos (-C)).trans_le (hb x).2.1
  have hmz : Measurable z := hU.neg.exp.stronglyMeasurable.integral_prod_right'.measurable
  let W := fun p : X × Y => U p + Real.log (z p.1)
  have hmW : Measurable W := hU.add (hmz.comp measurable_fst).log
  have hlog (x : X) : |Real.log (z x)| ≤ C := by
    apply abs_le.mpr
    constructor
    · have hh := Real.log_le_log (Real.exp_pos (-C)) (hb x).2.1
      simpa only [Real.log_exp] using hh
    · have hh := Real.log_le_log (hz x) (hb x).2.2
      simpa only [Real.log_exp] using hh
  have hW : ∀ p, |W p| ≤ C+C := fun p =>
    (abs_add_le _ _).trans (add_le_add (hC p) (hlog p.1))
  have hex (p : X × Y) : Real.exp (-W p) = Real.exp (-U p) / z p.1 := by
    dsimp [W]
    rw [neg_add, Real.exp_add, Real.exp_neg (Real.log (z p.1)), Real.exp_log (hz p.1), div_eq_mul_inv]
  have hi : Integrable (fun p => Real.exp (-W p)) (T.fst.prod η) := by
    apply (integrable_const (Real.exp (C+C))).mono' hmW.neg.exp.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      change -W p ≤ C+C
      have hh := (abs_le.mp (hW p)).1
      linarith
  have hnorm : (∫ p, Real.exp (-W p) ∂T.fst.prod η) = 1 := by
    rw [integral_prod _ hi]
    have hf : ∀ x, (∫ y, Real.exp (-W (x,y)) ∂η) = 1 := by
      intro x
      simp_rw [hex]
      rw [integral_div]
      exact div_self (hz x).ne'
    simp_rw [hf]
    simp
  have heq : NormalizedTilt (T.fst.prod η) (fun p => Real.exp (-W p)) =
      (T.fst.prod η).withDensity (fun p => ENNReal.ofReal (Real.exp (-U p) / z p.1)) := by
    unfold NormalizedTilt
    rw [hnorm]
    simp only [div_one, hex]
  obtain ⟨_,hp,hfin,he⟩ := BoundedGibbsRelativeEntropy (T.fst.prod η) T W hmW (C+C) hW hT
  rw [heq] at hp hfin he
  have hii : Integrable U T := by
    apply (integrable_const C).mono' hU.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hC p
  have hli : Integrable (fun p : X × Y => Real.log (z p.1)) T := by
    apply (integrable_const C).mono' ((hmz.comp measurable_fst).log).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs, Function.comp_apply] using hlog p.1
  refine ⟨fun x => ⟨hz x, (hb x).2⟩, hp, hfin, ?_⟩
  rw [he, hnorm, Real.log_one, add_zero]
  dsimp only [W]
  rw [integral_add hii hli]
  ring
