import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Tablet.MayerDefect
import Tablet.HeatOperatorBounds
-- [TABLET NODE: MayerRemainderLimit]
theorem MayerRemainderLimit (d : ℕ) (G : UnitAddTorus (Fin d) → ℝ)
    (hG : Measurable G) (hn : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d))), 0 ≤ G x)
    (hi : MeasureTheory.Integrable G (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d)))) :
    (∀ a : ℝ, 0 ≤ a →
      0 ≤ MayerDefect (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d))) G a ∧
      MayerDefect (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d))) G a ≤ a * (∫ x, G x ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d))))) ∧
    Filter.Tendsto (fun a : ℝ => MayerDefect (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d))) G a / a)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    (∀ (ε a : ℝ), 0 < ε → 0 ≤ a →
      MayerDefect (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d))) (HeatSemigroup d ε G) a ≤
        MayerDefect (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d))) G a) := by
-- BODY
  let m : MeasureTheory.Measure (UnitAddTorus (Fin d)) := MeasureTheory.volume
  let r (a z : ℝ) : ℝ := a * z - 1 + Real.exp (-a * z)
  have scalar_bounds (a z : ℝ) (ha : 0 ≤ a) (hz : 0 ≤ z) :
      0 ≤ r a z ∧ r a z ≤ a * z := by
    have haz : 0 ≤ a * z := mul_nonneg ha hz
    have ht := Real.add_one_le_exp (-a * z)
    have he : Real.exp (-a * z) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    dsimp [r]
    constructor <;> linarith
  have hrmeas (a : ℝ) : Measurable (fun x => r a (G x)) :=
    ((measurable_const.mul hG).sub measurable_const).add
      (Real.measurable_exp.comp (measurable_const.mul hG))
  have hrint (a : ℝ) (ha : 0 ≤ a) :
      MeasureTheory.Integrable (fun x => r a (G x)) m := by
    refine (hi.const_mul a).mono' (hrmeas a).aestronglyMeasurable ?_
    filter_upwards [hn] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (scalar_bounds a (G x) ha hx).1]
    exact (scalar_bounds a (G x) ha hx).2
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    change 0 ≤ ∫ x, r a (G x) ∂m ∧
      (∫ x, r a (G x) ∂m) ≤ a * (∫ x, G x ∂m)
    constructor
    · exact MeasureTheory.integral_nonneg_of_ae
        (hn.mono fun x hx => (scalar_bounds a (G x) ha hx).1)
    · rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.integral_mono_ae (hrint a ha) (hi.const_mul a)
        (hn.mono fun x hx => (scalar_bounds a (G x) ha hx).2)
  · have hpos : ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < a := self_mem_nhdsWithin
    have hlim := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := m) (F := fun a x => r a (G x) / a) (f := fun _ => (0 : ℝ)) G
      (Filter.Eventually.of_forall fun a =>
        ((hrmeas a).div_const a).aestronglyMeasurable)
      (hpos.mono fun a ha => hn.mono fun x hx => by
        have h := scalar_bounds a (G x) ha.le hx
        rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg h.1 ha.le)]
        exact (div_le_iff₀ ha).mpr (by simpa [mul_comm] using h.2))
      hi
      (Filter.Eventually.of_forall fun x => by
        have hd := (((hasDerivAt_id (0 : ℝ)).mul_const (G x)).sub_const 1).add
          (((hasDerivAt_id (0 : ℝ)).neg.mul_const (G x)).exp)
        simpa [r, smul_eq_mul, div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero_right)
    simpa only [MeasureTheory.integral_div, MeasureTheory.integral_zero, MayerDefect, r, m] using hlim
  · intro ε a hε ha
    obtain ⟨hpcont, hpnonneg, _, hpmass, _, _⟩ := HeatKernelFacts d ε hε
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hpcont.continuousOn
    have hpbound : ∀ᵐ y ∂m, ‖HeatKernel d ε y‖ ≤ C :=
      Filter.Eventually.of_forall fun y => hC y (Set.mem_univ y)
    have hpint : MeasureTheory.Integrable (HeatKernel d ε) m :=
      MeasureTheory.Integrable.of_bound hpcont.measurable.aestronglyMeasurable C hpbound
    have shifted_nonneg (x : UnitAddTorus (Fin d)) :
        ∀ᵐ y ∂m, 0 ≤ G (x - y) :=
      (MeasureTheory.Measure.measurePreserving_sub_left m x).quasiMeasurePreserving.ae hn
    have shifted_meas (x : UnitAddTorus (Fin d)) : Measurable (fun y => G (x - y)) :=
      hG.comp (measurable_const.sub measurable_id)
    have weighted_int (x : UnitAddTorus (Fin d)) :
        MeasureTheory.Integrable (fun y => HeatKernel d ε y * G (x - y)) m :=
      ((MeasureTheory.integrable_comp_sub_left G x).mpr hi).bdd_mul
        hpcont.measurable.aestronglyMeasurable hpbound
    have hPGnonneg (x : UnitAddTorus (Fin d)) : 0 ≤ HeatSemigroup d ε G x :=
      MeasureTheory.integral_nonneg_of_ae
        ((shifted_nonneg x).mono fun y hy => mul_nonneg (hpnonneg y) hy)
    have weighted_exp_int (x : UnitAddTorus (Fin d)) :
        MeasureTheory.Integrable (fun y => HeatKernel d ε y * Real.exp (-a * G (x - y))) m := by
      refine hpint.mono'
        (hpcont.measurable.mul
          (Real.measurable_exp.comp (measurable_const.mul (shifted_meas x)))).aestronglyMeasurable ?_
      filter_upwards [shifted_nonneg x] with y hy
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (hpnonneg y) (Real.exp_pos _).le)]
      exact mul_le_of_le_one_right (hpnonneg y)
        (Real.exp_le_one_iff.mpr (by nlinarith))
    have tangent (z b : ℝ) :
        Real.exp (-a * b) * (1 - a * (z - b)) ≤ Real.exp (-a * z) := by
      calc
        Real.exp (-a * b) * (1 - a * (z - b)) =
            Real.exp (-a * b) * (-a * (z - b) + 1) := by ring
        _ ≤ Real.exp (-a * b) * Real.exp (-a * (z - b)) :=
          mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (Real.exp_pos _).le
        _ = Real.exp (-a * b + -a * (z - b)) := (Real.exp_add _ _).symm
        _ = Real.exp (-a * z) := by congr 1; ring
    have jensen (x : UnitAddTorus (Fin d)) :
        Real.exp (-a * HeatSemigroup d ε G x) ≤
          HeatSemigroup d ε (fun z => Real.exp (-a * G z)) x := by
      let b := HeatSemigroup d ε G x
      let e := Real.exp (-a * b)
      have hlow : MeasureTheory.Integrable (fun y =>
          e * (1 + a * b) * HeatKernel d ε y -
            (a * e) * (HeatKernel d ε y * G (x - y))) m :=
        (hpint.const_mul (e * (1 + a * b))).sub ((weighted_int x).const_mul (a * e))
      have hmono := MeasureTheory.integral_mono_ae hlow (weighted_exp_int x)
        (Filter.Eventually.of_forall fun y => by
          calc
            e * (1 + a * b) * HeatKernel d ε y -
                (a * e) * (HeatKernel d ε y * G (x - y)) =
                HeatKernel d ε y * Real.exp (-a * b) * (1 - a * (G (x - y) - b)) := by
                  dsimp [e]
                  ring
            _ ≤ HeatKernel d ε y * Real.exp (-a * G (x - y)) := by
              simpa only [mul_assoc] using
                mul_le_mul_of_nonneg_left (tangent (G (x - y)) b) (hpnonneg y))
      have hloweq : (∫ y, (e * (1 + a * b) * HeatKernel d ε y -
          (a * e) * (HeatKernel d ε y * G (x - y))) ∂m) = e := by
        rw [MeasureTheory.integral_sub
          (hpint.const_mul (e * (1 + a * b))) ((weighted_int x).const_mul (a * e)),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hpmass]
        change e * (1 + a * b) * 1 - (a * e) * b = e
        ring
      rw [hloweq] at hmono
      exact hmono
    have hPG := HeatOperatorBounds d ε hε G hG hi
    have hPr := HeatOperatorBounds d ε hε (fun x => r a (G x)) (hrmeas a) (hrint a ha)
    have hpoint (x : UnitAddTorus (Fin d)) :
        r a (HeatSemigroup d ε G x) ≤ HeatSemigroup d ε (fun z => r a (G z)) x := by
      have heq : HeatSemigroup d ε (fun z => r a (G z)) x =
          a * HeatSemigroup d ε G x - 1 +
            HeatSemigroup d ε (fun z => Real.exp (-a * G z)) x := by
        have halg : (fun y => HeatKernel d ε y * r a (G (x - y))) =
            (fun y => a * (HeatKernel d ε y * G (x - y)) - HeatKernel d ε y +
              HeatKernel d ε y * Real.exp (-a * G (x - y))) := by
          funext y
          dsimp [r]
          ring
        have hsub : MeasureTheory.Integrable (fun y =>
            a * (HeatKernel d ε y * G (x - y)) - HeatKernel d ε y) m :=
          ((weighted_int x).const_mul a).sub hpint
        unfold HeatSemigroup
        rw [halg, MeasureTheory.integral_add hsub (weighted_exp_int x),
          MeasureTheory.integral_sub ((weighted_int x).const_mul a) hpint,
          MeasureTheory.integral_const_mul, hpmass]
      rw [heq]
      dsimp [r]
      linarith [jensen x]
    have hPHint : MeasureTheory.Integrable
        (fun x => r a (HeatSemigroup d ε G x)) m := by
      refine (hPG.2.1.const_mul a).mono' ?_ ?_
      · exact (((measurable_const.mul hPG.1).sub measurable_const).add
          (Real.measurable_exp.comp (measurable_const.mul hPG.1))).aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg
            (scalar_bounds a (HeatSemigroup d ε G x) ha (hPGnonneg x)).1]
          exact (scalar_bounds a (HeatSemigroup d ε G x) ha (hPGnonneg x)).2
    change (∫ x, r a (HeatSemigroup d ε G x) ∂m) ≤ ∫ x, r a (G x) ∂m
    rw [← hPr.2.2.1]
    exact MeasureTheory.integral_mono_ae hPHint hPr.2.1
      (Filter.Eventually.of_forall hpoint)
