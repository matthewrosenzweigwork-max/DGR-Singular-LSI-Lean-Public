import Tablet.RieszThermalEulerLagrange
import Tablet.ProbabilityConvolutionJensenInputs
import Tablet.BoundedDensityConvolutionBound
import Tablet.ThermalDensityBounds
import Tablet.BoundedTiltBounds
import Tablet.TiltNormalization
import Tablet.BoundedBackground
open MeasureTheory UnitAddTorus
open scoped Topology

-- [TABLET NODE: RieszThermalReferenceUniform]
theorem RieszThermalReferenceUniform (d : ℕ) (hd : 2 ≤ d) (s a : ℝ)
    (hs : 0 ≤ s) (hsd : s < (d : ℝ)) (ha : 0 < a) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ B : ℝ, 0 ≤ B →
      ∀ qlo qhi : ℝ, ∀ q : BoundedBackground d qlo qhi,
      let G := ∫ x, |RieszKernel d s a 0 x| ∂(volume : Measure (UnitAddTorus (Fin d)))
      let M := qhi*Real.exp (B*(c+qhi*G))
      let H := M*G
      ∀ ε β : ℝ, 0 < ε → 0 ≤ β → β ≤ B →
      ∃ r : BoundedBackground d (qlo*Real.exp (-2*B*H)) M,
        (∀ x, |∫ y, RieszKernel d s a ε (x-y)*r.density y| ≤ H) ∧
        (∀ᵐ x ∂volume, r.density x = q.density x*Real.exp (-β*(∫ y, RieszKernel d s a ε (x-y)*r.density y)) /
          (∫ z, q.density z*Real.exp (-β*(∫ y, RieszKernel d s a ε (z-y)*r.density y)))) := by
-- BODY
  classical
  letI : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
    ⟨by rw [AddCircle.volume_eq_smul_haarAddCircle]; simp⟩
  obtain ⟨c, hc, hf⟩ := RieszL1Foundation d hd s a hs hsd ha
  refine ⟨c, hc, ?_⟩
  intro B hB qlo qhi q
  dsimp only
  let G := ∫ x, |RieszKernel d s a 0 x| ∂(volume : Measure (UnitAddTorus (Fin d)))
  let M := qhi*Real.exp (B*(c+qhi*G))
  let H := M*G
  have hG : 0 ≤ G := integral_nonneg fun x => abs_nonneg _
  have hqhi : 0 ≤ qhi := zero_le_one.trans q.one_le_upper
  have hM : 1 ≤ M := by
    have he : 1 ≤ Real.exp (B*(c+qhi*G)) := Real.one_le_exp_iff.mpr (by positivity)
    exact q.one_le_upper.trans (by dsimp [M]; nlinarith)
  have hH : 0 ≤ H := mul_nonneg (zero_le_one.trans hM) hG
  have hlowp : 0 < qlo*Real.exp (-2*B*H) := mul_pos q.lower_pos (Real.exp_pos _)
  have hlowl : qlo*Real.exp (-2*B*H) ≤ 1 := by
    have he : Real.exp (-2*B*H) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    exact (mul_le_mul_of_nonneg_left he q.lower_pos.le).trans (by simpa using q.lower_le_one)
  intro ε β hε hβ hβB
  obtain ⟨C, L, hC, _, hgb, ρ, hρm, hρi, hρmass, hρb, _, hρEL⟩ :=
    RieszThermalEulerLagrange d hd s a ε β hs hsd ha hε hβ q.density qlo qhi q.lower_pos q.measurable q.bounds
  let h := fun x => ∫ y, RieszKernel d s a ε (x-y)*ρ y
  have hfund := hf ε hε.le
  have hqn : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), 0 ≤ q.density x ∧ q.density x ≤ qhi :=
    q.bounds.mono fun x hx => ⟨q.lower_pos.le.trans hx.1, hx.2⟩
  have hin := ProbabilityConvolutionJensenInputs d (RieszKernel d s a ε) q.density ρ
    hfund.1 hfund.2.1 q.measurable hρm qhi C c hqn hqhi hgb hfund.2.2.2.2.1 hρi
    (hρb.mono fun _ hx => hx.1.le) hρmass
  have hmean : (∫ x, q.density x*h x) ≤ qhi*G :=
    hin.2.2.2.trans (mul_le_mul_of_nonneg_left hfund.2.2.2.2.2.1 hqhi)
  have hqi := (BoundedTiltBounds volume q.density qlo qhi q.lower_pos q.measurable q.bounds).1
  have hqh : Integrable (fun x => q.density x * h x) volume := hin.2.2.1
  have hemeas : Measurable (fun x => Real.exp (-β * h x)) := (hin.1.const_mul (-β)).exp
  have heb : ∀ᵐ x ∂volume, ‖Real.exp (-β * h x)‖ ≤ Real.exp (B*C) := by
    filter_upwards [Filter.Eventually.of_forall fun x => (hin.2.1 x).2.2] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hxl := (abs_le.mp hx).1
    nlinarith [mul_le_mul_of_nonneg_right hβB hC.le]
  have hw := hqi.mul_bdd hemeas.aestronglyMeasurable heb
  have hb₁ := ThermalDensityBounds volume q.density h β B c qlo qhi G C
    hβ hβB hc q.lower_pos hG hC.le q.bounds
    (Filter.Eventually.of_forall fun x => (hin.2.1 x).2.1)
    (Filter.Eventually.of_forall fun x => (hin.2.1 x).2.2) hqi q.mass hqh hmean hw
  have hwpos : ∀ᵐ x ∂volume, 0 ≤ q.density x * Real.exp (-β*h x) :=
    q.bounds.mono fun x hx => mul_nonneg (q.lower_pos.le.trans hx.1) (Real.exp_pos _).le
  have hprob := (TiltNormalization volume _ (q.measurable.mul hemeas) hwpos hw hb₁.1).1
  have hmass : (∫ x, q.density x * Real.exp (-β*h x) /
      (∫ y, q.density y * Real.exp (-β*h y))) = 1 := by
    rw [integral_div, div_self hb₁.1.ne']
  have hρM : ∀ᵐ x ∂volume, 0 ≤ ρ x ∧ ρ x ≤ M := by
    filter_upwards [hρEL, hb₁.2.2.2, hρb] with x hx hy hz
    exact ⟨hz.1.le, hx ▸ hy.2⟩
  have hbound : ∀ x, |h x| ≤ H := by
    intro x
    have hh := (BoundedDensityConvolutionBound d (RieszKernel d s a ε) ρ hfund.1 hfund.2.1 hρm M hρM x).2
    exact hh.trans (mul_le_mul_of_nonneg_left hfund.2.2.2.2.2.1 (zero_le_one.trans hM))
  have hb₂ := ThermalDensityBounds volume q.density h β B c qlo qhi G H
    hβ hβB hc q.lower_pos hG hH q.bounds
    (Filter.Eventually.of_forall fun x => (hin.2.1 x).2.1)
    (Filter.Eventually.of_forall hbound) hqi q.mass hqh hmean hw
  have hbounds : ∀ᵐ x ∂volume, qlo*Real.exp (-2*B*H) ≤ ρ x ∧ ρ x ≤ M := by
    filter_upwards [hρEL, hb₂.2.2.2] with x hx hy
    simpa only [hx] using hy
  let r : BoundedBackground d (qlo*Real.exp (-2*B*H)) M :=
    ⟨ρ, hρm, hlowp, hlowl, hM, hbounds, hρmass⟩
  exact ⟨r, hbound, hρEL⟩
