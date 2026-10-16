import Tablet.Preamble
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory
-- [TABLET NODE: ProbabilityExponentialInterpolation]
theorem ProbabilityExponentialInterpolation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : Ω→ℝ) (hE : Measurable E)
    (T C : ℝ) (hT : 0<T) (hC : 1≤C)
    (hi : Integrable (fun x => Real.exp (-T*E x)) μ)
    (hb : (∫x,Real.exp (-T*E x)∂μ)≤C) :
    ∀t : ℝ,0≤t → t≤T → Integrable (fun x => Real.exp (-t*E x)) μ ∧
      (∫x,Real.exp (-t*E x)∂μ)≤C := by
-- BODY
  intro t ht htT
  let θ := t/T
  have hθ : 0≤θ := div_nonneg ht hT.le
  have hθ1 : θ≤1 := (div_le_one hT).mpr htT
  let B := fun x => (1-θ)+θ*Real.exp (-T*E x)
  have hBi : Integrable B μ := (integrable_const _).add (hi.const_mul θ)
  have hpoint : ∀x,Real.exp (-t*E x)≤B x := by
    intro x
    have hh := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (-T*E x))
      (show 0≤1-θ by linarith) hθ (show (1-θ)+θ=1 by ring)
    simp only [smul_eq_mul,Real.exp_zero,mul_one,mul_zero,zero_add] at hh
    have hid : θ*(-T*E x)=-t*E x := by dsimp [θ]; field_simp
    rw [hid] at hh
    exact hh
  have htmeas : Measurable (fun x => Real.exp (-t*E x)) := Real.measurable_exp.comp (measurable_const.mul hE)
  have hti : Integrable (fun x => Real.exp (-t*E x)) μ := hBi.mono' htmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hpoint x)
  refine ⟨hti,?_⟩
  calc
    (∫x,Real.exp (-t*E x)∂μ)≤∫x,B x∂μ := integral_mono hti hBi hpoint
    _=(1-θ)+θ*(∫x,Real.exp (-T*E x)∂μ) := by rw [integral_add (integrable_const _) (hi.const_mul θ),integral_const_mul]; simp
    _≤(1-θ)+θ*C := add_le_add le_rfl (mul_le_mul_of_nonneg_left hb hθ)
    _≤C := by nlinarith only [hC,hθ1]
