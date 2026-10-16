module

public import Tablet.LawVariance
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section
open MeasureTheory Filter Set
open scoped Topology

-- [TABLET NODE: LpVarianceContinuity]
theorem LpVarianceContinuity {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] :
    Continuous (fun f : Lp ℝ 2 P => ProbabilityTheory.variance (f : Ω → ℝ) P) := by
-- BODY
  let one : Lp ℝ 2 P := (memLp_const (1:ℝ)).toLp (fun _ => 1)
  have hmean (f : Lp ℝ 2 P) : inner ℝ f one = ∫ X, f X ∂P := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(memLp_const (1:ℝ) (μ := P)).coeFn_toLp] with X hx
    rw [hx]
    simp
  have hm : Continuous (fun f : Lp ℝ 2 P => ∫ X, f X ∂P) := by
    have hc : Continuous (fun f : Lp ℝ 2 P => inner ℝ f one) := continuous_id.inner continuous_const
    simpa only [hmean] using hc
  have he (f : Lp ℝ 2 P) : ProbabilityTheory.variance (f : Ω → ℝ) P = ‖f‖^2 - (∫ X, f X ∂P)^2 := by
    rw [ProbabilityTheory.variance_eq_sub (Lp.memLp f)]
    change (∫ X, (f X)^2 ∂P) - (∫ X, f X ∂P)^2 = _
    have hsquare : (∫ X, (f X)^2 ∂P) = ‖f‖^2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      simp only [Real.inner_apply, sq]
    rw [hsquare]
  have hc : Continuous (fun f : Lp ℝ 2 P => ‖f‖^2 - (∫ X, f X ∂P)^2) :=
    (continuous_norm.pow 2).sub (hm.pow 2)
  simpa only [he] using hc
