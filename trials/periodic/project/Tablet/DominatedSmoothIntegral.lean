module

public import Tablet.Preamble
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section
open MeasureTheory Set Filter
open scoped ContDiff Topology
-- [TABLET NODE: DominatedSmoothIntegral]
theorem DominatedSmoothIntegral
    {E F α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [MeasurableSpace α] (μ : Measure α) (U : Set E) (hU : IsOpen U)
    (f : E → α → F)
    (hf : ∀ᵐ a ∂μ, ContDiff ℝ ∞ (fun x => f x a))
    (hfm : ∀ (n : ℕ) (x : E), x ∈ U →
      AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (fun y => f y a) x) μ)
    (hdom : ∀ (x : E), x ∈ U → ∀ n : ℕ,
      ∃ r : ℝ, 0 < r ∧ ∃ b : α → ℝ, Integrable b μ ∧
        ∀ᵐ a ∂μ, ∀ y ∈ Metric.ball x r,
          ‖iteratedFDeriv ℝ n (fun y => f y a) y‖ ≤ b a) :
    ContDiffOn ℝ ∞ (fun x => ∫ a, f x a ∂μ) U := by
-- BODY
  have dominated_taylor_integral
      (μ : Measure α) (U : Set E) (hU : IsOpen U)
      (f : E → α → F) (p : E → α → FormalMultilinearSeries ℝ E F)
      (hp : ∀ᵐ a ∂μ, HasFTaylorSeriesUpToOn ∞ (fun x => f x a) (fun x => p x a) U)
      (hpm : ∀ (n : ℕ) (x : E), x ∈ U → AEStronglyMeasurable (fun a => p x a n) μ)
      (hdom : ∀ (x : E), x ∈ U → ∀ n : ℕ,
        ∃ r : ℝ, 0 < r ∧ ∃ b : α → ℝ, Integrable b μ ∧
          ∀ᵐ a ∂μ, ∀ y ∈ Metric.ball x r, ‖p y a n‖ ≤ b a) :
      ContDiffOn ℝ ∞ (fun x => ∫ a, f x a ∂μ) U := by
    classical
    have hi (n : ℕ) (x : E) (hx : x ∈ U) : Integrable (fun a => p x a n) μ := by
      rcases hdom x hx n with ⟨r,hr,b,hb,hbound⟩
      exact hb.mono' (hpm n x hx) (hbound.mono fun a ha => ha x (Metric.mem_ball_self hr))
    let q : E → FormalMultilinearSeries ℝ E F := fun x n => ∫ a, p x a n ∂μ
    have hq : HasFTaylorSeriesUpToOn ∞ (fun x => ∫ a, f x a ∂μ) q U := by
      apply (hasFTaylorSeriesUpToOn_top_iff' (le_refl _)).2
      constructor
      · intro x hx
        let L := (continuousMultilinearCurryFin0 ℝ E F).toContinuousLinearEquiv.toContinuousLinearMap
        have hL := L.integral_comp_comm (hi 0 x hx)
        change (∫ a, (p x a 0).curry0 ∂μ) = (q x 0).curry0 at hL
        rw [← hL]
        exact integral_congr_ae (hp.mono fun a ha => ha.zero_eq x hx)
      · intro n x hx
        rcases hdom x hx (n+1) with ⟨r,hr,b,hb,hbound⟩
        let V : Set E := U ∩ Metric.ball x r
        have hV : V ∈ 𝓝 x := inter_mem (hU.mem_nhds hx) (Metric.ball_mem_nhds x hr)
        let e := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) F
        have hmeas : AEStronglyMeasurable (fun a => (p x a (n+1)).curryLeft) μ := by
          exact e.continuous.comp_aestronglyMeasurable (hpm (n+1) x hx)
        have hbounded : ∀ᵐ a ∂μ, ∀ y ∈ V, ‖(p y a (n+1)).curryLeft‖ ≤ b a := by
          filter_upwards [hbound] with a ha y hy
          simpa only [ContinuousMultilinearMap.curryLeft_norm] using ha y hy.2
        have hdiff : ∀ᵐ a ∂μ, ∀ y ∈ V,
            HasFDerivAt (fun y => p y a n) (p y a (n+1)).curryLeft y := by
          filter_upwards [hp] with a ha y hy
          exact (ha.fderivWithin n (ENat.natCast_lt_of_coe_top_le_withTop (le_refl _) n) y hy.1).hasFDerivAt (hU.mem_nhds hy.1)
        have hm : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (fun a => p y a n) μ := by
          filter_upwards [hU.mem_nhds hx] with y hy
          exact hpm n y hy
        have hd := hasFDerivAt_integral_of_dominated_of_fderiv_le
          hV hm (hi n x hx) hmeas hbounded hb hdiff
        have hL := ContinuousLinearEquiv.integral_comp_comm (𝕜 := ℝ) (μ := μ)
          (E := E [×n+1]→L[ℝ] F) (F := E →L[ℝ] (E [×n]→L[ℝ] F)) e.toContinuousLinearEquiv
          (fun a => p x a (n+1))
        change (∫ a, (p x a (n+1)).curryLeft ∂μ) = (q x (n+1)).curryLeft at hL
        rw [hL] at hd
        exact hd.hasFDerivWithinAt
    exact hq.contDiffOn

  apply dominated_taylor_integral μ U hU f
    (fun x a => ftaylorSeries ℝ (fun y => f y a) x)
  · exact hf.mono fun a ha => ha.ftaylorSeries.hasFTaylorSeriesUpToOn U
  · exact hfm
  · exact hdom
