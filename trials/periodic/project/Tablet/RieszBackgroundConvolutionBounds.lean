import Tablet.RieszL1Foundation
import Tablet.BoundedDensityConvolutionBound
import Tablet.BoundedBackground
open MeasureTheory
-- [TABLET NODE: RieszBackgroundConvolutionBounds]
theorem RieszBackgroundConvolutionBounds (d : ℕ) (hd : 2 ≤ d)
    (s a l u : ℝ) (hs : 0 ≤ s) (hsd : s < (d : ℝ)) (ha : 0 < a)
    (hu : 0 ≤ u) :
    ∃ c H : ℝ, 0 ≤ c ∧ 0 ≤ H ∧ ∀ (ε : ℝ), 0 ≤ ε →
      ∀ q : BoundedBackground d l u,
      Measurable (fun x => ∫ y, RieszKernel d s a ε (x - y) * q.density y) ∧
      (∀ x, Integrable (fun y => RieszKernel d s a ε (x - y) * q.density y) volume) ∧
      (∀ x, -c ≤ ∫ y, RieszKernel d s a ε (x - y) * q.density y) ∧
      (∀ x, |∫ y, RieszKernel d s a ε (x - y) * q.density y| ≤ H) := by
-- BODY
  obtain ⟨c, hc, hg⟩ := RieszL1Foundation d hd s a hs hsd ha
  let H := u * (∫ y, |RieszKernel d s a 0 y|)
  have hH : 0 ≤ H := mul_nonneg hu (integral_nonneg fun y => abs_nonneg _)
  refine ⟨c, H, hc, hH, ?_⟩
  intro ε hε q
  obtain ⟨hm, hi, _, _, hl, hnorm, _⟩ := hg ε hε
  have hconv := BoundedDensityConvolutionBound d (RieszKernel d s a ε) q.density
    hm hi q.measurable u (q.bounds.mono fun y hy => ⟨q.lower_pos.le.trans hy.1, hy.2⟩)
  have hhi := fun x => (hconv x).1
  have hhb := fun x => (hconv x).2
  have hjoint : Measurable (fun p : UnitAddTorus (Fin d) × UnitAddTorus (Fin d) =>
      RieszKernel d s a ε (p.1-p.2)*q.density p.2) :=
    (hm.comp (measurable_fst.sub measurable_snd)).mul (q.measurable.comp measurable_snd)
  have hhm : Measurable (fun x => ∫ y, RieszKernel d s a ε (x-y)*q.density y) :=
    hjoint.stronglyMeasurable.integral_prod_right'.measurable
  have hqn : ∀ᵐ y ∂volume, 0 ≤ q.density y :=
    q.bounds.mono fun y hy => q.lower_pos.le.trans hy.1
  have hqb : ∀ᵐ y ∂volume, ‖q.density y‖ ≤ u := by
    filter_upwards [q.bounds, hqn] with y hy hn
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    exact hy.2
  have hqi : Integrable q.density volume :=
    (integrable_const (1 : ℝ)).bdd_mul q.measurable.aestronglyMeasurable hqb |>.congr
      (Filter.Eventually.of_forall fun _ => mul_one _)
  refine ⟨hhm, hhi, ?_, ?_⟩
  · intro x
    have hb : (fun y => (-c) * q.density y) ≤ᵐ[volume]
        (fun y => RieszKernel d s a ε (x-y) * q.density y) := by
      filter_upwards [hqn] with y hn
      exact mul_le_mul_of_nonneg_right (hl _) hn
    have hh := integral_mono_ae (hqi.const_mul (-c)) (hhi x) hb
    simpa only [integral_const_mul, q.mass, mul_one] using hh
  · intro x
    exact (hhb x).trans (mul_le_mul_of_nonneg_left hnorm hu)
