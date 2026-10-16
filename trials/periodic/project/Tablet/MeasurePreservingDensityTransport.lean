import Tablet.Preamble
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.Jacobian
open MeasureTheory
open scoped ENNReal
-- [TABLET NODE: MeasurePreservingDensityTransport]
theorem MeasurePreservingDensityTransport {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (η : Measure Y) (F : X→Y) (hF : MeasurePreserving F μ η)
    (ρ : Y→ℝ≥0∞) (hρ : Measurable ρ) :
    Measure.map F (μ.withDensity (ρ ∘ F))=η.withDensity ρ := by
-- BODY
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hF.measurable hs,withDensity_apply _ (hs.preimage hF.measurable),withDensity_apply _ hs]
  rw [←lintegral_indicator (hs.preimage hF.measurable),←lintegral_indicator hs]
  have he : (s.preimage F).indicator (ρ ∘ F)=(s.indicator ρ) ∘ F := by
    funext x
    rfl
  rw [he]
  exact hF.lintegral_comp (hρ.indicator hs)
