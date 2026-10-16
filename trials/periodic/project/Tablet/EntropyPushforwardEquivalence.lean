import Tablet.Entropy
open MeasureTheory
universe u v
-- [TABLET NODE: EntropyPushforwardEquivalence]
theorem EntropyPushforwardEquivalence {X:Type u}{Y:Type v}[MeasurableSpace X][MeasurableSpace Y]
    (μ:Measure X)(e:X≃ᵐY)(f:Y→ℝ) :
    Entropy (μ.map e) f=Entropy μ (f∘e) := by
-- BODY
  unfold Entropy
  rw[integral_map_equiv e (fun y=>f y*Real.log (f y)),integral_map_equiv e f]
  rfl
