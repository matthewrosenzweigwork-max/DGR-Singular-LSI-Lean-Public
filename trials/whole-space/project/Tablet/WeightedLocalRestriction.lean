import Tablet.Preamble
import Mathlib.MeasureTheory.Function.L2Space
open MeasureTheory Filter Set

-- [TABLET NODE: WeightedLocalRestriction]
theorem WeightedLocalRestriction {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure Ω) (r : Ω → ℝ)
    (K : Set Ω) (hK : MeasurableSet K) (m : ℝ) (hm : 0 < m)
    (hbound : ∀ᵐ x ∂μ, x ∈ K → m ≤ r x) :
    μ.restrict K ≪ μ.withDensity (fun x => ENNReal.ofReal (r x)) ∧
    ∃ T : Lp E 2 (μ.withDensity (fun x => ENNReal.ofReal (r x))) →L[ℝ] Lp E 2 (μ.restrict K),
      ∀ v, T v =ᵐ[μ.restrict K] (v : Ω → E) := by
-- BODY
  have hd : μ.restrict K ≤ ENNReal.ofReal m⁻¹ •
      μ.withDensity (fun x => ENNReal.ofReal (r x)) := by
    rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top, ← withDensity_indicator_one hK]
    apply withDensity_mono
    filter_upwards [hbound] with x hx
    by_cases hX : x ∈ K
    · simp only [Set.indicator_of_mem hX, Pi.one_apply]
      change 1 ≤ ENNReal.ofReal m⁻¹ * ENNReal.ofReal (r x)
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hm.le)]
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal
        ((one_le_inv_mul₀ hm).mpr (hx hX))
    · simp [Set.indicator_of_notMem hX]
  refine ⟨Measure.absolutelyContinuous_of_le_smul hd,
    Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top hd, ?_⟩
  intro v
  exact Lp.coeFn_LpToLpOfMeasureLeSMul _ _ _
