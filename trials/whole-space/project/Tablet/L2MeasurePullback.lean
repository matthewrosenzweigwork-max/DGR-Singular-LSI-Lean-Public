import Tablet.Preamble
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
set_option autoImplicit false
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped ContDiff ENNReal
noncomputable section

-- [TABLET NODE: L2MeasurePullback]
noncomputable def L2MeasurePullback {α β F : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (e : α ≃ᵐ β) (μ : Measure α) :
    Lp F 2 (μ.map e) ≃ₗᵢ[ℝ] Lp F 2 μ where
-- BODY
  toFun := Lp.compMeasurePreserving e (e.measurable.measurePreserving μ)
  invFun := Lp.compMeasurePreserving e.symm (e.measurePreserving_symm μ)
  left_inv f := by
    have h := (Lp.compMeasurePreserving_comp_apply f (e.measurable.measurePreserving μ)
      (e.measurePreserving_symm μ)).symm
    simpa only [e.self_comp_symm, Lp.compMeasurePreserving_id_apply] using h
  right_inv f := by
    have h := (Lp.compMeasurePreserving_comp_apply f (e.measurePreserving_symm μ)
      (e.measurable.measurePreserving μ)).symm
    simpa only [e.symm_comp_self, Lp.compMeasurePreserving_id_apply] using h
  map_add' f g := map_add (Lp.compMeasurePreserving e (e.measurable.measurePreserving μ)) f g
  map_smul' c f := (Lp.compMeasurePreservingₗ ℝ e (e.measurable.measurePreserving μ)).map_smul c f
  norm_map' f := Lp.norm_compMeasurePreserving f (e.measurable.measurePreserving μ)
