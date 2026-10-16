import Tablet.HeatKernelFacts
import Tablet.HeatSourceDensity
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Group.Integral
open MeasureTheory
-- [TABLET NODE: HeatSourceRegularity]
theorem HeatSourceRegularity (d : ℕ) (ε : ℝ) (hε : 0 < ε)
    (μ : Measure (UnitAddTorus (Fin d))) [IsFiniteMeasure μ] :
    Continuous (HeatSourceDensity d ε μ) ∧
      (∀ x, 0 ≤ HeatSourceDensity d ε μ x) ∧
      Integrable (HeatSourceDensity d ε μ) volume ∧
      (∫ x, HeatSourceDensity d ε μ x) = μ.real Set.univ := by
-- BODY
  classical
  let T := UnitAddTorus (Fin d)
  let p := HeatKernel d ε
  have hpc : Continuous p := (HeatKernelFacts d ε hε).1
  have hpn : ∀ x, 0 ≤ p x := (HeatKernelFacts d ε hε).2.1
  have hpm : (∫ x, p x) = 1 := (HeatKernelFacts d ε hε).2.2.2.1
  obtain ⟨C,hC⟩ := (isCompact_univ : IsCompact (Set.univ : Set T)).exists_bound_of_continuousOn hpc.continuousOn
  have hpbound : ∀ x, ‖p x‖ ≤ C := fun x => hC x (Set.mem_univ x)
  have hpjoint : Continuous (fun v : T × T => p (v.1-v.2)) :=
    hpc.comp (continuous_fst.sub continuous_snd)
  have hpi : Integrable (fun v : T × T => p (v.1-v.2)) (volume.prod μ) :=
    Integrable.of_bound hpjoint.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun v => hpbound _)
  have hc : Continuous (fun x : T => ∫ y, p (x-y) ∂μ) :=
    continuous_of_dominated
      (fun _ => (hpc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (fun _ => Filter.Eventually.of_forall fun _ => hpbound _)
      (integrable_const C) (Filter.Eventually.of_forall fun _ =>
        hpc.comp (continuous_id.sub continuous_const))
  refine ⟨hc, fun _ => integral_nonneg (fun _ => hpn _), hpi.integral_prod_left, ?_⟩
  change (∫ x, (∫ y, p (x-y) ∂μ)) = μ.real Set.univ
  rw [integral_integral_swap hpi]
  simp_rw [integral_sub_right_eq_self, hpm]
  simp [measureReal_def]
