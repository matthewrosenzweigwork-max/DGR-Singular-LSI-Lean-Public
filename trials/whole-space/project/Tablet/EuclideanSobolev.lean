import Tablet.SobolevExponent
import Tablet.GradientNormIdentity
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
open scoped NNReal

-- [TABLET NODE: EuclideanSobolev]
theorem EuclideanSobolev {ι : Type*} [Fintype ι] (hn : 3 ≤ Fintype.card ι) :
    ∃ C : ℝ≥0, ∀ f : EuclideanSpace ℝ ι → ℝ,
      ContDiff ℝ 1 f → HasCompactSupport f →
      MeasureTheory.eLpNorm f (SobolevExponent (Fintype.card ι) hn) MeasureTheory.volume ≤
        C * MeasureTheory.eLpNorm (EuclideanGradient f) 2 MeasureTheory.volume := by
-- BODY
  let E := EuclideanSpace ℝ ι
  refine ⟨MeasureTheory.eLpNormLESNormFDerivOfEqInnerConst
    (MeasureTheory.volume : MeasureTheory.Measure E) 2, ?_⟩
  intro f hf hs
  have hnorm : MeasureTheory.eLpNorm (fderiv ℝ f) 2 MeasureTheory.volume =
      MeasureTheory.eLpNorm (EuclideanGradient f) 2 MeasureTheory.volume :=
    MeasureTheory.eLpNorm_congr_norm_ae
      (Filter.Eventually.of_forall (fun x => (GradientNormIdentity f x).2.symm))
  rw [← hnorm]
  apply MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq_inner
    (p := (2 : ℝ≥0)) (p' := SobolevExponent (Fintype.card ι) hn)
    MeasureTheory.volume hf hs (by norm_num)
  · simpa [E, finrank_euclideanSpace] using (show 0 < Fintype.card ι by omega)
  · have hn0 : (Fintype.card ι : ℝ) ≠ 0 := by
      exact_mod_cast (show Fintype.card ι ≠ 0 by omega)
    have hn2 : (Fintype.card ι : ℝ) - 2 ≠ 0 := by
      have : (3 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hn
      linarith
    rw [finrank_euclideanSpace]
    change (2 * (Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) - 2))⁻¹ =
      ((2 : ℝ≥0)⁻¹ : ℝ) - (Fintype.card ι : ℝ)⁻¹
    norm_num only [NNReal.coe_inv, NNReal.coe_ofNat]
    field_simp
