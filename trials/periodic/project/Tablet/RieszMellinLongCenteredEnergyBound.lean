module

public import Tablet.TorusSummableGramCenteredEnergy
public import Tablet.RieszMellinFourier

@[expose] public section
open MeasureTheory
-- [TABLET NODE: RieszMellinLongCenteredEnergyBound]
theorem RieszMellinLongCenteredEnergyBound (d : ℕ) (s a : ℝ)
    (hsd : s < (d : ℝ)) (ha : 0 < a) (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 ≤ ε)
    (M : ℝ) (r : UnitAddTorus (Fin d) → ℝ) (hr : Measurable r)
    (hrb : ∀ᵐx∂volume, 0 ≤ r x ∧ r x ≤ M) (hrmass : ∫x,r x∂volume = 1) :
    ∀N : ℕ, 1 ≤ N → ∀X : Configuration d N,
      -2 * RieszMellinLong d s a δ ε 0 ≤
        CenteredPairEnergy (RieszMellinLong d s a δ ε) r X := by
-- BODY
  haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1:ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
    infer_instance
  haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := inferInstance
  have hri : Integrable r volume := Integrable.of_bound hr.aestronglyMeasurable M
    (hrb.mono fun x hx => by simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2)
  have hF := RieszMellinFourier d s a hsd ha δ ε hδ hε
  have hB := RieszMellinCoefficientBounds d s a hsd ha δ ε hδ hε
  have h := TorusSummableGramCenteredEnergy d (RieszMellinLong d s a δ ε) r hr
    (hrb.mono fun _ hx => hx.1) hri hrmass (RieszMellinCoefficient d s a δ ε)
    (fun k => (hB.2.2 k).1) hF.1 hF.2.1
  rw [hF.2.2.1] at h
  exact h
