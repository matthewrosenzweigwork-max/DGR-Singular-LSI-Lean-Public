import Tablet.ReplacementHaarSwap
import Tablet.BoundedTiltBounds
import Tablet.TiltNormalization
import Mathlib.MeasureTheory.Integral.Prod
open MeasureTheory MeasureTheory.Measure
-- [TABLET NODE: ProductGibbsRowStationarity]
theorem ProductGibbsRowStationarity (d N : ℕ) (W : Configuration d N → ℝ)
    (l u : ℝ) (hl : 0 < l) (hW : Measurable W)
    (hWb : ∀ᵐ X ∂volume, l ≤ W X ∧ W X ≤ u) :
    let P := NormalizedTilt (volume : Measure (Configuration d N)) W
    ∀ (i : Fin N) (F : Configuration d N → ℝ), Measurable F →
      (∃ C : ℝ, ∀ X, |F X| ≤ C) →
      let ν := fun X => NormalizedTilt (volume : Measure (UnitAddTorus (Fin d)))
        (fun z => W (Replacement X i z))
      Integrable (fun X => ∫ z, F (Replacement X i z) ∂ν X) P ∧
      (∫ X, ∫ z, F (Replacement X i z) ∂ν X ∂P) = ∫ X, F X ∂P := by
-- BODY
  classical
  dsimp only
  haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp; infer_instance
  haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := inferInstance
  haveI : IsProbabilityMeasure (volume : Measure (Configuration d N)) := inferInstance
  let M := (volume : Measure (Configuration d N))
  let m := (volume : Measure (UnitAddTorus (Fin d)))
  let P := NormalizedTilt M W
  have hbW := BoundedTiltBounds M W l u hl hW hWb
  have hWi := hbW.1
  let Z := ∫ X, W X ∂M
  have hZ : 0 < Z := hl.trans_le hbW.2.1
  have hu : 0 ≤ u := (hl.le.trans hbW.2.1).trans hbW.2.2.1
  have hWn : ∀ᵐ X ∂M, 0 ≤ W X := hWb.mono fun X hx => hl.le.trans hx.1
  have htn := TiltNormalization M W hW hWn hWi hZ
  haveI : IsProbabilityMeasure P := htn.1
  intro i F hF hFb
  obtain ⟨C,hC⟩ := hFb
  have hC0 : 0 ≤ C := (abs_nonneg (F 0)).trans (hC 0)
  let S : Configuration d N × UnitAddTorus (Fin d) → Configuration d N × UnitAddTorus (Fin d) :=
    fun v => (Replacement v.1 i v.2, v.1 i)
  let μ := M.prod m
  have hS : MeasurePreserving S μ μ := (ReplacementHaarSwap d N i).1
  have hSS (v : Configuration d N × UnitAddTorus (Fin d)) : S (S v) = v := by
    simp [S, Replacement, Function.update_eq_self]
  let R : Configuration d N × UnitAddTorus (Fin d) → ℝ := fun v => W (Replacement v.1 i v.2)
  have hRm : Measurable R := hW.comp (measurable_fst.comp hS.measurable)
  have hRb : ∀ᵐ v ∂μ, l ≤ R v ∧ R v ≤ u :=
    (measurePreserving_fst.comp hS).quasiMeasurePreserving.tendsto_ae hWb
  have hWB : ∀ᵐ v ∂μ, l ≤ W v.1 ∧ W v.1 ≤ u :=
    measurePreserving_fst.quasiMeasurePreserving.tendsto_ae hWb
  let Zi := fun X => ∫ z, R (X,z) ∂m
  have hZm : Measurable Zi := hRm.stronglyMeasurable.integral_prod_right'.measurable
  have hZb : ∀ᵐ X ∂M, l ≤ Zi X ∧ Zi X ≤ u := by
    filter_upwards [ae_ae_of_ae_prod hRb] with X hX
    have hb := BoundedTiltBounds m (fun z => R (X,z)) l u hl
      (hRm.comp (measurable_const.prodMk measurable_id)) hX
    exact ⟨hb.2.1,hb.2.2.1⟩
  have hZB : ∀ᵐ v ∂μ, l ≤ Zi v.1 ∧ Zi v.1 ≤ u :=
    measurePreserving_fst.quasiMeasurePreserving.tendsto_ae hZb
  have hZiS (v : Configuration d N × UnitAddTorus (Fin d)) : Zi (S v).1 = Zi v.1 := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by simp [Zi, R, S, Replacement, Function.update_idem]
  let D := fun v : Configuration d N × UnitAddTorus (Fin d) =>
    W v.1 * R v / (Zi v.1 * Z)
  have hDm : Measurable D := ((hW.comp measurable_fst).mul hRm).div
    ((hZm.comp measurable_fst).mul measurable_const)
  have hDS (v : Configuration d N × UnitAddTorus (Fin d)) : D (S v) = D v := by
    have hRS : R (S v) = W v.1 := by
      have hx := congrArg Prod.fst (hSS v)
      exact congrArg W hx
    dsimp only [D]
    rw [hRS,hZiS]
    change R v * W v.1 / (Zi v.1 * Z) = W v.1 * R v / (Zi v.1 * Z)
    rw [mul_comm]
  have hDb : ∀ᵐ v ∂μ, ‖D v‖ ≤ u * u / (l * Z) := by
    filter_upwards [hWB,hRb,hZB] with v hWv hRv hZv
    have hWp := hl.le.trans hWv.1
    have hRp := hl.le.trans hRv.1
    have hZvp := hl.trans_le hZv.1
    have hDn : 0 ≤ D v := div_nonneg (mul_nonneg hWp hRp) (mul_pos hZvp hZ).le
    change ‖W v.1 * R v / (Zi v.1 * Z)‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg hDn]
    apply (div_le_div_of_nonneg_right (mul_le_mul hWv.2 hRv.2 hRp hu) (mul_pos hZvp hZ).le).trans
    exact div_le_div_of_nonneg_left (mul_nonneg hu hu) (mul_pos hl hZ)
      (mul_le_mul_of_nonneg_right hZv.1 hZ.le)
  have hrawi : Integrable (fun v => D v * F (Replacement v.1 i v.2)) μ := by
    apply Integrable.of_bound (hDm.mul (hF.comp (measurable_fst.comp hS.measurable))).aestronglyMeasurable
      (u * u / (l * Z) * C)
    filter_upwards [hDb] with v hv
    change ‖D v * F (Replacement v.1 i v.2)‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul hv (by simpa only [Real.norm_eq_abs] using hC (Replacement v.1 i v.2))
      (norm_nonneg _) (by positivity)
  have hlefti : Integrable (fun v => D v * F v.1) μ := by
    apply Integrable.of_bound (hDm.mul (hF.comp measurable_fst)).aestronglyMeasurable
      (u * u / (l * Z) * C)
    filter_upwards [hDb] with v hv
    change ‖D v * F v.1‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul hv (by simpa only [Real.norm_eq_abs] using hC v.1)
      (norm_nonneg _) (by positivity)
  have hswap : (∫ v, D v * F (Replacement v.1 i v.2) ∂μ) = ∫ v, D v * F v.1 ∂μ := by
    have hh := (ReplacementHaarSwap d N i).2 (fun v => D v * F v.1)
    change (∫ v, D (S v) * F (S v).1 ∂μ) = _ at hh
    simp only [hDS] at hh
    exact hh
  let A := fun X => ∫ z, D (X,z) * F (Replacement X i z) ∂m
  let B := fun X => ∫ z, D (X,z) * F X ∂m
  have hAi : Integrable A M := hrawi.integral_prod_left
  have hBi : Integrable B M := hlefti.integral_prod_left
  have hrow : ∀ᵐ X ∂M,
      A X = (W X / Z) * (∫ z, F (Replacement X i z) ∂NormalizedTilt m (fun z => R (X,z))) ∧
      B X = W X / Z * F X := by
    filter_upwards [ae_ae_of_ae_prod hRb,hZb] with X hX hZX
    have hz : 0 < Zi X := hl.trans_le hZX.1
    have hri := (BoundedTiltBounds m (fun z => R (X,z)) l u hl
      (hRm.comp (measurable_const.prodMk measurable_id)) hX).1
    have hfi : Integrable (fun z => F (Replacement X i z) * R (X,z)) m := by
      apply hri.bdd_mul (hF.comp (measurable_fst.comp hS.measurable) |>.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => by
          change ‖F (Replacement X i z)‖ ≤ C
          simpa only [Real.norm_eq_abs] using hC (Replacement X i z))
    have ht := (TiltNormalization m (fun z => R (X,z))
      (hRm.comp (measurable_const.prodMk measurable_id))
      (hX.mono fun z hz => hl.le.trans hz.1) hri hz).2
      (fun z => F (Replacement X i z))
      ((hF.comp (measurable_fst.comp hS.measurable)).comp (measurable_const.prodMk measurable_id)) hfi
    constructor
    · rw [ht.2]
      dsimp [A,D]
      have hh : (fun z => W X * R (X,z) / (Zi X * Z) * F (Replacement X i z)) =
          fun z => (W X / Z / Zi X) * (F (Replacement X i z) * R (X,z)) := by funext z; ring
      rw [hh,integral_const_mul]
      ring
    · dsimp [B,D]
      have hh : (fun z => W X * R (X,z) / (Zi X * Z) * F X) =
          fun z => (W X / Z * F X / Zi X) * R (X,z) := by funext z; ring
      rw [hh,integral_const_mul]
      change W X / Z * F X / Zi X * Zi X = _
      field_simp
  let Q := fun X => ∫ z, F (Replacement X i z) ∂NormalizedTilt m (fun z => R (X,z))
  have hQaem : AEStronglyMeasurable Q M := by
    have hdenm : AEStronglyMeasurable (fun X => W X / Z) M := (hW.div_const Z).aestronglyMeasurable
    have hAem := hAi.aestronglyMeasurable
    have heq : Q =ᵐ[M] fun X => A X / (W X / Z) := by
      filter_upwards [hrow,hWb] with X hX hWX
      rw [hX.1]
      exact (mul_div_cancel_left₀ _ (div_ne_zero (ne_of_gt (hl.trans_le hWX.1)) hZ.ne')).symm
    have hquot : AEStronglyMeasurable (fun X => A X / (W X / Z)) M := by
      convert! hAem.mul ((hW.div_const Z).inv.aestronglyMeasurable) using 1 <;> simp only [div_eq_mul_inv]
    exact hquot.congr (Filter.EventuallyEq.symm heq)
  have hQwi : Integrable (fun X => Q X * W X) M := by
    have hh := hAi.const_mul Z
    apply hh.congr
    filter_upwards [hrow] with X hX
    rw [hX.1]
    dsimp [Q]
    field_simp
  have hQm : AEMeasurable Q M := hQaem.aemeasurable
  have hQtilt : Integrable Q P := by
    unfold P NormalizedTilt
    apply (integrable_withDensity_iff_integrable_smul'
      (hW.div_const Z).ennreal_ofReal (Filter.Eventually.of_forall fun X => ENNReal.ofReal_lt_top)).mpr
    apply (hQwi.div_const Z).congr
    filter_upwards [hWn] with X hX
    rw [ENNReal.toReal_ofReal (div_nonneg hX hZ.le)]
    simp [smul_eq_mul] <;> ring
  have hQint : (∫ X, Q X ∂P) = ∫ X, A X ∂M := by
    unfold P NormalizedTilt
    rw [integral_withDensity_eq_integral_toReal_smul (hW.div_const Z).ennreal_ofReal
      (Filter.Eventually.of_forall fun X => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards [hWn,hrow] with X hX hrowX
    rw [ENNReal.toReal_ofReal (div_nonneg hX hZ.le),hrowX.1]
    dsimp [Q]
  have hFwi : Integrable (fun X => F X * W X) M :=
    hWi.bdd_mul hF.aestronglyMeasurable (Filter.Eventually.of_forall fun X => by simpa only [Real.norm_eq_abs] using hC X)
  have hFint := (htn.2 F hF hFwi).2
  refine ⟨hQtilt, ?_⟩
  change (∫ X, Q X ∂P) = ∫ X, F X ∂P
  rw [hQint, ← integral_prod _ hrawi, hswap, integral_prod _ hlefti]
  rw [integral_congr_ae (hrow.mono fun X hx => hx.2)]
  rw [hFint]
  simp_rw [mul_comm (W _ / Z), ← mul_div_assoc]
  exact integral_div _ _
