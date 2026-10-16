import Tablet.BoundedBackground
open MeasureTheory
-- [TABLET NODE: ExternalPotentialBackground]
theorem ExternalPotentialBackground (d : ℕ)
    (V : UnitAddTorus (Fin d) → ℝ) (hV : Measurable V)
    (A L B β : ℝ) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hβ : 0 ≤ β) (hβB : β ≤ B)
    (hbounds : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))),
      A ≤ V x ∧ V x ≤ A + L) :
    0 < (∫ y, Real.exp (-β * V y)) ∧
    ∃ q : BoundedBackground d (Real.exp (-B * L)) (Real.exp (B * L)),
      ∀ x, q.density x = Real.exp (-β * V x) / (∫ y, Real.exp (-β * V y)) := by
-- BODY
  haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
    infer_instance
  haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := by
    infer_instance
  let w : UnitAddTorus (Fin d) → ℝ := fun x => Real.exp (-β * (V x - A))
  let Z : ℝ := ∫ x, w x
  have hwm : Measurable w := (hV.sub_const A).const_mul (-β) |>.exp
  have hw : ∀ᵐ x ∂volume, Real.exp (-B * L) ≤ w x ∧ w x ≤ 1 := by
    filter_upwards [hbounds] with x hx
    have hlower : -B * L ≤ -β * (V x - A) := by
      have h := mul_le_mul_of_nonneg_left (show V x - A ≤ L by linarith) hβ
      have hb := mul_le_mul_of_nonneg_right hβB hL
      nlinarith
    exact ⟨Real.exp_le_exp.mpr hlower,
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ)
        (sub_nonneg.mpr hx.1))⟩
  have hwi : Integrable w volume := (integrable_const (1 : ℝ)).mono'
    hwm.aestronglyMeasurable (hw.mono fun x hx => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hx.2)
  have hZlo : Real.exp (-B * L) ≤ Z := by
    simpa [Z] using integral_mono_ae (integrable_const (Real.exp (-B * L))) hwi
      (hw.mono fun _ hx => hx.1)
  have hZhi : Z ≤ 1 := by
    simpa [Z] using integral_mono_ae hwi (integrable_const (1 : ℝ))
      (hw.mono fun _ hx => hx.2)
  have hZ : 0 < Z := (Real.exp_pos _).trans_le hZlo
  have hlo : 0 < Real.exp (-B * L) := Real.exp_pos _
  have hlo1 : Real.exp (-B * L) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hB) hL)
  have hhi1 : 1 ≤ Real.exp (B * L) :=
    Real.one_le_exp_iff.mpr (mul_nonneg hB hL)
  have hqbounds : ∀ᵐ x ∂volume,
      Real.exp (-B * L) ≤ w x / Z ∧ w x / Z ≤ Real.exp (B * L) := by
    filter_upwards [hw] with x hx
    constructor
    · apply (le_div_iff₀ hZ).mpr
      exact (mul_le_mul_of_nonneg_left hZhi hlo.le).trans (by simpa using hx.1)
    · apply (div_le_iff₀ hZ).mpr
      have hid : Real.exp (B * L) * Real.exp (-B * L) = 1 := by
        rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
      exact hx.2.trans (by
        rw [← hid]
        exact mul_le_mul_of_nonneg_left hZlo (Real.exp_nonneg _))
  let q : BoundedBackground d (Real.exp (-B * L)) (Real.exp (B * L)) := {
    density := fun x => w x / Z
    measurable := hwm.div_const Z
    lower_pos := hlo
    lower_le_one := hlo1
    one_le_upper := hhi1
    bounds := hqbounds
    mass := by rw [integral_div]; change Z / Z = 1; exact div_self (ne_of_gt hZ) }
  have hwraw (y : UnitAddTorus (Fin d)) :
      w y = Real.exp (β * A) * Real.exp (-β * V y) := by
    dsimp [w]
    rw [← Real.exp_add]
    congr 1
    ring
  have hZraw : Z = Real.exp (β * A) * (∫ y, Real.exp (-β * V y)) := by
    simp only [Z, hwraw, integral_const_mul]
  have hZrawpos : 0 < (∫ y, Real.exp (-β * V y)) := by
    have h : 0 < Real.exp (β * A) * (∫ y, Real.exp (-β * V y)) := hZraw ▸ hZ
    exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp h
  refine ⟨hZrawpos, q, ?_⟩
  intro x
  change w x / Z = _
  rw [hwraw, hZraw]
  exact mul_div_mul_left _ _ (ne_of_gt (Real.exp_pos _))
