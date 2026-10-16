module

public import Tablet.CenteredKernel
public import Tablet.BoundedBackground
public import Tablet.NormalizedTilt
public import Tablet.ConditionalPotential
public import Tablet.Replacement

@[expose] public section
open MeasureTheory

-- [TABLET NODE: CenteredConditionalIdentity]
theorem CenteredConditionalIdentity (d N : ℕ) (hN : 2 ≤ N)
    (l u rl ru β Z : ℝ)
    (q : BoundedBackground d l u) (r : BoundedBackground d rl ru)
    (g : UnitAddTorus (Fin d) → ℝ) (hg : Measurable g)
    (hZ : 0 < Z) (hh : Measurable (BackgroundPotential g r.density))
    (hEL : ∀ᵐ x ∂volume,
      r.density x = q.density x * Real.exp (-β * BackgroundPotential g r.density x) / Z) :
    ∀ (X : Configuration d N) (i : Fin N),
      NormalizedTilt ((volume : Measure (UnitAddTorus (Fin d))).withDensity
        (fun z => ENNReal.ofReal (r.density z)))
        (fun z => Real.exp (-β / (N : ℝ) * ∑ j : Fin N,
          if j = i then 0 else CenteredKernel g r.density z (X j))) =
      NormalizedTilt volume (fun z => q.density z *
        Real.exp (-β * BackgroundPotential g r.density z / (N : ℝ)) *
        Real.exp (-ConditionalPotential g β X i z)) := by
-- BODY
  classical
  have hnp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have tilt_congr {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (w v : Ω → ℝ)
      (heq : w =ᵐ[μ] v) : NormalizedTilt μ w = NormalizedTilt μ v := by
    unfold NormalizedTilt
    rw [integral_congr_ae heq]
    apply withDensity_congr_ae
    exact heq.mono fun x hx => by dsimp only; rw [hx]
  have tilt_scale {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (w : Ω → ℝ)
      (t : ℝ) (ht : t ≠ 0) : NormalizedTilt μ (fun x => t * w x) = NormalizedTilt μ w := by
    unfold NormalizedTilt
    simp only [integral_const_mul]
    congr 1; funext x; congr 1
    exact mul_div_mul_left _ _ ht
  have tilt_density {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
      (r w : Ω → ℝ) (hr : Measurable r) (hw : Measurable w)
      (hrn : ∀ᵐ x ∂μ, 0 ≤ r x) :
      NormalizedTilt (μ.withDensity (fun x => ENNReal.ofReal (r x))) w =
        NormalizedTilt μ (fun x => w x * r x) := by
    have hz : (∫ x, w x ∂μ.withDensity (fun x => ENNReal.ofReal (r x))) = ∫ x, w x * r x ∂μ := by
      rw [integral_withDensity_eq_integral_toReal_smul hr.ennreal_ofReal
        (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top) w]
      apply integral_congr_ae
      filter_upwards [hrn] with x hn
      rw [ENNReal.toReal_ofReal hn]
      exact mul_comm _ _
    unfold NormalizedTilt
    rw [hz]
    rw [← withDensity_mul μ hr.ennreal_ofReal (hw.div_const _).ennreal_ofReal]
    apply withDensity_congr_ae
    filter_upwards [hrn] with x hn
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul hn]
    congr 1; ring
  intro X i
  let h := BackgroundPotential g r.density
  let m := BackgroundPairMean g r.density
  let S : UnitAddTorus (Fin d) → ℝ := fun z => ∑ j : Fin N, if j = i then 0 else g (z - X j)
  let Y := ∑ j : Fin N, if j = i then 0 else h (X j)
  let W : UnitAddTorus (Fin d) → ℝ := fun z => Real.exp (-β / (N : ℝ) * ∑ j : Fin N,
    if j = i then 0 else CenteredKernel g r.density z (X j))
  let V : UnitAddTorus (Fin d) → ℝ := fun z => q.density z * Real.exp (-β * h z / (N : ℝ)) *
    Real.exp (-ConditionalPotential g β X i z)
  have hsum (z : UnitAddTorus (Fin d)) :
      (∑ j : Fin N, if j = i then 0 else CenteredKernel g r.density z (X j)) =
        S z - ((N : ℝ)-1) * h z - Y + ((N : ℝ)-1) * m := by
    have hterm (j : Fin N) : (if j = i then 0 else CenteredKernel g r.density z (X j)) =
        (if j = i then 0 else g (z - X j)) - (if j = i then 0 else h z) -
          (if j = i then 0 else h (X j)) + (if j = i then 0 else m) := by
      split_ifs <;> simp [CenteredKernel, h, m] <;> ring
    have hconst (a : ℝ) : (∑ j : Fin N, if j = i then 0 else a) = ((N : ℝ)-1) * a := by
      have hterm (j : Fin N) : (if j = i then (0 : ℝ) else a) = a - (if j = i then a else 0) := by split_ifs <;> ring
      simp_rw [hterm]
      simp [Finset.sum_sub_distrib]
      ring
    simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hconst, hconst]
  have hWm : Measurable W := by
    dsimp [W]
    refine (measurable_const.mul (Finset.measurable_fun_sum _ fun j _ => ?_)).exp
    split_ifs
    · exact measurable_const
    · exact (((hg.comp (measurable_id.sub measurable_const)).sub hh).sub measurable_const).add measurable_const
  let t := Real.exp (β / (N : ℝ) * Y - β / (N : ℝ) * ((N : ℝ)-1) * m) / Z
  have ht : t ≠ 0 := div_ne_zero (Real.exp_pos _).ne' hZ.ne'
  have heq : (fun z => W z * r.density z) =ᵐ[volume] (fun z => t * V z) := by
    filter_upwards [hEL] with z hz
    have he : -β / (N : ℝ) * (S z - ((N : ℝ)-1) * h z - Y + ((N : ℝ)-1) * m) + (-β * h z) =
        (β / (N : ℝ) * Y - β / (N : ℝ) * ((N : ℝ)-1) * m) +
        (-β * h z / (N : ℝ)) + (-β / (N : ℝ) * S z) := by
      field_simp <;> ring
    change W z * r.density z = t * V z
    rw [hz]
    dsimp [W]
    rw [hsum]
    calc
      _ = q.density z / Z * (Real.exp (-β / (N : ℝ) *
          (S z - ((N : ℝ)-1) * h z - Y + ((N : ℝ)-1) * m)) * Real.exp (-β * h z)) := by dsimp [h]; ring
      _ = _ := by
        rw [← Real.exp_add, he, Real.exp_add, Real.exp_add]
        dsimp [t, V, ConditionalPotential, S, h]
        ring
  change NormalizedTilt _ W = NormalizedTilt volume V
  rw [tilt_density volume r.density W r.measurable hWm
    (r.bounds.mono fun z hz => r.lower_pos.le.trans hz.1)]
  rw [tilt_congr volume _ _ heq, tilt_scale volume V t ht]
