module

public import Tablet.CenteredCanonicalLaw
public import Tablet.CenteredEnergyIdentity
public import Tablet.ProductBackgroundMeasureIdentity
public import Tablet.GibbsNormalizerBounds
public import Tablet.BoundedDensityComparison

@[expose] public section
open MeasureTheory

-- [TABLET NODE: CenteredCanonicalRecenter]
theorem CenteredCanonicalRecenter (d N : ℕ) (hN : 2 ≤ N)
    (l u rl ru β c H Z : ℝ)
    (q : BoundedBackground d l u) (r : BoundedBackground d rl ru)
    (g : UnitAddTorus (Fin d) → ℝ) (hg : Measurable g) (hgi : Integrable g volume)
    (hβ : 0 ≤ β) (hc : 0 ≤ c) (hgl : ∀ᵐ x ∂volume, -c ≤ g x)
    (hH : 0 ≤ H) (hZ : 0 < Z)
    (hh : Measurable (BackgroundPotential g r.density))
    (hhb : ∀ᵐ x ∂volume, |BackgroundPotential g r.density x| ≤ H)
    (hEL : ∀ᵐ x ∂volume,
      r.density x = q.density x * Real.exp (-β * BackgroundPotential g r.density x) / Z) :
    let b : Configuration d N → ℝ := fun X =>
      Real.exp (-β / (N : ℝ) * ∑ i : Fin N, BackgroundPotential g r.density (X i))
    CenteredCanonicalLaw (N := N) g r.density β =
      NormalizedTilt (CanonicalLaw (N := N) g q.density β) b ∧
    (∀ᵐ X ∂CanonicalLaw (N := N) g q.density β,
      Real.exp (-β * H) ≤ b X ∧ b X ≤ Real.exp (β * H)) := by
-- BODY
  classical
  haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp; infer_instance
  haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := inferInstance
  let h := BackgroundPotential g r.density
  let b : Configuration d N → ℝ := fun X => Real.exp (-β / (N : ℝ) * ∑ i : Fin N, h (X i))
  have hnp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hcoords : ∀ᵐ X : Configuration d N ∂volume,
      ∀ i : Fin N, r.density (X i) = q.density (X i) * Real.exp (-β * h (X i)) / Z := by
    rw [Filter.eventually_all]
    intro i
    exact (measurePreserving_eval (fun _ : Fin N =>
      (volume : Measure (UnitAddTorus (Fin d)))) i).quasiMeasurePreserving.tendsto_ae hEL
  have hbounds : ∀ᵐ X : Configuration d N ∂volume, ∀ i : Fin N, |h (X i)| ≤ H := by
    rw [Filter.eventually_all]
    intro i
    exact (measurePreserving_eval (fun _ : Fin N =>
      (volume : Measure (UnitAddTorus (Fin d)))) i).quasiMeasurePreserving.tendsto_ae hhb
  have hb : ∀ᵐ X : Configuration d N ∂volume,
      Real.exp (-β * H) ≤ b X ∧ b X ≤ Real.exp (β * H) := by
    filter_upwards [hbounds] with X hX
    have hlo : -(N : ℝ) * H ≤ ∑ i : Fin N, h (X i) := by
      have hh' := Finset.sum_le_sum (s := Finset.univ) fun i _ => (abs_le.mp (hX i)).1
      simpa using hh'
    have hhi : (∑ i : Fin N, h (X i)) ≤ (N : ℝ) * H := by
      have hh' := Finset.sum_le_sum (s := Finset.univ) fun i _ => (abs_le.mp (hX i)).2
      simpa using hh'
    have hdiv : 0 ≤ β / (N : ℝ) := div_nonneg hβ hnp.le
    have helo := mul_le_mul_of_nonneg_left hhi hdiv
    have hehi := mul_le_mul_of_nonneg_left hlo hdiv
    have hid : β / (N : ℝ) * ((N : ℝ) * H) = β * H := by field_simp
    change Real.exp (-β * H) ≤ Real.exp _ ∧ Real.exp _ ≤ Real.exp (β * H)
    constructor <;> apply Real.exp_le_exp.mpr
    · simpa only [neg_div, neg_mul] using neg_le_neg (helo.trans_eq hid)
    · have hehi' : -(β * H) ≤ β / (N : ℝ) * ∑ i : Fin N, h (X i) := by
        have hnegid : β / (N : ℝ) * (-(N : ℝ) * H) = -(β * H) := by field_simp
        rwa [hnegid] at hehi
      simpa only [neg_div, neg_mul, neg_neg] using neg_le_neg hehi'
  have hbm : Measurable b := by
    dsimp [b, h]
    exact (measurable_const.mul (Finset.measurable_fun_sum _ fun i _ => hh.comp (measurable_pi_apply i))).exp
  have hpairm : Measurable (fun X : Configuration d N => PairEnergy g X) := by
    unfold PairEnergy
    refine measurable_const.mul (Finset.measurable_fun_sum _ fun i _ => ?_)
    refine Finset.measurable_fun_sum _ fun j _ => ?_
    split_ifs
    · exact hg.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))
    · exact measurable_const
  have hqm : Measurable (ProductDensity (N := N) q.density) :=
    (ProductBackgroundFacts d N l u q).1
  have hwm : Measurable (GibbsWeight (N := N) g q.density β) :=
    (measurable_const.mul hpairm).exp.mul hqm
  have hwpos : ∀ᵐ X : Configuration d N ∂volume, 0 ≤ GibbsWeight g q.density β X := by
    filter_upwards [(ProductBackgroundFacts d N l u q).2.2.2] with X hx
    exact mul_nonneg (Real.exp_pos _).le ((pow_nonneg q.lower_pos.le N).trans hx.1)
  have hgb := GibbsNormalizerBounds d N hN l u q g hg hgi c β hc hβ hgl
  have hZw : 0 < ∫ X : Configuration d N, GibbsWeight g q.density β X :=
    (Real.exp_pos _).trans_le hgb.2.1
  have tilt_multiply {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
      (w b : Ω → ℝ) (l u : ℝ) (hw : Measurable w)
      (hwp : ∀ᵐ x ∂μ, 0 ≤ w x) (hwi : Integrable w μ) (hZ : 0 < ∫ x, w x ∂μ)
      (hb : Measurable b) (hl : 0 < l) (hbb : ∀ᵐ x ∂μ, l ≤ b x ∧ b x ≤ u) :
      NormalizedTilt μ (fun x => b x * w x) = NormalizedTilt (NormalizedTilt μ w) b := by
    have hbn : ∀ᵐ x ∂μ, 0 ≤ b x := hbb.mono fun x hx => hl.le.trans hx.1
    have hbabs : ∀ᵐ x ∂μ, ‖b x‖ ≤ max |l| |u| := by
      filter_upwards [hbb, hbn] with x hx hp
      rw [Real.norm_eq_abs, abs_of_nonneg hp]
      exact hx.2.trans ((le_abs_self u).trans (le_max_right _ _))
    have hbwi : Integrable (fun x => b x * w x) μ := hwi.bdd_mul hb.aestronglyMeasurable hbabs
    have hZbw : 0 < ∫ x, b x * w x ∂μ := by
      have hlow : l * ∫ x, w x ∂μ ≤ ∫ x, b x * w x ∂μ := by
        rw [← integral_const_mul]
        apply integral_mono_ae (hwi.const_mul l) hbwi
        filter_upwards [hbb, hwp] with x hx hp
        exact mul_le_mul_of_nonneg_right hx.1 hp
      exact (mul_pos hl hZ).trans_le hlow
    have ht := (TiltNormalization μ w hw hwp hwi hZ).2 b hb (by simpa only [mul_comm] using hbwi)
    simp only [NormalizedTilt] at ht ⊢
    rw [ht.2]
    rw [← withDensity_mul μ (by fun_prop) (by fun_prop)]
    apply withDensity_congr_ae
    filter_upwards [hwp, hbn] with x hx hbpos
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (div_nonneg hx hZ.le)]
    congr 1
    field_simp [ne_of_gt hZ, ne_of_gt hZbw] <;> ring
  have tilt_scale {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (w : Ω → ℝ)
      (t : ℝ) (ht : t ≠ 0) : NormalizedTilt μ (fun x => t * w x) = NormalizedTilt μ w := by
    unfold NormalizedTilt
    simp only [integral_const_mul]
    congr 1; funext x; congr 1
    exact mul_div_mul_left _ _ ht
  have tilt_congr {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (w v : Ω → ℝ)
      (heq : w =ᵐ[μ] v) : NormalizedTilt μ w = NormalizedTilt μ v := by
    unfold NormalizedTilt
    rw [integral_congr_ae heq]
    apply withDensity_congr_ae
    exact heq.mono fun x hx => by dsimp only; rw [hx]
  let t := Real.exp (-β * ((N : ℝ) - 1) / 2 * BackgroundPairMean g r.density) / Z ^ N
  have ht : t ≠ 0 := div_ne_zero (Real.exp_pos _).ne' (pow_ne_zero _ hZ.ne')
  have hweight : (fun X : Configuration d N => Real.exp (-β * CenteredPairEnergy g r.density X) *
      ProductDensity r.density X) =ᵐ[volume] (fun X => t * (b X * GibbsWeight g q.density β X)) := by
    filter_upwards [hcoords] with X hX
    have hprod : ProductDensity r.density X =
        ProductDensity q.density X * Real.exp (-β * ∑ i : Fin N, h (X i)) / Z ^ N := by
      unfold ProductDensity
      simp_rw [hX]
      rw [Finset.prod_div_distrib, Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← Real.exp_sum, ← Finset.mul_sum]
    rw [hprod]
    have he : -β * CenteredPairEnergy g r.density X + (-β * ∑ i : Fin N, h (X i)) =
        -β * ((N : ℝ)-1) / 2 * BackgroundPairMean g r.density +
          (-β / (N : ℝ) * ∑ i : Fin N, h (X i)) + (-β * PairEnergy g X) := by
      rw [CenteredEnergyIdentity (by omega) g r.density X]
      dsimp [h]
      field_simp
      <;> ring
    calc
      _ = ProductDensity q.density X / Z ^ N *
          (Real.exp (-β * CenteredPairEnergy g r.density X) *
            Real.exp (-β * ∑ i : Fin N, h (X i))) := by ring
      _ = _ := by
        rw [← Real.exp_add, he, Real.exp_add, Real.exp_add]
        dsimp [t, b, GibbsWeight]
        ring
  have hcm : Measurable (fun X : Configuration d N => CenteredPairEnergy g r.density X) := by
    have hid : (fun X : Configuration d N => CenteredPairEnergy g r.density X) =
        fun X => PairEnergy g X - ((N : ℝ)-1)/(N : ℝ) * ∑ i : Fin N, h (X i) +
          ((N : ℝ)-1)/2 * BackgroundPairMean g r.density := by
      funext X; exact CenteredEnergyIdentity (by omega) g r.density X
    rw [hid]
    exact (hpairm.sub (measurable_const.mul
      (Finset.measurable_fun_sum _ fun i _ => hh.comp (measurable_pi_apply i)))).add measurable_const
  constructor
  · unfold CenteredCanonicalLaw
    have product_tilt (w : Configuration d N → ℝ) (hw : Measurable w) :
        NormalizedTilt
          (Measure.pi (fun _ : Fin N => (volume : Measure (UnitAddTorus (Fin d))).withDensity
            (fun x => ENNReal.ofReal (r.density x)))) w =
        NormalizedTilt (volume : Measure (Configuration d N))
          (fun X => w X * ProductDensity r.density X) := by
      rw [ProductBackgroundMeasureIdentity d N rl ru r]
      have hp := ProductBackgroundFacts d N rl ru r
      have hpn : 0 ≤ᵐ[(volume : Measure (Configuration d N))] ProductDensity r.density :=
        hp.2.2.2.mono fun X hx => (pow_nonneg r.lower_pos.le N).trans hx.1
      have hz : (∫ X, w X ∂(volume : Measure (Configuration d N)).withDensity
          (fun X => ENNReal.ofReal (ProductDensity r.density X))) =
          (∫ X, w X * ProductDensity r.density X) := by
        rw [integral_withDensity_eq_integral_toReal_smul hp.1.ennreal_ofReal
          (Filter.Eventually.of_forall fun X => ENNReal.ofReal_lt_top) w]
        apply integral_congr_ae
        filter_upwards [hpn] with X hn
        rw [ENNReal.toReal_ofReal hn]
        exact mul_comm _ _
      unfold NormalizedTilt
      rw [hz]
      rw [← withDensity_mul _ hp.1.ennreal_ofReal (hw.div_const _).ennreal_ofReal]
      apply withDensity_congr_ae
      filter_upwards [hpn] with X hn
      simp only [Pi.mul_apply]
      rw [← ENNReal.ofReal_mul hn]
      congr 1
      ring
    rw [product_tilt _ (by exact (measurable_const.mul hcm).exp)]
    rw [tilt_congr volume _ _ hweight, tilt_scale volume _ t ht]
    exact tilt_multiply volume _ b _ _ hwm hwpos hgb.1 hZw hbm (Real.exp_pos _) hb
  · exact hb.filter_mono (withDensity_absolutelyContinuous _ _).ae_le
