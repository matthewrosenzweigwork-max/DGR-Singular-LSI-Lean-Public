module

public import Tablet.TiltNormalization
public import Tablet.BoundedTiltBounds
public import Tablet.VarianceVariational
public import Tablet.EntropyVariational

@[expose] public section
-- [TABLET NODE: BoundedDensityComparison]
theorem BoundedDensityComparison {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (w f e : Ω → ℝ) (l u : ℝ) (hl : 0 < l)
    (hw : Measurable w) (hb : ∀ᵐ x ∂μ, l ≤ w x ∧ w x ≤ u)
    (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ᵐ x ∂μ, |f x| ≤ C)
    (he : Measurable e) (hen : ∀ᵐ x ∂μ, 0 ≤ e x)
    (hei : MeasureTheory.Integrable e μ) :
    ProbabilityTheory.variance f (NormalizedTilt μ w) ≤
      (u / (∫ x, w x ∂μ)) * ProbabilityTheory.variance f μ ∧
    Entropy (NormalizedTilt μ w) (fun x => f x ^ 2) ≤
      (u / (∫ x, w x ∂μ)) * Entropy μ (fun x => f x ^ 2) ∧
    (l / (∫ x, w x ∂μ)) * (∫ x, e x ∂μ) ≤
      (∫ x, e x ∂NormalizedTilt μ w) ∧
    (∫ x, e x ∂NormalizedTilt μ w) ≤
      (u / (∫ x, w x ∂μ)) * (∫ x, e x ∂μ) := by
-- BODY
  have hvar : ProbabilityTheory.variance f (NormalizedTilt μ w) ≤
      (u / (∫ x, w x ∂μ)) * ProbabilityTheory.variance f μ := by
    obtain ⟨hiw, hzl, hzu, _, _⟩ := BoundedTiltBounds μ w l u hl hw hb
    have hz : 0 < ∫ x, w x ∂μ := hl.trans_le hzl
    have hpos : ∀ᵐ x ∂μ, 0 ≤ w x := hb.mono fun _ hx => hl.le.trans hx.1
    obtain ⟨hprob, htilt⟩ := TiltNormalization μ w hw hpos hiw hz
    haveI : MeasureTheory.IsProbabilityMeasure (NormalizedTilt μ w) := hprob
    obtain ⟨C, hC⟩ := hfb
    have hfμ : MeasureTheory.MemLp f 2 μ :=
      MeasureTheory.MemLp.of_bound hf.aestronglyMeasurable C
        (by simpa only [Real.norm_eq_abs] using hC)
    have hac : (NormalizedTilt μ w).AbsolutelyContinuous μ :=
      MeasureTheory.withDensity_absolutelyContinuous _ _
    have hCν : ∀ᵐ x ∂NormalizedTilt μ w, |f x| ≤ C :=
      hC.filter_mono hac.ae_le
    have hfν : MeasureTheory.MemLp f 2 (NormalizedTilt μ w) :=
      MeasureTheory.MemLp.of_bound hf.aestronglyMeasurable C
        (by simpa only [Real.norm_eq_abs] using hCν)
    let b : ℝ := ∫ x, f x ∂μ
    let g : Ω → ℝ := fun x => (f x - b) ^ 2
    have hgm : Measurable g := (hf.sub measurable_const).pow_const 2
    have hgi : MeasureTheory.Integrable g μ :=
      (hfμ.sub (MeasureTheory.memLp_const b)).integrable_sq
    have hwb : ∀ᵐ x ∂μ, ‖w x‖ ≤ max |l| |u| := by
      filter_upwards [hb] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (hl.le.trans hx.1)]
      exact hx.2.trans ((le_abs_self u).trans (le_max_right _ _))
    have hgw : MeasureTheory.Integrable (fun x => g x * w x) μ := by
      simpa only [mul_comm] using hgi.bdd_mul hw.aestronglyMeasurable hwb
    have hbound : (∫ x, g x * w x ∂μ) ≤ (∫ x, g x ∂μ) * u := by
      rw [← MeasureTheory.integral_mul_const]
      apply MeasureTheory.integral_mono_ae hgw (hgi.mul_const u)
      filter_upwards [hb] with x hx
      exact mul_le_mul_of_nonneg_left hx.2 (sq_nonneg _)
    have hbase : (∫ x, g x ∂μ) = ProbabilityTheory.variance f μ := by
      simpa [g, b] using (VarianceVariational μ f hfμ b).1
    calc
      ProbabilityTheory.variance f (NormalizedTilt μ w) ≤
          (∫ x, g x ∂NormalizedTilt μ w) := (VarianceVariational _ f hfν b).2
      _ = (∫ x, g x * w x ∂μ) / (∫ x, w x ∂μ) := (htilt g hgm hgw).2
      _ ≤ ((∫ x, g x ∂μ) * u) / (∫ x, w x ∂μ) :=
        div_le_div_of_nonneg_right hbound hz.le
      _ = (u / (∫ x, w x ∂μ)) * ProbabilityTheory.variance f μ := by
        rw [hbase]
        ring

  obtain ⟨hiw, hzl, hzu, _, _⟩ := BoundedTiltBounds μ w l u hl hw hb
  have hz : 0 < ∫ x, w x ∂μ := hl.trans_le hzl
  have hpos : ∀ᵐ x ∂μ, 0 ≤ w x := hb.mono fun _ hx => hl.le.trans hx.1
  obtain ⟨hprob, htilt⟩ := TiltNormalization μ w hw hpos hiw hz
  let ν := NormalizedTilt μ w
  haveI : MeasureTheory.IsProbabilityMeasure ν := hprob
  have hwb : ∀ᵐ x ∂μ, ‖w x‖ ≤ max |l| |u| := by
    filter_upwards [hb] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hl.le.trans hx.1)]
    exact hx.2.trans ((le_abs_self u).trans (le_max_right _ _))
  have hac : ν.AbsolutelyContinuous μ :=
    MeasureTheory.withDensity_absolutelyContinuous _ _
  obtain ⟨C, hC⟩ := hfb
  have hCν : ∀ᵐ x ∂ν, |f x| ≤ C := hC.filter_mono hac.ae_le
  have hfμ : MeasureTheory.MemLp f 2 μ :=
    MeasureTheory.MemLp.of_bound hf.aestronglyMeasurable C
      (by simpa only [Real.norm_eq_abs] using hC)
  have hfν : MeasureTheory.MemLp f 2 ν :=
    MeasureTheory.MemLp.of_bound hf.aestronglyMeasurable C
      (by simpa only [Real.norm_eq_abs] using hCν)
  have hLogFor : ∀ (ρ : MeasureTheory.Measure Ω),
      MeasureTheory.IsProbabilityMeasure ρ →
      (∀ᵐ x ∂ρ, |f x| ≤ C) →
      MeasureTheory.Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) ρ := by
    intro ρ hprobρ hCρ
    haveI : MeasureTheory.IsProbabilityMeasure ρ := hprobρ
    obtain ⟨K, hK⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (C ^ 2))).exists_bound_of_continuousOn
      Real.continuous_mul_log.continuousOn
    apply (MeasureTheory.integrable_const K).mono'
      (Real.continuous_mul_log.measurable.comp (hf.pow_const 2)).aestronglyMeasurable
    filter_upwards [hCρ] with x hx
    exact hK _ ⟨sq_nonneg _, sq_le_sq.mpr (hx.trans (le_abs_self C))⟩
  have hiSqμ : MeasureTheory.Integrable (fun x => f x ^ 2) μ := hfμ.integrable_sq
  have hiSqν : MeasureTheory.Integrable (fun x => f x ^ 2) ν := hfν.integrable_sq
  have hlogμ := hLogFor μ inferInstance hC
  have hlogν := hLogFor ν inferInstance hCν
  have hEVμ := EntropyVariational μ (fun x => f x ^ 2) (hf.pow_const 2)
    (Filter.Eventually.of_forall fun x => sq_nonneg (f x)) hiSqμ hlogμ
  have hEVν := EntropyVariational ν (fun x => f x ^ 2) (hf.pow_const 2)
    (Filter.Eventually.of_forall fun x => sq_nonneg (f x)) hiSqν hlogν
  have hent : Entropy ν (fun x => f x ^ 2) ≤
      (u / (∫ x, w x ∂μ)) * Entropy μ (fun x => f x ^ 2) := by
    by_cases hzero : (∫ x, f x ^ 2 ∂μ) = 0
    · have hfae : (fun x => f x ^ 2) =ᵐ[μ] 0 :=
        (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
          (Filter.Eventually.of_forall fun x => sq_nonneg (f x)) hiSqμ).mp hzero
      have hfaeν : (fun x => f x ^ 2) =ᵐ[ν] 0 := hfae.filter_mono hac.ae_le
      have hzeroν : (∫ x, f x ^ 2 ∂ν) = 0 := by
        rw [MeasureTheory.integral_congr_ae hfaeν]
        simp
      rw [hEVμ.2.2 hzero, hEVν.2.2 hzeroν]
      simp
    · let t : ℝ := ∫ x, f x ^ 2 ∂μ
      have ht : 0 < t := lt_of_le_of_ne
        (MeasureTheory.integral_nonneg fun x => sq_nonneg (f x)) (Ne.symm hzero)
      let Φ : Ω → ℝ := fun x =>
        f x ^ 2 * Real.log (f x ^ 2 / t) - f x ^ 2 + t
      have hΦm : Measurable Φ := by fun_prop
      have hΦi : MeasureTheory.Integrable Φ μ := (hEVμ.1 t ht).2.1
      have hΦn : ∀ᵐ x ∂μ, 0 ≤ Φ x := (hEVμ.1 t ht).1
      have hΦwi : MeasureTheory.Integrable (fun x => Φ x * w x) μ :=
        hΦi.mul_bdd hw.aestronglyMeasurable hwb
      have hbound : (∫ x, Φ x * w x ∂μ) ≤ (∫ x, Φ x ∂μ) * u := by
        rw [← MeasureTheory.integral_mul_const]
        apply MeasureTheory.integral_mono_ae hΦwi (hΦi.mul_const u)
        filter_upwards [hb, hΦn] with x hx hn
        exact mul_le_mul_of_nonneg_left hx.2 hn
      have hbase : (∫ x, Φ x ∂μ) = Entropy μ (fun x => f x ^ 2) :=
        (hEVμ.2.1 ht).symm
      calc
        Entropy ν (fun x => f x ^ 2) ≤ ∫ x, Φ x ∂ν := (hEVν.1 t ht).2.2
        _ = (∫ x, Φ x * w x ∂μ) / (∫ x, w x ∂μ) := (htilt Φ hΦm hΦwi).2
        _ ≤ ((∫ x, Φ x ∂μ) * u) / (∫ x, w x ∂μ) :=
          div_le_div_of_nonneg_right hbound hz.le
        _ = _ := by rw [hbase]; ring
  have hewi : MeasureTheory.Integrable (fun x => e x * w x) μ :=
    hei.mul_bdd hw.aestronglyMeasurable hwb
  have heνeq : (∫ x, e x ∂ν) =
      (∫ x, e x * w x ∂μ) / (∫ x, w x ∂μ) := (htilt e he hewi).2
  have hLower : l * (∫ x, e x ∂μ) ≤ ∫ x, e x * w x ∂μ := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_mono_ae (hei.const_mul l) hewi
    filter_upwards [hb, hen] with x hx hn
    calc
      l * e x = e x * l := mul_comm _ _
      _ ≤ e x * w x := mul_le_mul_of_nonneg_left hx.1 hn
  have hUpper : (∫ x, e x * w x ∂μ) ≤ u * (∫ x, e x ∂μ) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_mono_ae hewi (hei.const_mul u)
    filter_upwards [hb, hen] with x hx hn
    calc
      e x * w x ≤ e x * u := mul_le_mul_of_nonneg_left hx.2 hn
      _ = u * e x := mul_comm _ _
  refine ⟨hvar, hent, ?_, ?_⟩
  · calc
      (l / (∫ x, w x ∂μ)) * (∫ x, e x ∂μ) =
          (l * (∫ x, e x ∂μ)) / (∫ x, w x ∂μ) := by ring
      _ ≤ (∫ x, e x * w x ∂μ) / (∫ x, w x ∂μ) :=
        div_le_div_of_nonneg_right hLower hz.le
      _ = _ := heνeq.symm
  · calc
      (∫ x, e x ∂ν) = (∫ x, e x * w x ∂μ) / (∫ x, w x ∂μ) := heνeq
      _ ≤ (u * (∫ x, e x ∂μ)) / (∫ x, w x ∂μ) :=
        div_le_div_of_nonneg_right hUpper hz.le
      _ = _ := by ring
