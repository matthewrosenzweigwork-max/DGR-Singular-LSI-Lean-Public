module

public import Tablet.CenteredCanonicalRecenter
public import Tablet.BoundedDensityComparison
public import Tablet.UniformRegularizedPoincare
public import Tablet.ConfigurationCalculus

@[expose] public section
open MeasureTheory
-- [TABLET NODE: CenteredUniformPoincare]
theorem CenteredUniformPoincare (d : ℕ) (hd : 2 ≤ d)
    (s a B l u H : ℝ) (hs : 0 ≤ s) (hsd : s ≤ (d : ℝ)-2)
    (ha : 0 < a) (hB : 0 ≤ B) (hl : 0 < l) (hl1 : l ≤ 1) (hu : 1 ≤ u) (hH : 0 ≤ H) :
    ∃ rate : ℝ, 0 < rate ∧ ∀ (N : ℕ), 2 ≤ N →
      ∀ (β : ℝ), 0 ≤ β → β ≤ B → ∀ (q : BoundedBackground d l u),
      ∀ (ε : ℝ), 0 < ε → ∀ (rl ru Z : ℝ) (r : BoundedBackground d rl ru),
      0 < Z → Measurable (BackgroundPotential (RieszKernel d s a ε) r.density) →
      (∀ᵐ x ∂volume, |BackgroundPotential (RieszKernel d s a ε) r.density x| ≤ H) →
      (∀ᵐ x ∂volume, r.density x = q.density x *
        Real.exp (-β * BackgroundPotential (RieszKernel d s a ε) r.density x) / Z) →
      ∀ (f : Configuration d N → ℝ), f ∈ SmoothCore d N →
        ProbabilityTheory.variance f (CenteredCanonicalLaw (N := N) (RieszKernel d s a ε) r.density β) ≤
          rate⁻¹ * PhysicalEnergy (CenteredCanonicalLaw (N := N) (RieszKernel d s a ε) r.density β) f := by
-- BODY
  have poincare_transport {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (w f e : Ω → ℝ)
    (l u P : ℝ) (hl : 0 < l) (hP : 0 ≤ P)
    (hw : Measurable w) (hb : ∀ᵐ x ∂μ, l ≤ w x ∧ w x ≤ u)
    (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ᵐ x ∂μ, |f x| ≤ C)
    (he : Measurable e) (hen : ∀ᵐ x ∂μ, 0 ≤ e x) (hei : Integrable e μ)
    (hpi : ProbabilityTheory.variance f μ ≤ P * ∫ x, e x ∂μ) :
    ProbabilityTheory.variance f (NormalizedTilt μ w) ≤
      (u / l * P) * ∫ x, e x ∂NormalizedTilt μ w := by

    have ht := BoundedDensityComparison μ w f e l u hl hw hb hf hfb he hen hei
    have hz := (BoundedTiltBounds μ w l u hl hw hb).2.1
    have hZ : 0 < ∫ x, w x ∂μ := hl.trans_le hz
    have hu : 0 ≤ u := (hl.le.trans hz).trans ((BoundedTiltBounds μ w l u hl hw hb).2.2.1)
    have hscale : 0 ≤ u / (∫ x, w x ∂μ) := div_nonneg hu hZ.le
    have hecomp := ht.2.2.1
    have hh := mul_le_mul_of_nonneg_left hecomp (show 0 ≤ u / l * P by positivity)
    have hcoef : u / l * P * (l / (∫ x, w x ∂μ)) = u / (∫ x, w x ∂μ) * P := by
      field_simp
    calc
      ProbabilityTheory.variance f (NormalizedTilt μ w) ≤
          (u / (∫ x, w x ∂μ)) * ProbabilityTheory.variance f μ := ht.1
      _ ≤ (u / (∫ x, w x ∂μ)) * (P * ∫ x, e x ∂μ) :=
        mul_le_mul_of_nonneg_left hpi hscale
      _ = (u / l * P) * ((l / (∫ x, w x ∂μ)) * ∫ x, e x ∂μ) := by
        calc
          _ = ((u / (∫ x, w x ∂μ)) * P) * (∫ x, e x ∂μ) := by ring
          _ = _ := by rw [← hcoef]; ring
      _ ≤ _ := hh
  obtain ⟨rate, hrate, hpi⟩ := UniformRegularizedPoincare d hd s a B l u hs hsd ha hB hl hl1 hu
  let rate' := rate * Real.exp (-2 * B * H)
  have hrate' : 0 < rate' := mul_pos hrate (Real.exp_pos _)
  refine ⟨rate', hrate', ?_⟩
  intro N hN β hβ hβB q ε hε rl ru Z r hZ hh hhb hEL f hf
  let G := RieszKernel d s a ε
  let h := BackgroundPotential G r.density
  let b : Configuration d N → ℝ := fun X => Real.exp (-β / (N : ℝ) * ∑ i : Fin N, h (X i))
  let P := CanonicalLaw (N := N) G q.density β
  obtain ⟨c, hc, hfound⟩ := RieszL1Foundation d hd s a hs (by linarith) ha
  have hF := hfound ε hε.le
  have hgl : ∀ᵐ x ∂volume, -c ≤ G x := Filter.Eventually.of_forall hF.2.2.2.2.1
  have hr := CenteredCanonicalRecenter d N hN l u rl ru β c H Z q r G hF.1 hF.2.1 hβ hc hgl hH hZ hh hhb hEL
  have hprob := (GibbsNormalizerBounds d N hN l u q G hF.1 hF.2.1 c β hc hβ hgl).2.2.2
  haveI : IsProbabilityMeasure P := hprob
  have hbm : Measurable b := by
    exact (measurable_const.mul (Finset.measurable_fun_sum _ fun i _ => hh.comp (measurable_pi_apply i))).exp
  have hCal := (ConfigurationCalculus d N).2.2.2 f hf
  have hfm := hCal.2.1
  have hfb := hCal.2.2.1
  have hem := hCal.2.2.2.1
  have heb := hCal.2.2.2.2.1
  have hei : Integrable (fun X => ‖CoordinateGradient f X‖^2) P := by
    obtain ⟨C, hC⟩ := heb
    apply (integrable_const C).mono' hem.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun X => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖CoordinateGradient f X‖))] using hC X
  have ht := poincare_transport P b f (fun X => ‖CoordinateGradient f X‖^2)
    (Real.exp (-β * H)) (Real.exp (β * H)) rate⁻¹ (Real.exp_pos _) (inv_nonneg.mpr hrate.le)
    hbm hr.2 hfm (by obtain ⟨C,hC⟩:=hfb; exact ⟨C,Filter.Eventually.of_forall hC⟩)
    hem (Filter.Eventually.of_forall fun X => sq_nonneg _) hei (hpi N hN β hβ hβB q ε hε f hf)
  rw [← hr.1] at ht
  have hcoeff : (Real.exp (β * H) / Real.exp (-β * H) * rate⁻¹) ≤ rate'⁻¹ := by
    have htemp : β * H ≤ B * H := mul_le_mul_of_nonneg_right hβB hH
    have hrat : Real.exp (β * H) / Real.exp (-β * H) = Real.exp (2 * β * H) := by
      rw [← Real.exp_sub]; congr 1; ring
    rw [hrat]
    have he : Real.exp (2 * β * H) ≤ Real.exp (2 * B * H) := Real.exp_le_exp.mpr (by linarith)
    have hh' := mul_le_mul_of_nonneg_right he (inv_nonneg.mpr hrate.le)
    have hid : rate'⁻¹ = Real.exp (2 * B * H) * rate⁻¹ := by
      dsimp [rate']; rw [mul_inv_rev, ← Real.exp_neg]; congr 1; congr 1; ring
    rw [hid]
    exact hh'
  exact ht.trans (mul_le_mul_of_nonneg_right hcoeff (integral_nonneg fun X => sq_nonneg _))
