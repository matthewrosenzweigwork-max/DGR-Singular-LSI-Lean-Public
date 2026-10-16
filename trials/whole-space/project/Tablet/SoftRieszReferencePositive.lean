module

public import Tablet.RieszKernel
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Tactic

@[expose] public section
open MeasureTheory Filter Set
open scoped InnerProduct
set_option autoImplicit false
set_option maxHeartbeats 1500000

-- [TABLET NODE: SoftRieszReferencePositive]
theorem SoftRieszReferencePositive (d : ℕ) (s ε : ℝ) (hs : 0 < s) (hε : 0 < ε)
    (μ : Measure (OneParticle d)) [IsProbabilityMeasure μ]
    (f : OneParticle d → ℝ) (hf : MemLp f 2 μ) :
    0 ≤ ∫ q : OneParticle d × OneParticle d,
      f q.1 * f q.2 * RieszKernel s ε (q.1-q.2) ∂μ.prod μ := by
-- BODY
  have midpoint_square (d : ℕ) (x y z : EuclideanSpace ℝ (Fin d)) :
      2 * ‖x-z‖^2 + 2 * ‖y-z‖^2 =
        ‖x-y‖^2 + 4 * ‖z-(1/2:ℝ) • (x+y)‖^2 := by
    simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, 
       inner_smul_right, inner_add_right, real_inner_comm z x,
      real_inner_comm z y]
    have h := norm_add_sq_real x y
    nlinarith
  have gaussian_integrable (d : ℕ) (t : ℝ) (ht : 0 < t) :
      Integrable (fun z : EuclideanSpace ℝ (Fin d) => Real.exp (-t*‖z‖^2)) volume := by
    have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (V := EuclideanSpace ℝ (Fin d)) (b := (t:ℂ)) (by simpa using ht) 0 0).re
    simp only [zero_mul, add_zero] at h
    change Integrable (fun z : EuclideanSpace ℝ (Fin d) =>
      (Complex.exp (-(t:ℂ)*(‖z‖:ℂ)^2)).re) volume at h
    simpa only [← Complex.ofReal_pow, ← Complex.ofReal_mul,
      ← Complex.ofReal_neg, Complex.exp_ofReal_re] using h
  have gaussian_gram_pointwise (d : ℕ) (t : ℝ)
      (x y z : EuclideanSpace ℝ (Fin d)) :
      Real.exp (-2*t*‖x-z‖^2) * Real.exp (-2*t*‖y-z‖^2) =
        Real.exp (-t*‖x-y‖^2) * Real.exp (-4*t*‖z-(1/2:ℝ) • (x+y)‖^2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    calc
      _ = -t * (2*‖x-z‖^2 + 2*‖y-z‖^2) := by ring
      _ = -t * (‖x-y‖^2 + 4*‖z-(1/2:ℝ) • (x+y)‖^2) := by rw [midpoint_square]
      _ = _ := by ring
  have gaussian_feature_product_integrable (d : ℕ) (t : ℝ) (ht : 0 < t)
      (x y : EuclideanSpace ℝ (Fin d)) :
      Integrable (fun z => Real.exp (-2*t*‖x-z‖^2) * Real.exp (-2*t*‖y-z‖^2)) volume := by
    have h := ((gaussian_integrable d (4*t) (by positivity)).comp_sub_right
      ((1/2:ℝ) • (x+y))).const_mul (Real.exp (-t*‖x-y‖^2))
    apply h.congr
    exact Filter.Eventually.of_forall fun z => by
      dsimp only
      rw [gaussian_gram_pointwise]
      simp only [neg_mul]
  have gaussian_gram_integral (d : ℕ) (t : ℝ) (ht : 0 < t)
      (x y : EuclideanSpace ℝ (Fin d)) :
      (∫ z, Real.exp (-2*t*‖x-z‖^2) * Real.exp (-2*t*‖y-z‖^2)) =
        Real.exp (-t*‖x-y‖^2) * (Real.pi/(4*t)) ^ ((d:ℝ)/2) := by
    simp_rw [gaussian_gram_pointwise]
    rw [integral_const_mul]
    have htrans := integral_sub_right_eq_self (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
      (fun z => Real.exp (-4*t*‖z‖^2)) ((1/2:ℝ) • (x+y))
    rw [htrans]
    simp only [neg_mul]
    have hg := GaussianFourier.integral_rexp_neg_mul_sq_norm
      (V := EuclideanSpace ℝ (Fin d)) (by positivity : 0 < 4*t)
    simp only [neg_mul] at hg
    rw [hg]
    simp
  have soft_riesz_mixture_integrable (d : ℕ) (s ε : ℝ) (hs : 0 < s) (hε : 0 < ε)
      (x y : EuclideanSpace ℝ (Fin d)) :
      IntegrableOn (fun t : ℝ => t ^ (s/2-1) * Real.exp (-t*ε^2) *
        Real.exp (-t*‖x-y‖^2)) (Ioi 0) := by
    have hr : 0 < ‖x-y‖^2 + ε^2 := by positivity
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := s/2-1) (p := 1) (b := ‖x-y‖^2 + ε^2) (by linarith) (by norm_num) hr
    simp only [Real.rpow_one] at h
    apply h.congr
    exact Filter.Eventually.of_forall fun t => by
      dsimp only
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
  have gaussian_quadratic_nonnegative (d : ℕ) (t : ℝ) (ht : 0 < t)
      (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
      (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : MemLp f 2 μ) :
      0 ≤ ∫ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
        f p.1*f p.2*Real.exp (-t*‖p.1-p.2‖^2) ∂μ.prod μ := by
    let E := EuclideanSpace ℝ (Fin d)
    let C := (Real.pi/(4*t)) ^ ((d:ℝ)/2)
    let Φ := fun (x z : E) => Real.exp (-2*t*‖x-z‖^2)
    let F := fun p : (E × E) × E => (f p.1.1*f p.1.2)*(Φ p.1.1 p.2*Φ p.1.2 p.2)
    have hC : 0 < C := Real.rpow_pos_of_pos (by positivity) _
    have hfi := hf.integrable (by norm_num)
    have hPhim : Continuous (fun p : (E × E) × E => Φ p.1.1 p.2*Φ p.1.2 p.2) := by
      dsimp [Φ]
      fun_prop
    have hFm : AEStronglyMeasurable F ((μ.prod μ).prod (volume : Measure E)) :=
      (hf.aestronglyMeasurable.comp_fst.mul hf.aestronglyMeasurable.comp_snd).comp_fst.mul
        hPhim.measurable.aestronglyMeasurable
    have hinner (p : E × E) : Integrable (fun z => F (p,z)) (volume : Measure E) := by
      dsimp only [F, Φ]
      exact (gaussian_feature_product_integrable d t ht p.1 p.2).const_mul (f p.1*f p.2)
    have hnorm (p : E × E) : (∫ z : E, ‖F (p,z)‖) =
        |f p.1*f p.2| *(Real.exp (-t*‖p.1-p.2‖^2)*C) := by
      calc
        _ = ∫ z : E, |f p.1*f p.2| *(Φ p.1 z*Φ p.2 z) := by
          apply integral_congr_ae
          exact Eventually.of_forall fun z => by
            dsimp [F, Φ]
            rw [abs_mul, abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))]
        _ = _ := by
          rw [integral_const_mul]
          dsimp [Φ, C]
          rw [gaussian_gram_integral d t ht]
    have hDint : Integrable (fun p : E × E => ∫ z : E, ‖F (p,z)‖) (μ.prod μ) := by
      have hb : Integrable (fun p : E × E => C*(|f p.1| *|f p.2|)) (μ.prod μ) := by
        simpa only [Real.norm_eq_abs] using (hfi.norm.mul_prod hfi.norm).const_mul C
      apply hb.mono' hFm.norm.integral_prod_right'
      exact Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun z => norm_nonneg _), hnorm, abs_mul]
        have he : Real.exp (-t*‖p.1-p.2‖^2) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖p.1-p.2‖])
        have hh := mul_le_mul_of_nonneg_left he
          (mul_nonneg (mul_nonneg (abs_nonneg (f p.1)) (abs_nonneg (f p.2))) hC.le)
        nlinarith only [hh]
    have hFint : Integrable F ((μ.prod μ).prod (volume : Measure E)) :=
      (integrable_prod_iff hFm).mpr ⟨Eventually.of_forall hinner, hDint⟩
    have hpos : 0 ≤ ∫ p : E × E, ∫ z : E, F (p,z) ∂volume ∂μ.prod μ := by
      rw [integral_integral_swap hFint]
      apply integral_nonneg
      intro z
      have he : (∫ p : E × E, F (p,z) ∂μ.prod μ) = (∫ x : E, f x*Φ x z ∂μ)^2 := by
        calc
          _ = ∫ p : E × E, (f p.1*Φ p.1 z)*(f p.2*Φ p.2 z) ∂μ.prod μ := by
            apply integral_congr_ae
            exact Eventually.of_forall fun p => by dsimp [F]; ring
          _ = _ := by
            simpa only [pow_two] using integral_prod_mul (μ := μ) (ν := μ)
              (fun x : E => f x*Φ x z) (fun x : E => f x*Φ x z)
      change 0 ≤ ∫ p : E × E, F (p,z) ∂μ.prod μ
      rw [he]
      exact sq_nonneg _
    have heq : (∫ p : E × E, ∫ z : E, F (p,z) ∂volume ∂μ.prod μ) =
        C*(∫ p : E × E, f p.1*f p.2*Real.exp (-t*‖p.1-p.2‖^2) ∂μ.prod μ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by
        dsimp [F, Φ]
        rw [integral_const_mul, gaussian_gram_integral d t ht]
        dsimp [C]
        ring
    rw [heq] at hpos
    exact (mul_nonneg_iff_of_pos_left hC).mp hpos
  have soft_riesz_gamma_integral_value (d : ℕ) (s ε : ℝ) (hs : 0 < s) (hε : 0 < ε)
      (x y : EuclideanSpace ℝ (Fin d)) :
      (∫ t : ℝ in Ioi 0, t ^ (s/2-1) * Real.exp (-t*ε^2) * Real.exp (-t*‖x-y‖^2)) =
        Real.Gamma (s/2)*(‖x-y‖^2+ε^2)^(-s/2) := by
    have hr : 0 < ‖x-y‖^2+ε^2 := by positivity
    have hfun : (fun t : ℝ => t ^ (s/2-1) * Real.exp (-t*ε^2) * Real.exp (-t*‖x-y‖^2)) =
        fun t => t ^ (s/2-1) * Real.exp (-((‖x-y‖^2+ε^2)*t)) := by
      funext t
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    rw [hfun, Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity) hr]
    rw [one_div, Real.inv_rpow hr.le, ← Real.rpow_neg hr.le]
    have hex : -(s/2) = -s/2 := by ring
    rw [hex]
    ring
  have soft_riesz_quadratic_nonnegative (d : ℕ) (s ε : ℝ) (hs : 0 < s) (hε : 0 < ε)
      (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
      (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : MemLp f 2 μ) :
      0 ≤ ∫ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
        f p.1*f p.2*((‖p.1-p.2‖^2+ε^2)^(-s/2)/s) ∂μ.prod μ := by
    let E := EuclideanSpace ℝ (Fin d)
    let τ := (volume : Measure ℝ).restrict (Ioi 0)
    let w := fun t : ℝ => t ^ (s/2-1)*Real.exp (-t*ε^2)
    let F := fun p : (E × E) × ℝ => (f p.1.1*f p.1.2)*(w p.2*Real.exp (-p.2*‖p.1.1-p.1.2‖^2))
    let C := Real.Gamma (s/2)*(ε^2)^(-s/2)
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hgamma : 0 < Real.Gamma (s/2) := Real.Gamma_pos_of_pos (by positivity)
    have hfi := hf.integrable (by norm_num)
    have hwm : Measurable (fun p : (E × E) × ℝ => w p.2*Real.exp (-p.2*‖p.1.1-p.1.2‖^2)) := by
      dsimp [w]
      fun_prop
    have hFm : AEStronglyMeasurable F ((μ.prod μ).prod τ) :=
      (hf.aestronglyMeasurable.comp_fst.mul hf.aestronglyMeasurable.comp_snd).comp_fst.mul
        hwm.aestronglyMeasurable
    have hinner (p : E × E) : Integrable (fun t => F (p,t)) τ := by
      dsimp only [F, w, τ]
      exact (soft_riesz_mixture_integrable d s ε hs hε p.1 p.2).const_mul (f p.1*f p.2)
    have hnorm (p : E × E) : (∫ t, ‖F (p,t)‖ ∂τ) =
        |f p.1*f p.2| * (Real.Gamma (s/2)*(‖p.1-p.2‖^2+ε^2)^(-s/2)) := by
      calc
        _ = ∫ t, |f p.1*f p.2| * (w t*Real.exp (-t*‖p.1-p.2‖^2)) ∂τ := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          have hp : 0 < t := ht
          dsimp only [F]
          rw [Real.norm_eq_abs, abs_mul]
          have hpos : 0 ≤ w t*Real.exp (-t*‖p.1-p.2‖^2) := by
            dsimp [w]
            positivity
          rw [abs_of_nonneg hpos]
        _ = _ := by
          rw [integral_const_mul]
          dsimp [w, τ]
          rw [soft_riesz_gamma_integral_value d s ε hs hε]
    have hDint : Integrable (fun p : E × E => ∫ t, ‖F (p,t)‖ ∂τ) (μ.prod μ) := by
      have hb : Integrable (fun p : E × E => C*(|f p.1| * |f p.2|)) (μ.prod μ) := by
        simpa only [Real.norm_eq_abs] using (hfi.norm.mul_prod hfi.norm).const_mul C
      apply hb.mono' hFm.norm.integral_prod_right'
      exact Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun t => norm_nonneg _), hnorm, abs_mul]
        have he : (‖p.1-p.2‖^2+ε^2)^(-s/2) ≤ (ε^2)^(-s/2) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg ‖p.1-p.2‖]) (by linarith)
        have hh := mul_le_mul_of_nonneg_left he
          (mul_nonneg (mul_nonneg (abs_nonneg (f p.1)) (abs_nonneg (f p.2))) hgamma.le)
        dsimp [C]
        nlinarith only [hh]
    have hFint : Integrable F ((μ.prod μ).prod τ) :=
      (integrable_prod_iff hFm).mpr ⟨Eventually.of_forall hinner,hDint⟩
    have hpos : 0 ≤ ∫ p : E × E, ∫ t, F (p,t) ∂τ ∂μ.prod μ := by
      rw [integral_integral_swap hFint]
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : 0 < t := ht
      change 0 ≤ ∫ p : E × E, F (p,t) ∂μ.prod μ
      have he : (∫ p : E × E, F (p,t) ∂μ.prod μ) =
          w t*(∫ p : E × E, f p.1*f p.2*Real.exp (-t*‖p.1-p.2‖^2) ∂μ.prod μ) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun p => by dsimp [F]; ring
      rw [he]
      exact mul_nonneg (mul_nonneg (Real.rpow_nonneg htpos.le _) (Real.exp_nonneg _))
        (gaussian_quadratic_nonnegative d t htpos μ f hf)
    have heq : (∫ p : E × E, ∫ t, F (p,t) ∂τ ∂μ.prod μ) =
        (s*Real.Gamma (s/2))*(∫ p : E × E, f p.1*f p.2*((‖p.1-p.2‖^2+ε^2)^(-s/2)/s) ∂μ.prod μ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by
        dsimp [F, w, τ]
        rw [integral_const_mul, soft_riesz_gamma_integral_value d s ε hs hε]
        field_simp
    rw [heq] at hpos
    exact (mul_nonneg_iff_of_pos_left (mul_pos hs hgamma)).mp hpos
  simpa only [RieszKernel, ne_of_gt hε, if_false] using
    soft_riesz_quadratic_nonnegative d s ε hs hε μ f hf
