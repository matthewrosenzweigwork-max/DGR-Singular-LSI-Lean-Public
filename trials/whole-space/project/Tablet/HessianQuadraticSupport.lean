module

public import Tablet.PotentialBounds
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Strong
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section
set_option maxHeartbeats 800000

-- [TABLET NODE: HessianQuadraticSupport]
theorem HessianQuadraticSupport {d : ℕ} (V : OneParticle d → ℝ)
    (κ : ℝ) (hV : PotentialBounds d κ V) (a x : OneParticle d) :
    StrongConvexOn Set.univ κ V ∧
    V a + fderiv ℝ V a (x - a) + κ / 2 * ‖x - a‖ ^ 2 ≤ V x := by
-- BODY
  have line_derivative {d : ℕ} (x v : OneParticle d) (t : ℝ) :
      HasDerivAt (fun r : ℝ => r • v + x) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).add_const x
  
  have potential_line_derivative {d : ℕ} (V : OneParticle d → ℝ)
      (hV : ContDiff ℝ 2 V) (x v : OneParticle d) (t : ℝ) :
      HasDerivAt (fun r : ℝ => V (r • v + x)) (fderiv ℝ V (t • v + x) v) t := by
    exact ((hV.differentiable (by norm_num)) (t • v + x)).hasFDerivAt.comp_hasDerivAt t
      (line_derivative x v t)
  
  have potential_line_second_derivative {d : ℕ} (V : OneParticle d → ℝ)
      (hV : ContDiff ℝ 2 V) (x v : OneParticle d) (t : ℝ) :
      HasDerivAt (fun r : ℝ => fderiv ℝ V (r • v + x) v)
        (EuclideanHessian V (t • v + x) v v) t := by
    have hD : Differentiable ℝ (fderiv ℝ V) :=
      (hV.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
    have hline := (hD (t • v + x)).hasFDerivAt.comp_hasDerivAt t (line_derivative x v t)
    simpa [Function.comp_def, EuclideanHessian] using hline.clm_apply (hasDerivAt_const t v)
  
  let compensatedLine {d : ℕ} (V : OneParticle d → ℝ) (κ : ℝ)
      (x v : OneParticle d) (t : ℝ) : ℝ := V (t • v + x) - κ / 2 * ‖v‖ ^ 2 * t ^ 2
  
  have compensatedLine_hasDerivAt {d : ℕ} (V : OneParticle d → ℝ)
      (hV : ContDiff ℝ 2 V) (κ : ℝ) (x v : OneParticle d) (t : ℝ) :
      HasDerivAt (compensatedLine V κ x v)
        (fderiv ℝ V (t • v + x) v - κ * ‖v‖ ^ 2 * t) t := by
    have hpow := ((hasDerivAt_id t).pow 2).const_mul (κ / 2 * ‖v‖ ^ 2)
    convert (potential_line_derivative V hV x v t).sub hpow using 1 <;>
      (try rfl) <;> (try simp [compensatedLine, Pi.sub_apply, id_eq]) <;> ring
  
  have compensatedLine_deriv {d : ℕ} (V : OneParticle d → ℝ)
      (hV : ContDiff ℝ 2 V) (κ : ℝ) (x v : OneParticle d) :
      deriv (compensatedLine V κ x v) =
        fun t => fderiv ℝ V (t • v + x) v - κ * ‖v‖ ^ 2 * t := by
    funext t
    exact (compensatedLine_hasDerivAt V hV κ x v t).deriv
  
  have compensatedLine_second_hasDerivAt {d : ℕ} (V : OneParticle d → ℝ)
      (hV : ContDiff ℝ 2 V) (κ : ℝ) (x v : OneParticle d) (t : ℝ) :
      HasDerivAt (deriv (compensatedLine V κ x v))
        (EuclideanHessian V (t • v + x) v v - κ * ‖v‖ ^ 2) t := by
    rw [compensatedLine_deriv V hV]
    convert (potential_line_second_derivative V hV x v t).sub
      ((hasDerivAt_id t).const_mul (κ * ‖v‖ ^ 2)) using 1 <;>
      (try rfl) <;> simp [Pi.sub_apply, id_eq, mul_one]
  
  have compensatedLine_convex {d : ℕ} (V : OneParticle d → ℝ)
      (hV : ContDiff ℝ 2 V) (κ : ℝ)
      (hH : ∀ z u, κ * ‖u‖ ^ 2 ≤ EuclideanHessian V z u u) (x v : OneParticle d) :
      ConvexOn ℝ Set.univ (compensatedLine V κ x v) := by
    apply convexOn_univ_of_deriv2_nonneg
    · intro t
      exact (compensatedLine_hasDerivAt V hV κ x v t).differentiableAt
    · intro t
      exact (compensatedLine_second_hasDerivAt V hV κ x v t).differentiableAt
    · intro t
      change 0 ≤ deriv (deriv (compensatedLine V κ x v)) t
      rw [(compensatedLine_second_hasDerivAt V hV κ x v t).deriv]
      exact sub_nonneg.mpr (hH (t • v + x) v)
  
  have hessian_quadratic_support {d : ℕ} (V : OneParticle d → ℝ)
      (hV : ContDiff ℝ 2 V) (κ : ℝ)
      (hH : ∀ z u, κ * ‖u‖ ^ 2 ≤ EuclideanHessian V z u u) (a x : OneParticle d) :
      V a + fderiv ℝ V a (x - a) + κ / 2 * ‖x - a‖ ^ 2 ≤ V x := by
    have hconv := compensatedLine_convex V hV κ hH a (x - a)
    have hs := hconv.le_slope_of_hasDerivAt (x := (0 : ℝ)) (y := (1 : ℝ))
      (by simp) (by simp) (by norm_num)
      (compensatedLine_hasDerivAt V hV κ a (x - a) 0)
    simp [slope_def_field, compensatedLine] at hs
    rw [map_sub]
    linarith
  have strongConvex_of_hessian {d : ℕ} (V : OneParticle d → ℝ)
      (hV : ContDiff ℝ 2 V) (κ : ℝ)
      (hH : ∀ z u, κ * ‖u‖ ^ 2 ≤ EuclideanHessian V z u u) :
      StrongConvexOn Set.univ κ V := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    have hconv := (compensatedLine_convex V hV κ hH y (x - y)).2
      (x := (1 : ℝ)) (y := (0 : ℝ)) (by simp) (by simp) ha hb hab
    have hpoint : a • (x - y) + y = a • x + b • y := by
      have hba : b = 1 - a := by linarith
      rw [hba, smul_sub, sub_smul, one_smul]
      abel
    simp only [compensatedLine, smul_eq_mul, mul_one, mul_zero, add_zero,
      one_smul, sub_add_cancel, zero_smul, zero_add, one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0),
      mul_one, mul_zero, sub_zero] at hconv
    rw [hpoint] at hconv
    change V (a • x + b • y) ≤ a * V x + b * V y - a * b * (κ / 2 * ‖x - y‖ ^ 2)
    have hb' : b = 1 - a := by linarith
    rw [hb'] at hconv ⊢
    nlinarith [hconv]
  exact ⟨strongConvex_of_hessian V hV.regularity κ hV.lower,
    hessian_quadratic_support V hV.regularity κ hV.lower a x⟩
