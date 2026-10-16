module

public import Tablet.Preamble
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

@[expose] public section
open MeasureTheory Set

-- Exact physical-radius to heat-time substitution; no integrability oracle.
-- [TABLET NODE: GaussianPhysicalScaleIntegral]
theorem GaussianPhysicalScaleIntegral (α η : ℝ) (hη : 0 < η) (H : ℝ → ℝ) :
    (∫ t in Ioc (0 : ℝ) (η^2), t^(α-1)*H t) =
      2 * ∫ ρ in Ioc (0 : ℝ) η, ρ^(2*α-1)*H (ρ^2) ∧
    (∫ t in Ioi (η^2), t^(α-1)*H t) =
      2 * ∫ ρ in Ioi η, ρ^(2*α-1)*H (ρ^2) := by
-- BODY
  have hder (x : ℝ) : HasDerivAt (fun z : ℝ => z^2) (2*x) x := by
    convert! (hasDerivAt_id x).pow 2 using 1 <;> simp
  have hinj (S : Set ℝ) (hS : ∀ x ∈ S, 0 < x) : InjOn (fun x : ℝ => x^2) S := by
    intro x hx y hy hxy
    have hx0 := hS x hx
    have hy0 := hS y hy
    nlinarith
  have himgNear : (fun x : ℝ => x^2) '' Ioc 0 η = Ioc 0 (η^2) := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨sq_pos_of_pos hx.1, pow_le_pow_left₀ hx.1.le hx.2 2⟩
    · intro ht
      refine ⟨Real.sqrt t, ⟨Real.sqrt_pos.mpr ht.1, ?_⟩, Real.sq_sqrt ht.1.le⟩
      exact (Real.sqrt_le_iff).mpr ⟨hη.le, ht.2⟩
  have himgLong : (fun x : ℝ => x^2) '' Ioi η = Ioi (η^2) := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      change η < x at hx
      have hx0 : 0 < x := hη.trans hx
      change η^2 < x^2
      nlinarith [mul_pos (sub_pos.mpr hx) (show 0 < x+η by linarith)]
    · intro ht
      have ht0 : 0 < t := (sq_pos_of_pos hη).trans ht
      refine ⟨Real.sqrt t, ?_, Real.sq_sqrt ht0.le⟩
      exact (Real.lt_sqrt hη.le).mpr ht
  have hpoint (x : ℝ) (hx : 0 < x) :
      |2*x| • ((x^2)^(α-1)*H (x^2)) = 2*(x^(2*α-1)*H (x^2)) := by
    rw [abs_of_pos (mul_pos (by norm_num) hx)]
    simp only [smul_eq_mul]
    have hp : x*(x^2)^(α-1) = x^(2*α-1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
      calc
        _ = x^(1:ℝ)*x^((2:ℝ)*(α-1)) := by rw [Real.rpow_one]; norm_num
        _ = x^((1:ℝ)+2*(α-1)) := (Real.rpow_add hx _ _).symm
        _ = _ := by congr 1; ring
    calc
      (2*x)*((x^2)^(α-1)*H (x^2)) = 2*(x*(x^2)^(α-1))*H (x^2) := by ring
      _ = _ := by rw [hp]; ring
  constructor
  · have hh := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc
      (fun x _ => (hder x).hasDerivWithinAt)
      (hinj (Ioc 0 η) (fun _ hx => hx.1)) (fun t => t^(α-1)*H t)
    rw [himgNear] at hh
    rw [hh]
    calc
      _ = ∫ x in Ioc 0 η, 2*(x^(2*α-1)*H (x^2)) :=
        setIntegral_congr_fun measurableSet_Ioc (fun x hx => hpoint x hx.1)
      _ = _ := integral_const_mul _ _
  · have hh := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun x _ => (hder x).hasDerivWithinAt)
      (hinj (Ioi η) (fun _ hx => hη.trans hx)) (fun t => t^(α-1)*H t)
    rw [himgLong] at hh
    rw [hh]
    calc
      _ = ∫ x in Ioi η, 2*(x^(2*α-1)*H (x^2)) :=
        setIntegral_congr_fun measurableSet_Ioi (fun x hx => hpoint x (hη.trans hx))
      _ = _ := integral_const_mul _ _
