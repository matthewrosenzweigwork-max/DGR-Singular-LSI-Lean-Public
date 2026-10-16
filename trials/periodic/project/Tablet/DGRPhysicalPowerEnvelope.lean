import Tablet.Preamble
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
-- [TABLET NODE: DGRPhysicalPowerEnvelope]
theorem DGRPhysicalPowerEnvelope (p s c N u : ℝ)
    (hp : 0<p) (hs : 0<s) (hc : 0<c) (hN : 1≤N) (hu : 1≤u) :
    let η := min 1 ((u/(c*N))^(1/p))
    η^(-s)≤1+c^(s/p)*(N/u)^(s/p) := by
-- BODY
  have hNp : 0<N := zero_lt_one.trans_le hN
  have hup : 0<u := zero_lt_one.trans_le hu
  let x := u/(c*N)
  have hx : 0<x := div_pos hup (mul_pos hc hNp)
  let θ := s/p
  have hθ : 0<θ := div_pos hs hp
  change (min 1 (x^(1/p)))^(-s)≤1+c^θ*(N/u)^θ
  by_cases hh : 1≤x^(1/p)
  · rw [min_eq_left hh,Real.one_rpow]
    linarith [mul_nonneg (Real.rpow_nonneg hc.le θ) (Real.rpow_nonneg (show 0≤N/u by positivity) θ)]
  · rw [min_eq_right (le_of_not_ge hh),←Real.rpow_mul hx.le]
    have he : (1/p)*(-s)=-θ := by dsimp [θ]; ring
    rw [he,Real.rpow_neg_eq_inv_rpow]
    have hi : x⁻¹=c*(N/u) := by dsimp [x]; field_simp
    rw [hi,Real.mul_rpow hc.le (by positivity : 0≤N/u)]
    linarith
