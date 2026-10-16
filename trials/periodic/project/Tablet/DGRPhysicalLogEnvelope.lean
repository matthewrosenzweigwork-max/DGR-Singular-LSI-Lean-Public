module

public import Tablet.Preamble
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section
-- [TABLET NODE: DGRPhysicalLogEnvelope]
theorem DGRPhysicalLogEnvelope (p c N u : ℝ)
    (hp : 0<p) (hc : 0<c) (hN : 1≤N) (hu : 1≤u) :
    let η := min 1 ((u/(c*N))^(1/p))
    |Real.log (η^2)|≤(2/p)*(|Real.log c|+Real.log N) := by
-- BODY
  have hNp : 0<N := zero_lt_one.trans_le hN
  have hup : 0<u := zero_lt_one.trans_le hu
  let x := u/(c*N)
  have hx : 0<x := div_pos hup (mul_pos hc hNp)
  have hlogN : 0≤Real.log N := Real.log_nonneg hN
  have hlogu : 0≤Real.log u := Real.log_nonneg hu
  change |Real.log ((min 1 (x^(1/p)))^2)|≤(2/p)*(|Real.log c|+Real.log N)
  by_cases hh : 1≤x^(1/p)
  · rw [min_eq_left hh]; norm_num
    positivity
  · have hη : 0<x^(1/p) := Real.rpow_pos_of_pos hx _
    have hlogη : Real.log (x^(1/p))≤0 := Real.log_nonpos hη.le (le_of_not_ge hh)
    rw [min_eq_right (le_of_not_ge hh),Real.log_pow,abs_mul]
    norm_num only [Nat.cast_ofNat,abs_of_nonneg (show (0:ℝ)≤2 by norm_num)]
    rw [abs_of_nonpos hlogη,Real.log_rpow hx]
    have hlogx : Real.log x=Real.log u-(Real.log c+Real.log N) := by
      dsimp [x]
      rw [Real.log_div hup.ne' (mul_pos hc hNp).ne',Real.log_mul hc.ne' hNp.ne']
    rw [hlogx]
    have habs := le_abs_self (Real.log c)
    have hh' := mul_le_mul_of_nonneg_left (show Real.log c+Real.log N-Real.log u≤
      |Real.log c|+Real.log N by linarith) (show 0≤2/p by positivity)
    convert! hh' using 1 <;> ring
