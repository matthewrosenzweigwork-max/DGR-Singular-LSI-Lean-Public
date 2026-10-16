module

public import Tablet.Preamble
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

@[expose] public section
-- [TABLET NODE: DGRCappedLogGrowth]
theorem DGRCappedLogGrowth (N C u m A : ℝ)
    (hN : 1≤N) (hC : 1≤C) (hu : 1≤u) (hm : 0≤m) (hA : 0≤A)
    (hmb : m≤C*(1+Real.log N)) (hAb : A≤C*(1+Real.log N)) :
    min u m*(1+A)≤8*C^2*(Real.log (Real.exp 1+N))^2 := by
-- BODY
  have hNp : 0<N := zero_lt_one.trans_le hN
  have hCp : 0<C := zero_lt_one.trans_le hC
  have hlogN : 0≤Real.log N := Real.log_nonneg hN
  have hbase : 1≤C*(1+Real.log N) := by
    have hh := mul_nonneg hCp.le hlogN
    nlinarith only [hC,hh]
  have hmin : min u m≤C*(1+Real.log N) := (min_le_right u m).trans hmb
  have h1A : 1+A≤2*C*(1+Real.log N) := by linarith only [hAb,hbase]
  have hproduct := mul_le_mul hmin h1A (show 0≤1+A by linarith) (by positivity : 0≤C*(1+Real.log N))
  have hsum : Real.exp 1≤Real.exp 1+N := by linarith only [hNp]
  have hlog1 : 1≤Real.log (Real.exp 1+N) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hsum
  have hlogcmp : Real.log N≤Real.log (Real.exp 1+N) :=
    Real.log_le_log hNp (by linarith only [Real.exp_pos (1:ℝ)])
  have hsq : (1+Real.log N)^2≤4*(Real.log (Real.exp 1+N))^2 := by
    nlinarith only [hlogN,hlog1,hlogcmp]
  have hh := mul_le_mul_of_nonneg_left hsq (show 0≤2*C^2 by positivity)
  nlinarith only [hproduct,hh]
