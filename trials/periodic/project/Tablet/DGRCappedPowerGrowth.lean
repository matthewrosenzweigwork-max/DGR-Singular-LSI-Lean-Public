module

public import Tablet.Preamble
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section
-- [TABLET NODE: DGRCappedPowerGrowth]
theorem DGRCappedPowerGrowth (N θ C u m A : ℝ)
    (hN : 1≤N) (hθ : 0<θ) (hθ1 : θ<1) (hC : 1≤C) (hu : 1≤u)
    (hm : 0≤m) (hA : 0≤A)
    (hmb : m≤C*(1+(N/u)^θ)) (hAb : A≤C*(1+(N/u)^θ)) :
    min u m*(1+A)≤6*C^2*N^(2*θ/(1+θ)) := by
-- BODY
  let γ := θ/(1+θ)
  have hNp : 0<N := zero_lt_one.trans_le hN
  have hup : 0<u := zero_lt_one.trans_le hu
  have hCp : 0<C := zero_lt_one.trans_le hC
  have hγ : 0<γ := div_pos hθ (by positivity)
  have hexp : θ+γ*(1-θ)=2*γ := by dsimp [γ]; field_simp; ring
  have hexp' : θ*(1-γ)=γ := by dsimp [γ]; field_simp; ring
  have hv1 : 1≤N^γ := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow (by norm_num : (0:ℝ)≤1) hN hγ.le
  have hNpow : N^γ≤N^(2*γ) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hf0 : 0≤1+(N/u)^θ := by positivity
  have hmin0 : 0≤min u m := le_min hup.le hm
  have htarget : 2*θ/(1+θ)=2*γ := by dsimp [γ]; ring
  rw [htarget]
  by_cases huv : u≤N^γ
  · have hscale : u*(N/u)^θ=N^θ*u^(1-θ) := by
      rw [Real.div_rpow hNp.le hup.le,Real.rpow_sub hup,Real.rpow_one]
      field_simp
    have hupow := Real.rpow_le_rpow hup.le huv (by linarith : 0≤1-θ)
    rw [← Real.rpow_mul hNp.le] at hupow
    have hproduct := mul_le_mul_of_nonneg_left hupow (Real.rpow_nonneg hNp.le θ)
    rw [← Real.rpow_add hNp,hexp] at hproduct
    have huf : u*(1+(N/u)^θ)≤2*N^(2*γ) := by
      have huu := huv.trans hNpow
      rw [mul_add,mul_one,hscale]
      linarith
    have hsmall := mul_le_mul_of_nonneg_right (min_le_left u m) (show 0≤1+A by linarith)
    have hreplace := mul_le_mul_of_nonneg_left hAb hup.le
    have hCf := mul_le_mul_of_nonneg_left huf hCp.le
    have huu := huv.trans hNpow
    have hfactor : 1+2*C≤6*C^2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hNp.le (2*γ))
    nlinarith
  · have hvu : N^γ≤u := le_of_not_ge huv
    have hratio : N/u≤N/(N^γ) := div_le_div_of_nonneg_left hNp.le (by positivity) hvu
    have hpower := Real.rpow_le_rpow (show 0≤N/u by positivity) hratio hθ.le
    have he : (N/(N^γ))^θ=N^γ := by
      have hquot : N/(N^γ)=N^(1-γ) := by rw [Real.rpow_sub hNp,Real.rpow_one]
      rw [hquot,← Real.rpow_mul hNp.le]
      congr 1
      nlinarith only [hexp']
    rw [he] at hpower
    have hf : C*(1+(N/u)^θ)≤2*C*N^γ := by
      have hh := mul_le_mul_of_nonneg_left (show 1+(N/u)^θ≤2*N^γ by linarith) hCp.le
      nlinarith
    have hm' := hmb.trans hf
    have hA' := hAb.trans hf
    have hCpow : 1≤C*N^γ := by
      nlinarith only [hC,hv1,mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hv1)]
    have h1A : 1+A≤3*C*N^γ := by linarith
    have hmin : min u m≤2*C*N^γ := (min_le_right u m).trans hm'
    have hh := mul_le_mul hmin h1A (show 0≤1+A by linarith) (by positivity : 0≤2*C*N^γ)
    have he : (2*C*N^γ)*(3*C*N^γ)=6*C^2*N^(2*γ) := by
      rw [show 2*γ=γ+γ by ring,Real.rpow_add hNp]; ring
    exact hh.trans_eq he
