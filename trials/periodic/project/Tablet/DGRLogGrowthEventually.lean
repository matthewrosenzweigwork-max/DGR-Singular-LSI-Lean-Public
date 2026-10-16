import Tablet.DGRPowerGrowthEventually
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
open scoped Topology
-- [TABLET NODE: DGRLogGrowthEventually]
theorem DGRLogGrowthEventually (C : ℝ) (hC : 0≤C) :
    ∃N₀ : ℕ,2≤N₀ ∧ ∀N : ℕ,N₀≤N → C*(Real.log (Real.exp 1+(N:ℝ)))^2≤(N:ℝ) := by
-- BODY
  let B := (Real.exp 1+1)^((1:ℝ)/4)
  have hB : 0<B := Real.rpow_pos_of_pos (by positivity) _
  obtain ⟨N₀,hN₀,hevent⟩ := DGRPowerGrowthEventually (1/2:ℝ) (16*C*B^2) (by norm_num) (by positivity)
  refine ⟨N₀,hN₀,?_⟩
  intro N hN
  have hN2 : 2≤N := hN₀.trans hN
  have hNr : 1≤(N:ℝ) := by exact_mod_cast (show 1≤N by omega)
  have hNp : 0<(N:ℝ) := zero_lt_one.trans_le hNr
  have hx : 0<Real.exp 1+(N:ℝ) := by positivity
  have hlog0 : 0≤Real.log (Real.exp 1+(N:ℝ)) :=
    Real.log_nonneg (by linarith [Real.exp_pos (1:ℝ)])
  have hlog := Real.log_le_rpow_div hx.le (by norm_num : (0:ℝ)<1/4)
  have hbase : Real.exp 1+(N:ℝ)≤(Real.exp 1+1)*(N:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hNr (Real.exp_nonneg (1:ℝ))
    nlinarith only [hh]
  have hpow := Real.rpow_le_rpow hx.le hbase (by norm_num : (0:ℝ)≤1/4)
  rw [Real.mul_rpow (by positivity : (0:ℝ)≤Real.exp 1+1) hNp.le] at hpow
  have hlogB : Real.log (Real.exp 1+(N:ℝ))≤4*B*(N:ℝ)^((1:ℝ)/4) := by
    change (Real.exp 1+(N:ℝ))^((1:ℝ)/4)≤B*(N:ℝ)^((1:ℝ)/4) at hpow
    nlinarith only [hlog,hpow]
  have hsq : (Real.log (Real.exp 1+(N:ℝ)))^2≤16*B^2*(N:ℝ)^((1:ℝ)/2) := by
    have hh := pow_le_pow_left₀ hlog0 hlogB 2
    have hp : ((N:ℝ)^((1:ℝ)/4))^2=(N:ℝ)^((1:ℝ)/2) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hNp.le]
      congr 1
      norm_num
    rw [mul_pow,mul_pow,hp] at hh
    nlinarith only [hh]
  have hh := mul_le_mul_of_nonneg_left hsq hC
  exact (by nlinarith only [hh] : C*(Real.log (Real.exp 1+(N:ℝ)))^2≤16*C*B^2*(N:ℝ)^((1:ℝ)/2)).trans
    (hevent N hN)
