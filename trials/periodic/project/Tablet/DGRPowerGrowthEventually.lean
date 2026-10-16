import Tablet.Preamble
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic
open Filter
open scoped Topology
-- [TABLET NODE: DGRPowerGrowthEventually]
theorem DGRPowerGrowthEventually (p C : ℝ) (hp : p<1) (hC : 0≤C) :
    ∃N₀ : ℕ,2≤N₀ ∧ ∀N : ℕ,N₀≤N → C*(N:ℝ)^p≤(N:ℝ) := by
-- BODY
  have hlim := ((tendsto_rpow_neg_atTop (show 0<1-p by linarith)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul C
  simp only [mul_zero] at hlim
  have he := hlim.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))
  obtain ⟨n,hn⟩ := eventually_atTop.mp he
  refine ⟨max 2 n,le_max_left _ _,?_⟩
  intro N hN
  have hN2 : 2≤N := (le_max_left _ _).trans hN
  have hNp : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hh := (hn N ((le_max_right _ _).trans hN)).le
  have hm := mul_le_mul_of_nonneg_right hh hNp.le
  dsimp only [Function.comp_apply] at hm
  rw [one_mul] at hm
  have hpower : (N:ℝ)^(-(1-p))*(N:ℝ)=(N:ℝ)^p := by
    calc
      _=(N:ℝ)^(-(1-p))*(N:ℝ)^(1:ℝ) := by rw [Real.rpow_one]
      _=(N:ℝ)^(-(1-p)+1) := (Real.rpow_add hNp _ _).symm
      _=(N:ℝ)^p := by congr 1; ring
  calc
    C*(N:ℝ)^p=C*((N:ℝ)^(-(1-p))*(N:ℝ)) := by rw [hpower]
    _≤(N:ℝ) := by nlinarith only [hm]
