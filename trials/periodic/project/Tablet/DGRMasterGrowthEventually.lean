module

public import Tablet.DGRPowerGrowthEventually
public import Tablet.DGRLogGrowthEventually

@[expose] public section
-- [TABLET NODE: DGRMasterGrowthEventually]
theorem DGRMasterGrowthEventually (d : ℕ) (hd : 2≤d) (s C : ℝ)
    (hs : 0≤s) (hL : s<(d:ℝ)/2) (hC : 0≤C) :
    ∃N₀ : ℕ,2≤N₀ ∧ ∀N : ℕ,N₀≤N →
      C*(if s=0 then (Real.log (Real.exp 1+(N:ℝ)))^2 else (N:ℝ)^(2*s/(d:ℝ)))≤(N:ℝ) := by
-- BODY
  by_cases hz : s=0
  · simpa only [if_pos hz] using DGRLogGrowthEventually C hC
  · have hdp : 0<(d:ℝ) := by exact_mod_cast (show 0<d by omega)
    have hp : 2*s/(d:ℝ)<1 := (div_lt_one hdp).mpr (by linarith)
    simpa only [if_neg hz] using DGRPowerGrowthEventually (2*s/(d:ℝ)) C hp hC
