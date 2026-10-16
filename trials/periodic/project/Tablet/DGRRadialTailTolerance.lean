import Tablet.Preamble
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic
open Filter Set
open scoped Topology
-- [TABLET NODE: DGRRadialTailTolerance]
theorem DGRRadialTailTolerance (p q C D L : ℝ)
    (hp : 0<p) (hq : 0<q) (hC : 0<C) (hD : 0<D) (hL : 1≤L) :
    ∃κ : ℝ,1≤κ ∧ 0<C*κ^(-p) ∧ 0<D*κ^(-q) ∧
      C*κ^(-p)≤1/L ∧ D*κ^(-q)≤1/L := by
-- BODY
  have hLp : 0<L := zero_lt_one.trans_le hL
  have hlimC := (tendsto_rpow_neg_atTop hp).const_mul C
  have hlimD := (tendsto_rpow_neg_atTop hq).const_mul D
  simp only [mul_zero] at hlimC hlimD
  have heC := hlimC.eventually (Iio_mem_nhds (one_div_pos.mpr hLp))
  have heD := hlimD.eventually (Iio_mem_nhds (one_div_pos.mpr hLp))
  obtain ⟨κ,hκ,heC,heD⟩ := ((eventually_ge_atTop (1:ℝ)).and (heC.and heD)).exists
  have hκp : 0<κ := zero_lt_one.trans_le hκ
  exact ⟨κ,hκ,mul_pos hC (Real.rpow_pos_of_pos hκp _),
    mul_pos hD (Real.rpow_pos_of_pos hκp _),heC.le,heD.le⟩
