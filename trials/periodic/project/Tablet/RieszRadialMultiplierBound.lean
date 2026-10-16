import Tablet.Preamble
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic
open scoped BigOperators
-- [TABLET NODE: RieszRadialMultiplierBound]
theorem RieszRadialMultiplierBound (d:ℕ) (s a:ℝ) (hsd:s<(d:ℝ)) (ha:0<a) :
    ∃ C:ℝ,0<C ∧ ∀κ:ℝ,1≤κ → ∀k:Fin d→ℤ,
      κ^2<∑j,(k j:ℝ)^2 →
      (if k=0 then 0 else a*(4*Real.pi^2*∑j,(k j:ℝ)^2)^(-((d:ℝ)-s)/2))≤C*κ^(s-(d:ℝ)) := by
-- BODY
  classical
  let C:=a*(4*Real.pi^2)^(-((d:ℝ)-s)/2)
  have hC:0<C := by dsimp [C];positivity
  refine ⟨C,hC,?_⟩
  intro κ hκ k htail
  have hκpos:0<κ := lt_of_lt_of_le (by norm_num) hκ
  have hq:0<∑j,(k j:ℝ)^2 := lt_trans (sq_pos_of_pos hκpos) htail
  have hk:k≠0 := by
    intro hz
    subst k
    simpa using hq
  rw [if_neg hk]
  have hb : (∑j,(k j:ℝ)^2)^(-((d:ℝ)-s)/2)≤κ^(s-(d:ℝ)) := by
    have h:=Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hκpos) htail.le
      (by linarith : -((d:ℝ)-s)/2≤0)
    have he : (κ^2)^(-((d:ℝ)-s)/2)=κ^(s-(d:ℝ)) := by
      rw [←Real.rpow_two,←Real.rpow_mul hκpos.le]
      congr 1
      ring
    exact he ▸ h
  rw [Real.mul_rpow (by positivity : (0:ℝ)≤4*Real.pi^2) hq.le]
  have hc:a*(4*Real.pi^2)^(-((d:ℝ)-s)/2)=C := rfl
  rw [←mul_assoc,hc]
  exact mul_le_mul_of_nonneg_left hb hC.le
