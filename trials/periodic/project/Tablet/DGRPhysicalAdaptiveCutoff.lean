import Tablet.RieszMellinCoefficientBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
open scoped BigOperators
-- [TABLET NODE: DGRPhysicalAdaptiveCutoff]
theorem DGRPhysicalAdaptiveCutoff (d N : ℕ) (hN : 1≤N)
    (s a M t η₀ : ℝ) (hsd : s<(d:ℝ)) (ha : 0<a) (hM : 1≤M) (ht : 0<t)
    (hη₀ : 0<η₀) (hη₀1 : η₀≤1)
    (K : Finset (Fin d→ℤ)) :
    let α := ((d:ℝ)-s)/2
    let b := (a/Real.Gamma α)/α
    let B := ∑k∈K,if k=0 then (0:ℝ) else a*(4*Real.pi^2*∑j,(k j:ℝ)^2)^(-((d:ℝ)-s)/2)
    let U := max 1 (6*t*B)
    1≤U ∧ ∀ u : ℝ,U≤u →
      let η := min η₀ ((u/(8*t*(N:ℝ)*M*b))^(1/((d:ℝ)-s)))
      0<η ∧ η≤η₀ ∧ η≤1 ∧
      t*((N:ℝ)-1)*M*(b*η^((d:ℝ)-s))≤u/8 ∧
      2*t*(∑k∈K,RieszMellinCoefficient d s a (η^2) 0 k)≤u/3 := by
-- BODY
  classical
  let α := ((d:ℝ)-s)/2
  let b := (a/Real.Gamma α)/α
  let B := ∑k∈K,if k=0 then (0:ℝ) else a*(4*Real.pi^2*∑j,(k j:ℝ)^2)^(-((d:ℝ)-s)/2)
  let U := max 1 (6*t*B)
  have hα : 0<α := by dsimp [α]; linarith
  have hb : 0<b := div_pos (div_pos ha (Real.Gamma_pos_of_pos hα)) hα
  have hds : 0<(d:ℝ)-s := sub_pos.mpr hsd
  have hNp : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hMp : 0<M := zero_lt_one.trans_le hM
  change 1≤U ∧ _
  refine ⟨le_max_left _ _,?_⟩
  intro u hu
  have hu1 : 1≤u := (le_max_left _ _).trans hu
  have hup : 0<u := zero_lt_one.trans_le hu1
  let x := u/(8*t*(N:ℝ)*M*b)
  let η := min η₀ (x^(1/((d:ℝ)-s)))
  have hx : 0<x := div_pos hup (by positivity)
  have hη : 0<η := lt_min hη₀ (Real.rpow_pos_of_pos hx _)
  have hηbound : η≤η₀ := min_le_left _ _
  have hnear : t*(N:ℝ)*M*b*η^((d:ℝ)-s)≤u/8 := by
    have hpow := Real.rpow_le_rpow hη.le (min_le_right η₀ (x^(1/((d:ℝ)-s)))) hds.le
    rw [← Real.rpow_mul hx.le,one_div_mul_cancel hds.ne',Real.rpow_one] at hpow
    have hh := mul_le_mul_of_nonneg_left hpow (show 0≤t*(N:ℝ)*M*b by positivity)
    have he : t*(N:ℝ)*M*b*x=u/8 := by dsimp [x]; field_simp
    exact hh.trans_eq he
  change 0<η ∧ η≤η₀ ∧ η≤1 ∧ _ ∧ _
  refine ⟨hη,hηbound,hηbound.trans hη₀1,?_,?_⟩
  · change t*((N:ℝ)-1)*M*(b*η^((d:ℝ)-s))≤u/8
    have hh := mul_le_mul_of_nonneg_right (show (N:ℝ)-1≤(N:ℝ) by linarith)
      (show 0≤t*M*b*η^((d:ℝ)-s) by positivity)
    nlinarith
  · change 2*t*(∑k∈K,RieszMellinCoefficient d s a (η^2) 0 k)≤u/3
    have hc := RieszMellinCoefficientBounds d s a hsd ha (η^2) 0 (sq_pos_of_pos hη) le_rfl
    have hsum : (∑k∈K,RieszMellinCoefficient d s a (η^2) 0 k)≤B :=
      Finset.sum_le_sum fun k _ => (hc.2.2 k).2.1
    have hB : 6*t*B≤u := (le_max_right _ _).trans hu
    have hh := mul_le_mul_of_nonneg_left hsum (show 0≤2*t by positivity)
    nlinarith
