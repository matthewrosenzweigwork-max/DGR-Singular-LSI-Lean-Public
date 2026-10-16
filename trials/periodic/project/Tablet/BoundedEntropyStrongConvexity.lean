import Tablet.Preamble
import Mathlib.Analysis.Convex.Deriv

-- [TABLET NODE: BoundedEntropyStrongConvexity]
theorem BoundedEntropyStrongConvexity (M : ℝ) (hM : 0 < M)
    (x y : ℝ) (hx : x ∈ Set.Icc 0 M) (hy : y ∈ Set.Icc 0 M) :
    ((x + y) / 2) * Real.log ((x + y) / 2) ≤
      (x * Real.log x + y * Real.log y) / 2 - (x - y) ^ 2 / (8 * M) := by
-- BODY
  let F : ℝ → ℝ := fun z => z * Real.log z - z ^ 2 / (2 * M)
  let D : ℝ → ℝ := fun z => Real.log z + 1 - z / M
  have hcv : ConvexOn ℝ (Set.Icc 0 M) F := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 M)
      (f' := D) (f'' := fun z => z⁻¹ - M⁻¹)
    · exact (Real.continuous_mul_log.sub ((continuous_id.pow 2).div_const _)).continuousOn
    · intro z hz
      have hzp : 0 < z := (show z ∈ Set.Ioo 0 M by simpa only [interior_Icc] using hz).1
      have hd := (Real.hasDerivAt_mul_log hzp.ne').sub
        ((hasDerivAt_id z).pow 2 |>.div_const (2 * M))
      convert! hd.hasDerivWithinAt using 1
      simp [D]
      field_simp
    · intro z hz
      have hzp : 0 < z := (show z ∈ Set.Ioo 0 M by simpa only [interior_Icc] using hz).1
      have hd := ((Real.hasDerivAt_log hzp.ne').add_const 1).sub
        ((hasDerivAt_id z).div_const M)
      convert! hd.hasDerivWithinAt using 1
      simp
    · intro z hz
      have hz' : z ∈ Set.Ioo 0 M := by simpa only [interior_Icc] using hz
      exact sub_nonneg.mpr (inv_anti₀ hz'.1 hz'.2.le)
  have hh := hcv.2 hx hy (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num)
  simp only [smul_eq_mul] at hh
  have hmid : (1 : ℝ) / 2 * x + 1 / 2 * y = (x + y) / 2 := by ring
  rw [hmid] at hh
  dsimp [F] at hh
  have hid :
      (1 / 2 * (x ^ 2 / (2 * M)) + 1 / 2 * (y ^ 2 / (2 * M))) -
        ((x + y) / 2) ^ 2 / (2 * M) = (x - y) ^ 2 / (8 * M) := by
    field_simp
    ring
  linarith
