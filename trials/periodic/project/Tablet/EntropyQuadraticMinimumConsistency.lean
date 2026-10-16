import Tablet.BoundedDensityEntropyMidpoint
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
open MeasureTheory
open scoped Topology

-- [TABLET NODE: EntropyQuadraticMinimumConsistency]
theorem EntropyQuadraticMinimumConsistency {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M β : ℝ) (hM : 0 < M)
    (a : Lp ℝ 2 μ) (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hself : ∀ u v, inner ℝ u (T v) = inner ℝ (T u) v)
    (r ν : Lp ℝ 2 μ)
    (hr : ∀ᵐ x ∂μ, r x ∈ Set.Icc 0 M) (hν : ∀ᵐ x ∂μ, ν x ∈ Set.Icc 0 M)
    (hrm : (∫ x, r x ∂μ) = 1) (hνm : (∫ x, ν x ∂μ) = 1)
    (hmin : ∀ f : Lp ℝ 2 μ, (∀ᵐ x ∂μ, f x ∈ Set.Icc 0 M) → (∫ x, f x ∂μ) = 1 →
      (∫ x, r x * Real.log (r x) ∂μ) - inner ℝ r a + β/2 * inner ℝ r (T r) ≤
      (∫ x, f x * Real.log (f x) ∂μ) - inner ℝ f a + β/2 * inner ℝ f (T f))
    (hlinear : ∀ f : Lp ℝ 2 μ, (∀ᵐ x ∂μ, f x ∈ Set.Icc 0 M) → (∫ x, f x ∂μ) = 1 →
      (∫ x, ν x * Real.log (ν x) ∂μ) - inner ℝ ν (a - β • T r) ≤
      (∫ x, f x * Real.log (f x) ∂μ) - inner ℝ f (a - β • T r)) : r = ν := by
-- BODY
  let E : Lp ℝ 2 μ → ℝ := fun f => ∫ x, f x * Real.log (f x) ∂μ
  let b := a - β • T r
  let J : Lp ℝ 2 μ → ℝ := fun f => E f - inner ℝ f b
  let D : ℝ := J r - J ν
  let Q : ℝ := β/2 * inner ℝ (ν-r) (T (ν-r))
  have hDl : 0 ≤ D := sub_nonneg.mpr (hlinear r hr hrm)
  have hbound (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) : D ≤ Q*t := by
    let z : Lp ℝ 2 μ := (1-t) • r + t • ν
    have hzeq : ∀ᵐ x ∂μ, z x = (1-t) * r x + t * ν x := by
      filter_upwards [Lp.coeFn_add ((1-t) • r) (t • ν),
        Lp.coeFn_smul (1-t) r, Lp.coeFn_smul t ν] with x hx hy hw
      change ((1-t) • r + t • ν) x = _
      rw [hx]
      simp only [Pi.add_apply, hy, hw, Pi.smul_apply, smul_eq_mul]
    have hzb : ∀ᵐ x ∂μ, z x ∈ Set.Icc 0 M := by
      filter_upwards [hzeq, hr, hν] with x hx hux hvx
      rw [hx]
      exact convex_Icc 0 M hux hvx (sub_nonneg.mpr ht1) ht.le (by ring)
    have hri := (Lp.memLp r).integrable (by norm_num : (1 : ENNReal) ≤ 2)
    have hνi := (Lp.memLp ν).integrable (by norm_num : (1 : ENNReal) ≤ 2)
    have hzm : (∫ x, z x ∂μ) = 1 := by
      rw [integral_congr_ae hzeq, integral_add (hri.const_mul _) (hνi.const_mul _),
        integral_const_mul, integral_const_mul, hrm, hνm]
      ring
    have hint (f : Lp ℝ 2 μ) (hf : ∀ᵐ x ∂μ, f x ∈ Set.Icc 0 M) :=
      (BoundedDensityEntropyMidpoint μ f f M hM
        (Lp.aestronglyMeasurable f) (Lp.aestronglyMeasurable f) hf hf).1
    have he : E z ≤ (1-t)*E r+t*E ν := by
      have hh := integral_mono_ae (hint z hzb)
        (((hint r hr).const_mul (1-t)).add ((hint ν hν).const_mul t)) (by
          filter_upwards [hzeq, hr, hν] with x hx hux hvx
          rw [hx]
          simpa only [smul_eq_mul, Pi.add_apply] using Real.convexOn_mul_log.2 hux.1 hvx.1
            (sub_nonneg.mpr ht1) ht.le (show (1-t)+t=1 by ring))
      change (∫ x, z x * Real.log (z x) ∂μ) ≤
        ∫ x, (1-t)*(r x*Real.log (r x)) + t*(ν x*Real.log (ν x)) ∂μ at hh
      rw [integral_add ((hint r hr).const_mul _) ((hint ν hν).const_mul _),
        integral_const_mul, integral_const_mul] at hh
      exact hh
    have hm := hmin z hzb hzm
    have hid : inner ℝ z a = (1-t)*inner ℝ r a+t*inner ℝ ν a := by
      simp only [z, inner_add_left, inner_smul_left, RCLike.conj_to_real]
    have hquad : inner ℝ z (T z) = inner ℝ r (T r) +
        2*t*(inner ℝ ν (T r)-inner ℝ r (T r)) +
        t^2 * inner ℝ (ν-r) (T (ν-r)) := by
      have hc : inner ℝ r (T ν) = inner ℝ ν (T r) :=
        (hself r ν).trans (real_inner_comm _ _)
      simp only [z, map_add, map_smul, map_sub, inner_add_left, inner_add_right,
        inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right, RCLike.conj_to_real]
      rw [hc]
      ring
    have hb (f : Lp ℝ 2 μ) : inner ℝ f b = inner ℝ f a - β*inner ℝ f (T r) := by
      simp only [b, inner_sub_right, inner_smul_right]
    have htd : t*D ≤ Q*t^2 := by
      change E r - inner ℝ r a + β/2 * inner ℝ r (T r) ≤
        E z - inner ℝ z a + β/2 * inner ℝ z (T z) at hm
      rw [hid, hquad] at hm
      dsimp only [D, J, Q]
      rw [hb r, hb ν]
      nlinarith
    have htd' : t*D ≤ t*(Q*t) := by nlinarith [htd]
    exact (mul_le_mul_iff_right₀ ht).mp (by simpa only [mul_comm] using htd')
  have hDu : D ≤ 0 := by
    by_contra hn
    have hDp : 0 < D := lt_of_not_ge hn
    let t : ℝ := D/(2*(|Q|+D+1))
    have hden : 0 < 2*(|Q|+D+1) := by positivity
    have htp : 0 < t := div_pos hDp hden
    have ht1 : t ≤ 1 := (div_le_one hden).mpr (by linarith [abs_nonneg Q])
    have heq : t*(2*(|Q|+D+1)) = D := by dsimp [t]; field_simp
    have hbt := hbound t htp ht1
    have hqt : Q*t ≤ |Q| * t := mul_le_mul_of_nonneg_right (le_abs_self Q) htp.le
    nlinarith [mul_nonneg hDp.le htp.le, mul_nonneg (abs_nonneg Q) htp.le]
  have hD : D = 0 := le_antisymm hDu hDl
  let z : Lp ℝ 2 μ := (1/2 : ℝ) • (r+ν)
  have hz : ∀ᵐ x ∂μ, z x = (r x+ν x)/2 := by
    filter_upwards [Lp.coeFn_smul (1/2 : ℝ) (r+ν), Lp.coeFn_add r ν] with x hx hy
    change ((1/2 : ℝ) • (r+ν)) x = _
    rw [hx]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hy]
    simp only [Pi.add_apply]
    ring
  have hzb : ∀ᵐ x ∂μ, z x ∈ Set.Icc 0 M := by
    filter_upwards [hz, hr, hν] with x hx hu hv
    rw [hx]
    constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]
  have hzm : (∫ x, z x ∂μ) = 1 := by
    rw [integral_congr_ae hz, integral_div,
      integral_add ((Lp.memLp r).integrable (by norm_num)) ((Lp.memLp ν).integrable (by norm_num)), hrm, hνm]
    norm_num
  have hgap := (BoundedDensityEntropyMidpoint μ r ν M hM
    (Lp.aestronglyMeasurable r) (Lp.aestronglyMeasurable ν) hr hν).2.2.2
  have hsq : (∫ x, (r x-ν x)^2 ∂μ) = ‖r-ν‖^2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub r ν] with x hx
    change (r x-ν x)^2 = (r-ν) x * (r-ν) x
    rw [hx]
    simp [sq]
  have hent : E z = ∫ x, ((r x+ν x)/2)*Real.log ((r x+ν x)/2) ∂μ :=
    integral_congr_ae (hz.mono fun _ hx => by dsimp [E]; rw [hx])
  have hmid : inner ℝ z b = (inner ℝ r b+inner ℝ ν b)/2 := by
    simp only [z, inner_smul_left, inner_add_left, RCLike.conj_to_real]
    ring
  rw [hsq, ← hent] at hgap
  have hJ : J ν ≤ J z := hlinear z hzb hzm
  have hJeq : J r = J ν := sub_eq_zero.mp hD
  have hnorm : ‖r-ν‖^2 ≤ 0 := by
    dsimp only [J] at hJ hJeq
    rw [hmid] at hJ
    have hden : 0 < 8*M := by positivity
    have hh : ‖r-ν‖^2/(8*M) ≤ 0 := by dsimp only [E] at *; linarith
    simpa only [zero_mul] using (div_le_iff₀ hden).mp hh
  have hn : ‖r-ν‖ = 0 := by nlinarith [norm_nonneg (r-ν)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)
