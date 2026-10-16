import Tablet.Preamble
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
open MeasureTheory UnitAddTorus
open scoped Topology

-- [TABLET NODE: ProbabilityConvolutionJensenInputs]
theorem ProbabilityConvolutionJensenInputs (d : ℕ)
    (g q r : UnitAddTorus (Fin d) → ℝ)
    (hg : Measurable g) (hgi : Integrable g volume) (hq : Measurable q) (hr : Measurable r)
    (qhi C c : ℝ) (hqb : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), 0 ≤ q x ∧ q x ≤ qhi)
    (hqhi : 0 ≤ qhi) (hgb : ∀ x, ‖g x‖ ≤ C) (hgl : ∀ x, -c ≤ g x)
    (hri : Integrable r volume) (hrn : ∀ᵐ x ∂volume, 0 ≤ r x) (hrm : (∫ x, r x) = 1) :
    let h := fun x => ∫ y, g (x-y)*r y
    Measurable h ∧
    (∀ x, Integrable (fun y => g (x-y)*r y) volume ∧ -c ≤ h x ∧ |h x| ≤ C) ∧
    Integrable (fun x => q x*h x) volume ∧
    (∫ x, q x*h x) ≤ qhi*(∫ x, |g x|) := by
-- BODY
  classical
  letI : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
    ⟨by rw [AddCircle.volume_eq_smul_haarAddCircle]; simp⟩
  let h := fun x => ∫ y, g (x-y)*r y
  have hqn : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), ‖q x‖ ≤ qhi :=
    hqb.mono fun _ hx => by simpa [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2
  have hqi : Integrable q volume := Integrable.of_bound hq.aestronglyMeasurable qhi hqn
  have hji (x : UnitAddTorus (Fin d)) : Integrable (fun y => g (x-y)*r y) volume := by
    simpa [mul_comm, Function.comp_def] using hri.mul_bdd
      (hg.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => hgb (x-y))
  have hm : Measurable h :=
    ((hg.comp (measurable_fst.sub measurable_snd)).mul (hr.comp measurable_snd)).stronglyMeasurable.integral_prod_right.measurable
  have hb (x : UnitAddTorus (Fin d)) : |h x| ≤ C := by
    calc
      |h x| ≤ ∫ y, ‖g (x-y)*r y‖ := by simpa only [h, Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y => g (x-y)*r y)
      _ ≤ ∫ y, C*r y := by
        apply integral_mono_ae (hji x).norm (hri.const_mul C)
        filter_upwards [hrn] with y hy
        rw [norm_mul, Real.norm_eq_abs (r y), abs_of_nonneg hy]
        exact mul_le_mul_of_nonneg_right (hgb (x-y)) hy
      _ = C := by rw [integral_const_mul, hrm, mul_one]
  have hl (x : UnitAddTorus (Fin d)) : -c ≤ h x := by
    have hh := integral_mono_ae (hri.const_mul (-c)) (hji x) (hrn.mono fun y hy =>
      mul_le_mul_of_nonneg_right (hgl (x-y)) hy)
    rw [integral_const_mul, hrm, mul_one] at hh
    exact hh
  have hqh : Integrable (fun x => q x*h x) volume :=
    hqi.mul_bdd hm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hb x)
  have hpair : Integrable (fun p : UnitAddTorus (Fin d) × UnitAddTorus (Fin d) =>
      q p.1*g (p.1-p.2)*r p.2) (volume.prod volume) := by
    have hi := (hqi.mul_prod hri).mul_bdd
      (hg.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => hgb (p.1-p.2))
    convert hi using 1
    funext p
    simp only [Function.comp_apply, Pi.sub_apply]
    ring
  let k := fun y => ∫ x, g (x-y)*q x
  have hkm : Measurable k :=
    ((hg.comp (measurable_snd.sub measurable_fst)).mul (hq.comp measurable_snd)).stronglyMeasurable.integral_prod_right.measurable
  have hki (y : UnitAddTorus (Fin d)) : Integrable (fun x => g (x-y)*q x) volume :=
    (hgi.comp_sub_right y).mul_bdd hq.aestronglyMeasurable hqn
  have hk (y : UnitAddTorus (Fin d)) : |k y| ≤ qhi*(∫ x, |g x|) := by
    calc
      |k y| ≤ ∫ x, ‖g (x-y)*q x‖ := by simpa only [k, Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => g (x-y)*q x)
      _ ≤ ∫ x, qhi*|g (x-y)| := by
        apply integral_mono_ae (hki y).norm ((hgi.abs.comp_sub_right y).const_mul qhi)
        filter_upwards [hqn] with x hx
        rw [norm_mul, Real.norm_eq_abs (g (x-y))]
        exact (mul_le_mul_of_nonneg_left hx (abs_nonneg _)).trans_eq (mul_comm _ _)
      _ = _ := by rw [integral_const_mul, integral_sub_right_eq_self (fun x => |g x|) y]
  have hrk : Integrable (fun x => r x*k x) volume :=
    hri.mul_bdd hkm.aestronglyMeasurable (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hk y)
  have hex : (∫ x, q x*h x) = ∫ y, r y*k y := by
    calc
      _ = ∫ x, ∫ y, q x*g (x-y)*r y := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          dsimp [h]
          rw [← integral_const_mul]
          congr 1
          funext y
          ring
      _ = ∫ y, ∫ x, q x*g (x-y)*r y := integral_integral_swap hpair
      _ = _ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by
          dsimp [k]
          rw [← integral_const_mul]
          congr 1
          funext x
          ring
  refine ⟨hm, fun x => ⟨hji x, hl x, hb x⟩, hqh, ?_⟩
  rw [hex]
  calc
    _ ≤ ∫ y, (qhi*(∫ x, |g x|))*r y := by
      apply integral_mono_ae hrk (hri.const_mul _)
      filter_upwards [hrn] with y hy
      exact (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hk y)) hy).trans_eq (mul_comm _ _)
    _ = _ := by rw [integral_const_mul, hrm, mul_one]
