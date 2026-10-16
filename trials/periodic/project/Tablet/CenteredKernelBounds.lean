module

public import Tablet.CenteredKernel
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section
open MeasureTheory
-- [TABLET NODE: CenteredKernelBounds]
theorem CenteredKernelBounds (d : ℕ) (g r : UnitAddTorus (Fin d) → ℝ)
    (hg : Measurable g) (hgi : Integrable g volume)
    (hr : Measurable r) (M c : ℝ) (hM : 1 ≤ M) (hc : 0 ≤ c)
    (hrb : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), 0 ≤ r x ∧ r x ≤ M)
    (hrmass : ∫ x, r x ∂volume = 1) (hgl : ∀ x, -c ≤ g x) :
    let H := M * ∫ x, |g x| ∂volume
    Measurable (BackgroundPotential g r) ∧
    (∀ x, Integrable (fun y => g (x-y) * r y) volume ∧
      |BackgroundPotential g r x| ≤ H) ∧
    Integrable (fun x => BackgroundPotential g r x * r x) volume ∧
    |BackgroundPairMean g r| ≤ H ∧
    Measurable (fun p : UnitAddTorus (Fin d) × UnitAddTorus (Fin d) =>
      CenteredKernel g r p.1 p.2) ∧
    (∀ x, Integrable (fun y => CenteredKernel g r x y * r y) volume ∧
      (∫ y, CenteredKernel g r x y * r y ∂volume) = 0) ∧
    (∀ x y, -c - 3 * H ≤ CenteredKernel g r x y) := by
-- BODY
  have hpot_eq : BackgroundPotential g r = fun x => ∫ y, g (x-y)*r y := by
    funext x
    unfold BackgroundPotential convolution
    change (∫ y, r y*g (x-y)) = ∫ y, g (x-y)*r y
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => mul_comm _ _
  haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
    infer_instance
  haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := by
    infer_instance
  let H := M * ∫ x, |g x| ∂volume
  have hH : 0 ≤ H := mul_nonneg (zero_le_one.trans hM) (integral_nonneg (fun _ => abs_nonneg _))
  have hrnorm : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), ‖r x‖ ≤ M := by
    filter_upwards [hrb] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2
  have hri : Integrable r volume := Integrable.of_bound hr.aestronglyMeasurable M hrnorm
  have hji (x : UnitAddTorus (Fin d)) : Integrable (fun y => g (x-y) * r y) volume :=
    (hgi.comp_sub_left x).mul_bdd hr.aestronglyMeasurable hrnorm
  have hjm : Measurable (fun p : UnitAddTorus (Fin d) × UnitAddTorus (Fin d) =>
      g (p.1-p.2) * r p.2) :=
    (hg.comp (measurable_fst.sub measurable_snd)).mul (hr.comp measurable_snd)
  have hm : Measurable (BackgroundPotential g r) := by
    rw [hpot_eq]
    exact hjm.stronglyMeasurable.integral_prod_right.measurable
  have hb (x : UnitAddTorus (Fin d)) : |BackgroundPotential g r x| ≤ H := by
    calc
      _ ≤ ∫ y, ‖g (x-y) * r y‖ ∂volume := by
        simpa only [hpot_eq, Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun y => g (x-y)*r y)
      _ ≤ ∫ y, M * |g (x-y)| ∂volume := by
        apply integral_mono_ae (hji x).norm ((hgi.abs.comp_sub_left x).const_mul M)
        filter_upwards [hrb] with y hy
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hy.1]
        nlinarith [abs_nonneg (g (x-y))]
      _ = H := by
        rw [integral_const_mul, integral_sub_left_eq_self
          (fun y : UnitAddTorus (Fin d) => |g y|) volume x]
  have hip : Integrable (BackgroundPotential g r) volume :=
    Integrable.of_bound hm.aestronglyMeasurable H (Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using hb x)
  have hir : Integrable (fun x => BackgroundPotential g r x * r x) volume :=
    hip.mul_bdd hr.aestronglyMeasurable hrnorm
  have hbJ : |BackgroundPairMean g r| ≤ H := by
    calc
      _ ≤ ∫ x, ‖BackgroundPotential g r x * r x‖ ∂volume := by
        simpa only [BackgroundPairMean, Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun x => BackgroundPotential g r x*r x)
      _ ≤ ∫ x, H*r x ∂volume := by
        apply integral_mono_ae hir.norm (hri.const_mul H)
        filter_upwards [hrb] with x hx
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx.1]
        exact mul_le_mul_of_nonneg_right (hb x) hx.1
      _ = H := by rw [integral_const_mul,hrmass,mul_one]
  have hcm : Measurable (fun p : UnitAddTorus (Fin d) × UnitAddTorus (Fin d) =>
      CenteredKernel g r p.1 p.2) := by
    exact (((hg.comp (measurable_fst.sub measurable_snd)).sub
      (hm.comp measurable_fst)).sub (hm.comp measurable_snd)).add measurable_const
  have hcf (x : UnitAddTorus (Fin d)) :
      Integrable (fun y => CenteredKernel g r x y * r y) volume ∧
        (∫ y, CenteredKernel g r x y * r y ∂volume) = 0 := by
    have heq (y : UnitAddTorus (Fin d)) : CenteredKernel g r x y * r y =
      g (x-y)*r y - BackgroundPotential g r x*r y -
        BackgroundPotential g r y*r y + BackgroundPairMean g r*r y := by
      unfold CenteredKernel
      ring
    have hB : Integrable (fun y => g (x-y)*r y - BackgroundPotential g r x*r y) volume :=
      (hji x).sub (hri.const_mul (BackgroundPotential g r x))
    have hA := hB.sub hir
    change Integrable (fun y => g (x-y)*r y - BackgroundPotential g r x*r y -
      BackgroundPotential g r y*r y) volume at hA
    constructor
    · simp_rw [heq]
      exact hA.add (hri.const_mul (BackgroundPairMean g r))
    · simp_rw [heq]
      rw [integral_add hA (hri.const_mul _),
        integral_sub hB hir,
        integral_sub (hji x) (hri.const_mul (BackgroundPotential g r x)), integral_const_mul,
        integral_const_mul,hrmass]
      rw [← congrFun hpot_eq x]
      change BackgroundPotential g r x - BackgroundPotential g r x*1 -
        BackgroundPairMean g r + BackgroundPairMean g r*1 = 0
      ring
  refine ⟨hm, fun x => ⟨hji x,hb x⟩,hir,hbJ,hcm,hcf,?_⟩
  intro x y
  have hx := (abs_le.mp (hb x)).2
  have hy := (abs_le.mp (hb y)).2
  have hj := (abs_le.mp hbJ).1
  unfold CenteredKernel
  linarith [hgl (x-y)]
