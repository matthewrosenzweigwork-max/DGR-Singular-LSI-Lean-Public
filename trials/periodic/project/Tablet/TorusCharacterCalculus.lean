import Tablet.TorusFourierLaplacian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
open MeasureTheory
open scoped ContDiff
-- [TABLET NODE: TorusCharacterCalculus]
theorem TorusCharacterCalculus (d : ℕ) (k : Fin d → ℤ) :
    TorusSmooth (fun x => (UnitAddTorus.mFourier k x).re) ∧
    TorusSmooth (fun x => (UnitAddTorus.mFourier k x).im) ∧
    (∀ x, TorusLaplacian (fun x => (UnitAddTorus.mFourier k x).re) x =
      -(4*Real.pi^2*∑j,(k j:ℝ)^2)*(UnitAddTorus.mFourier k x).re) ∧
    (∀ x, TorusLaplacian (fun x => (UnitAddTorus.mFourier k x).im) x =
      -(4*Real.pi^2*∑j,(k j:ℝ)^2)*(UnitAddTorus.mFourier k x).im) := by
-- BODY
  classical
  have character_on_lift (d : ℕ) (k : Fin d → ℤ) (y : EuclideanSpace ℝ (Fin d)) :
      UnitAddTorus.mFourier k (TorusLift d y) = Complex.exp
        ((2*Real.pi*∑j,(k j:ℝ)*y j : ℝ)*Complex.I) := by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, TorusLift,
      fourier_coe_apply, div_one]
    rw [← Complex.exp_sum]
    congr 1
    simp only [Complex.ofReal_mul,Complex.ofReal_sum,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    push_cast
    ring

  have torus_character_smooth (d : ℕ) (k : Fin d → ℤ) :
      TorusSmooth (fun x => (UnitAddTorus.mFourier k x).re) ∧
      TorusSmooth (fun x => (UnitAddTorus.mFourier k x).im) := by
    let A : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
      ∑ j, (2*Real.pi*(k j:ℝ)) • EuclideanSpace.proj j
    have hA (y : EuclideanSpace ℝ (Fin d)) : A y = 2*Real.pi*∑j,(k j:ℝ)*y j := by
      simp only [A,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
        EuclideanSpace.coe_proj,smul_eq_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    constructor
    · change ContDiff ℝ ∞ (fun y => (UnitAddTorus.mFourier k (TorusLift d y)).re)
      simp_rw [character_on_lift, Complex.exp_re]
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.I_re,mul_zero,
        Complex.ofReal_im,Complex.I_im,zero_mul,sub_zero,Real.exp_zero,one_mul,
        Complex.mul_im,mul_one,zero_add,add_zero]
      simp_rw [←hA]
      exact A.contDiff.cos
    · change ContDiff ℝ ∞ (fun y => (UnitAddTorus.mFourier k (TorusLift d y)).im)
      simp_rw [character_on_lift,Complex.exp_im]
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.I_re,mul_zero,
        Complex.ofReal_im,Complex.I_im,zero_mul,sub_zero,Real.exp_zero,one_mul,
        Complex.mul_im,mul_one,zero_add,add_zero]
      simp_rw [←hA]
      exact A.contDiff.sin

  have linear_phase_laplacian_cos (d : ℕ)
      (A : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (y : EuclideanSpace ℝ (Fin d)) :
      (∑ j, fderiv ℝ (fun z : EuclideanSpace ℝ (Fin d) =>
        fderiv ℝ (fun w => Real.cos (A w)) z (EuclideanSpace.single j 1))
        y (EuclideanSpace.single j 1)) =
          -Real.cos (A y) * ∑ j, (A (EuclideanSpace.single j 1))^2 := by
    have hfirst (z : EuclideanSpace ℝ (Fin d)) :
        fderiv ℝ (fun w => Real.cos (A w)) z = -Real.sin (A z) • A :=
      (A.hasFDerivAt.cos).fderiv
    simp_rw [hfirst]
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.neg_apply,smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hd := (((A.hasFDerivAt (x := y)).sin.neg).mul_const
      (A (EuclideanSpace.single j 1))).fderiv
    simp only [Pi.neg_apply] at hd
    rw [hd]
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.neg_apply,smul_eq_mul]
    ring

  have linear_phase_laplacian_sin (d : ℕ)
      (A : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (y : EuclideanSpace ℝ (Fin d)) :
      (∑ j, fderiv ℝ (fun z : EuclideanSpace ℝ (Fin d) =>
        fderiv ℝ (fun w => Real.sin (A w)) z (EuclideanSpace.single j 1))
        y (EuclideanSpace.single j 1)) =
          -Real.sin (A y) * ∑ j, (A (EuclideanSpace.single j 1))^2 := by
    have hfirst (z : EuclideanSpace ℝ (Fin d)) :
        fderiv ℝ (fun w => Real.sin (A w)) z = Real.cos (A z) • A :=
      (A.hasFDerivAt.sin).fderiv
    simp_rw [hfirst]
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.neg_apply,smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [((A.hasFDerivAt.cos).mul_const (A (EuclideanSpace.single j 1))).fderiv]
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.neg_apply,smul_eq_mul]
    ring

  have torus_character_laplacian (d : ℕ) (k : Fin d → ℤ) :
      (∀ x, TorusLaplacian (fun x => (UnitAddTorus.mFourier k x).re) x =
        -(4*Real.pi^2*∑j,(k j:ℝ)^2)*(UnitAddTorus.mFourier k x).re) ∧
      (∀ x, TorusLaplacian (fun x => (UnitAddTorus.mFourier k x).im) x =
        -(4*Real.pi^2*∑j,(k j:ℝ)^2)*(UnitAddTorus.mFourier k x).im) := by
    classical
    let A : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
      ∑ j, (2*Real.pi*(k j:ℝ)) • EuclideanSpace.proj j
    have hA (y : EuclideanSpace ℝ (Fin d)) : A y = 2*Real.pi*∑j,(k j:ℝ)*y j := by
      simp only [A,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
        EuclideanSpace.coe_proj,smul_eq_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have hc (y : EuclideanSpace ℝ (Fin d)) :
        (UnitAddTorus.mFourier k (TorusLift d y)).re = Real.cos (A y) := by
      rw [character_on_lift]
      simp [Complex.exp_re,hA]
    have hs (y : EuclideanSpace ℝ (Fin d)) :
        (UnitAddTorus.mFourier k (TorusLift d y)).im = Real.sin (A y) := by
      rw [character_on_lift]
      simp [Complex.exp_im,hA]
    have hAsq : (∑ j, (A (EuclideanSpace.single j 1))^2) =
        4*Real.pi^2*∑j,(k j:ℝ)^2 := by
      simp_rw [hA]
      simp only [EuclideanSpace.single_apply,ite_mul,mul_ite,mul_zero,mul_one,
        Finset.sum_ite_eq',Finset.mem_univ,if_true]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    constructor
    · intro x
      let y : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2
        (fun j => (AddCircle.equivIco (1 : ℝ) 0 (x j) : ℝ))
      have hy : TorusLift d y = x := by
        ext j
        simp [TorusLift,y]
      unfold TorusLaplacian
      change (∑ j, fderiv ℝ (fun z =>
        fderiv ℝ (fun w => (UnitAddTorus.mFourier k (TorusLift d w)).re) z
        (EuclideanSpace.single j 1)) y (EuclideanSpace.single j 1)) = _
      simp_rw [hc]
      rw [linear_phase_laplacian_cos,hAsq]
      rw [←hc,hy]
      ring
    · intro x
      let y : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2
        (fun j => (AddCircle.equivIco (1 : ℝ) 0 (x j) : ℝ))
      have hy : TorusLift d y = x := by
        ext j
        simp [TorusLift,y]
      unfold TorusLaplacian
      change (∑ j, fderiv ℝ (fun z =>
        fderiv ℝ (fun w => (UnitAddTorus.mFourier k (TorusLift d w)).im) z
        (EuclideanSpace.single j 1)) y (EuclideanSpace.single j 1)) = _
      simp_rw [hs]
      rw [linear_phase_laplacian_sin,hAsq]
      rw [←hs,hy]
      ring
  exact ⟨(torus_character_smooth d k).1, (torus_character_smooth d k).2,
    (torus_character_laplacian d k).1, (torus_character_laplacian d k).2⟩
