module

public import Tablet.TorusIntegrationByParts
public import Tablet.TiltNormalization
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section
open scoped ContDiff
-- [TABLET NODE: TorusGroundState]
theorem TorusGroundState (d : ℕ) (V f : UnitAddTorus (Fin d) → ℝ)
    (hV : TorusSmooth V) (hf : TorusSmooth f) :
    let Z := ∫ x, Real.exp (-V x) ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d)))
    let ψ := fun x => f x * Real.exp (-V x / 2) / Real.sqrt Z
    0 < Z ∧
    (∫ x, ‖TorusGradient f x‖ ^ 2
      ∂NormalizedTilt (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d))) (fun x => Real.exp (-V x))) =
      ∫ x, ‖TorusGradient ψ x‖ ^ 2 +
        (1 / 4 : ℝ) * ‖TorusGradient V x‖ ^ 2 * ψ x ^ 2 -
        (1 / 2 : ℝ) * TorusLaplacian V x * ψ x ^ 2 ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d))) := by
-- BODY
  classical
  have quotient (d : ℕ) : IsOpenQuotientMap (TorusLift d) := by
    have hc : IsOpenQuotientMap ((↑) : ℝ → AddCircle (1 : ℝ)) :=
      QuotientAddGroup.isOpenQuotientMap_mk
    have hp : IsOpenQuotientMap
        (Pi.map (fun _ : Fin d => ((↑) : ℝ → AddCircle (1 : ℝ)))) :=
      IsOpenQuotientMap.piMap (fun _ => hc)
    exact hp.comp (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isOpenQuotientMap
  
  have continuous {d : ℕ} {f : UnitAddTorus (Fin d) → ℝ}
      (hf : TorusSmooth f) : Continuous f := by
    apply (quotient d).continuous_comp_iff.mp
    exact hf.continuous
  
  have lift_translation_eq {d : ℕ} (y z : EuclideanSpace ℝ (Fin d))
      (h : TorusLift d y = TorusLift d z) (x : EuclideanSpace ℝ (Fin d)) :
      TorusLift d (x + (z-y)) = TorusLift d x := by
    funext j
    have hj := congrFun h j
    change (y j : AddCircle (1 : ℝ)) = (z j : AddCircle (1 : ℝ)) at hj
    simp only [TorusLift, PiLp.add_apply, PiLp.sub_apply]
    rw [AddCircle.coe_add, AddCircle.coe_sub, ← hj, sub_self, add_zero]
  
  have lift_fderiv_eq {d : ℕ} (f : UnitAddTorus (Fin d) → ℝ)
      (y z : EuclideanSpace ℝ (Fin d)) (h : TorusLift d y = TorusLift d z) :
      fderiv ℝ (fun x => f (TorusLift d x)) y =
        fderiv ℝ (fun x => f (TorusLift d x)) z := by
    let q := fun x => f (TorusLift d x)
    have hfun : (fun x => q (x+(z-y))) = q := by
      funext x
      exact congrArg f (lift_translation_eq y z h x)
    have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := q) (x := y) (z-y)
    rw [hfun] at hd
    simpa using hd
  
  have gradient_on_lift {d : ℕ} (f : UnitAddTorus (Fin d) → ℝ)
      (y : EuclideanSpace ℝ (Fin d)) (j : Fin d) :
      TorusGradient f (TorusLift d y) j =
        fderiv ℝ (fun x => f (TorusLift d x)) y (EuclideanSpace.single j 1) := by
    let z : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2
      (fun j => (AddCircle.equivIco (1 : ℝ) 0 (TorusLift d y j) : ℝ))
    have hz : TorusLift d z = TorusLift d y := by
      funext j
      simp [TorusLift, z]
    change fderiv ℝ (fun x => f (TorusLift d x)) z (EuclideanSpace.single j 1) = _
    rw [lift_fderiv_eq f z y hz]
  
  have gradient_smooth {d : ℕ} {f : UnitAddTorus (Fin d) → ℝ}
      (hf : TorusSmooth f) (j : Fin d) : TorusSmooth (fun x => TorusGradient f x j) := by
    change ContDiff ℝ ∞ (fun y => TorusGradient f (TorusLift d y) j)
    simp_rw [gradient_on_lift]
    exact (hf.fderiv_right (by simp)).clm_apply contDiff_const
  
  have gradient_mul {d : ℕ} {f h : UnitAddTorus (Fin d) → ℝ}
      (hf : TorusSmooth f) (hh : TorusSmooth h) (x : UnitAddTorus (Fin d))
      (j : Fin d) : TorusGradient (fun x => f x * h x) x j =
        TorusGradient f x j * h x + f x * TorusGradient h x j := by
    obtain ⟨y, rfl⟩ := (quotient d).surjective x
    simp_rw [gradient_on_lift]
    have hd := (hf.differentiable (by simp) y).hasFDerivAt.mul
      (hh.differentiable (by simp) y).hasFDerivAt
    change HasFDerivAt (fun x => f (TorusLift d x) * h (TorusLift d x)) _ y at hd
    rw [hd.fderiv]
    simp
    ring
  
  have laplacian_gradient_sum {d : ℕ} (f : UnitAddTorus (Fin d) → ℝ)
      (x : UnitAddTorus (Fin d)) :
      TorusLaplacian f x = ∑ j, TorusGradient (fun x => TorusGradient f x j) x j := by
    let y : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2
      (fun j => (AddCircle.equivIco (1 : ℝ) 0 (x j) : ℝ))
    have hy : TorusLift d y = x := by
      ext j
      simp [TorusLift, y]
    calc
      TorusLaplacian f x = ∑ j, fderiv ℝ
          (fun z => fderiv ℝ (fun w => f (TorusLift d w)) z
            (EuclideanSpace.single j 1)) y (EuclideanSpace.single j 1) := rfl
      _ = ∑ j, TorusGradient (fun x => TorusGradient f x j) (TorusLift d y) j := by
        simp_rw [gradient_on_lift]
      _ = _ := by rw [hy]
  
  let m := (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d)))
  let Z := ∫ x, Real.exp (-V x) ∂m
  let c := Real.sqrt Z
  let ψ := fun x => f x * Real.exp (-V x / 2) / c
  have hw : Continuous (fun x => Real.exp (-V x)) := Real.continuous_exp.comp (continuous hV).neg
  have hwi : MeasureTheory.Integrable (fun x => Real.exp (-V x)) m :=
    hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hZ : 0 < Z := MeasureTheory.integral_exp_pos hwi
  have hc : 0 < c := Real.sqrt_pos.2 hZ
  have hc2 : c^2 = Z := Real.sq_sqrt hZ.le
  have hψ : TorusSmooth ψ := by
    change ContDiff ℝ ∞ (fun y => f (TorusLift d y) *
      Real.exp (-V (TorusLift d y) / 2) / c)
    exact (hf.mul (hV.neg.div_const 2).exp).div_const c
  have gradient_psi (x : UnitAddTorus (Fin d)) (j : Fin d) :
      TorusGradient ψ x j =
        (TorusGradient f x j - f x * TorusGradient V x j / 2) *
          Real.exp (-V x / 2) / c := by
    obtain ⟨y, rfl⟩ := (quotient d).surjective x
    simp_rw [gradient_on_lift]
    have hdf := (hf.differentiable (by simp) y).hasFDerivAt
    have hdV := (hV.differentiable (by simp) y).hasFDerivAt
    have hd := (hdf.mul (hdV.neg.mul_const (1 / 2 : ℝ)).exp).mul_const (1 / c)
    simp only [div_eq_mul_inv, one_mul, Pi.mul_apply, Pi.neg_apply] at hd
    have heq : (fun z => f (TorusLift d z) * Real.exp (-V (TorusLift d z) * 2⁻¹) * c⁻¹) =
        (fun z => ψ (TorusLift d z)) := by
      funext z
      simp only [ψ, div_eq_mul_inv]
    rw [heq] at hd
    rw [hd.fderiv]
    simp
    ring
  have cont_grad {g : UnitAddTorus (Fin d) → ℝ} (hg : TorusSmooth g) :
      Continuous (TorusGradient g) := by
    exact (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).continuous_symm.comp
      (continuous_pi (fun j => continuous (gradient_smooth hg j)))
  have cont_lap : Continuous (TorusLaplacian V) := by
    change Continuous (fun x => TorusLaplacian V x)
    simp_rw [laplacian_gradient_sum]
    exact continuous_finsetSum _ (fun j _ =>
      continuous (gradient_smooth (gradient_smooth hV j) j))
  have ci {g : UnitAddTorus (Fin d) → ℝ} (hg : Continuous g) :
      MeasureTheory.Integrable g m :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have cf := continuous hf
  have cψ := continuous hψ
  have cgψ := cont_grad hψ
  have cgV := cont_grad hV
  have cgf := cont_grad hf
  let A := fun x => ‖TorusGradient ψ x‖^2
  let B := fun x => (1 / 4 : ℝ) * ‖TorusGradient V x‖^2 * ψ x^2
  let D := fun x => ∑ j : Fin d, ψ x * TorusGradient ψ x j * TorusGradient V x j
  let E := fun x => ‖TorusGradient f x‖^2 * Real.exp (-V x) / Z
  have hAi : MeasureTheory.Integrable A m := ci (cgψ.norm.pow 2)
  have hBi : MeasureTheory.Integrable B m :=
    ci ((continuous_const.mul (cgV.norm.pow 2)).mul (cψ.pow 2))
  have hDi : MeasureTheory.Integrable D m := ci <|
    continuous_finsetSum _ (fun j _ =>
      (cψ.mul (continuous (gradient_smooth hψ j))).mul
        (continuous (gradient_smooth hV j)))
  have hLi : MeasureTheory.Integrable (fun x => TorusLaplacian V x * ψ x^2) m :=
    ci (cont_lap.mul (cψ.pow 2))
  have pointwise (x) : A x + B x + D x = E x := by
    have hexp : Real.exp (-V x / 2)^2 = Real.exp (-V x) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    simp only [A, B, D, E, EuclideanSpace.real_norm_sq_eq]
    simp only [Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [gradient_psi]
    dsimp [ψ]
    rw [← hc2, ← hexp]
    field_simp [ne_of_gt hc]
    <;> ring
  have hip := TorusIntegrationByParts d (fun x => ψ x^2) V (hψ.pow 2) hV
  have hd2 (x) (j) : TorusGradient (fun x => ψ x^2) x j =
      2 * ψ x * TorusGradient ψ x j := by
    simp only [pow_two]
    rw [gradient_mul hψ hψ]
    ring
  simp_rw [hd2] at hip
  have hs (x) : (∑ j : Fin d, 2 * ψ x * TorusGradient ψ x j * TorusGradient V x j) =
      2 * D x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hs] at hip
  rw [MeasureTheory.integral_const_mul] at hip
  have hip' : (∫ x, TorusLaplacian V x * ψ x^2 ∂m) = -(2 * ∫ x, D x ∂m) := by
    simpa only [mul_comm] using hip
  have htilt := (TiltNormalization m (fun x => Real.exp (-V x)) hw.measurable
    (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)) hwi hZ).2
      (fun x => ‖TorusGradient f x‖^2) (cgf.norm.pow 2).measurable
      (ci ((cgf.norm.pow 2).mul hw))
  refine ⟨hZ, ?_⟩
  change (∫ x, ‖TorusGradient f x‖^2
    ∂NormalizedTilt m (fun x => Real.exp (-V x))) = ∫ x, A x + B x -
      (1 / 2 : ℝ) * TorusLaplacian V x * ψ x^2 ∂m
  rw [htilt.2]
  have he : (∫ x, E x ∂m) = (∫ x, ‖TorusGradient f x‖^2 * Real.exp (-V x) ∂m) / Z :=
    MeasureTheory.integral_div Z _
  rw [← he]
  simp_rw [← pointwise]
  rw [MeasureTheory.integral_add (show MeasureTheory.Integrable (fun x => A x + B x) m from hAi.add hBi) hDi,
    MeasureTheory.integral_add hAi hBi,
    MeasureTheory.integral_sub (show MeasureTheory.Integrable (fun x => A x + B x) m from hAi.add hBi)]
  · rw [MeasureTheory.integral_add hAi hBi]
    have ht : (fun x => (1 / 2 : ℝ) * TorusLaplacian V x * ψ x^2) =
        fun x => (1 / 2 : ℝ) * (TorusLaplacian V x * ψ x^2) := by
      funext x
      ring
    rw [ht, MeasureTheory.integral_const_mul, hip']
    ring
  · simpa only [mul_assoc] using hLi.const_mul (1 / 2 : ℝ)
