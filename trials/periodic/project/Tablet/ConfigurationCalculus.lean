module

public import Tablet.ConfigurationFlatten
public import Tablet.SmoothCore
public import Tablet.PhysicalEnergy
public import Tablet.TorusGradient
public import Tablet.TorusSmooth
public import Tablet.Replacement
public import Tablet.TorusLift
public import Tablet.ConfigurationLift
public import Tablet.CoordinateGradient
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.WithLp

@[expose] public section
open MeasureTheory
open scoped ContDiff
-- [TABLET NODE: ConfigurationCalculus]
theorem ConfigurationCalculus (d N : ℕ) :
    Measurable (ConfigurationFlatten d N) ∧
    Measurable (ConfigurationFlatten d N).symm ∧
    MeasureTheory.Measure.map (ConfigurationFlatten d N)
      (MeasureTheory.volume : MeasureTheory.Measure (Configuration d N)) =
      (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin (N * d)))) ∧
    ∀ f : Configuration d N → ℝ, f ∈ SmoothCore d N →
      TorusSmooth (fun x => f ((ConfigurationFlatten d N).symm x)) ∧
      Measurable f ∧ (∃ C : ℝ, ∀ X, |f X| ≤ C) ∧
      Measurable (fun X => ‖CoordinateGradient f X‖^2) ∧
      (∃ C : ℝ, ∀ X, ‖CoordinateGradient f X‖^2 ≤ C) ∧
      (∀ X, ‖TorusGradient (fun x => f ((ConfigurationFlatten d N).symm x))
        (ConfigurationFlatten d N X)‖^2 = ‖CoordinateGradient f X‖^2) ∧
      (∀ (X : Configuration d N) (i : Fin N),
        TorusSmooth (fun z => f (Replacement X i z)) ∧
        ∀ z, ‖TorusGradient (fun y => f (Replacement X i y)) z‖^2 =
          ∑ j : Fin d, (CoordinateGradient f (Replacement X i z) (i, j))^2) ∧
      (∀ X, ‖CoordinateGradient f X‖^2 =
        ∑ i : Fin N, ∑ j : Fin d, (CoordinateGradient f X (i, j))^2) := by
-- BODY
  classical
  have flatten_measurable (d N : ℕ) : Measurable (ConfigurationFlatten d N) := by
    apply measurable_pi_lambda
    intro k
    exact (measurable_pi_apply (finProdFinEquiv.symm k).2).comp
      (measurable_pi_apply (finProdFinEquiv.symm k).1)

  have flatten_preserves_volume (d N : ℕ) :
      MeasurePreserving (ConfigurationFlatten d N)
        (volume : Measure (Configuration d N))
        (volume : Measure (UnitAddTorus (Fin (N*d)))) := by
    refine ⟨flatten_measurable d N, ?_⟩
    change (volume : Measure (Configuration d N)).map (ConfigurationFlatten d N) =
      Measure.pi (fun _ : Fin (N*d) => (volume : Measure (AddCircle (1 : ℝ))))
    symm
    apply Measure.pi_eq
    intro S hS
    rw [Measure.map_apply (flatten_measurable d N) (MeasurableSet.univ_pi hS)]
    have hpre : (ConfigurationFlatten d N) ⁻¹' Set.pi Set.univ S =
        Set.pi Set.univ (fun i : Fin N =>
          Set.pi Set.univ (fun j : Fin d => S (finProdFinEquiv (i,j)))) := by
      ext X
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const]
      constructor
      · intro h i j
        have he : (ConfigurationFlatten d N X) (finProdFinEquiv (i,j)) = X i j := by
          change X (finProdFinEquiv.symm (finProdFinEquiv (i,j))).1
            (finProdFinEquiv.symm (finProdFinEquiv (i,j))).2 = X i j
          rw [Equiv.symm_apply_apply]
        simpa only [he] using h (finProdFinEquiv (i,j))
      · intro h k
        have hh := h (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
        change X (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 ∈
          S (finProdFinEquiv (finProdFinEquiv.symm k)) at hh
        rw [Equiv.apply_symm_apply] at hh
        exact hh
    rw [hpre, volume_pi_pi]
    simp_rw [volume_pi_pi]
    let e : Fin N × Fin d ≃ Fin (N*d) := finProdFinEquiv
    calc
      (∏ i : Fin N, ∏ j : Fin d, (volume : Measure (AddCircle (1 : ℝ)))
          (S (finProdFinEquiv (i,j)))) =
        ∏ ij : Fin N × Fin d, (volume : Measure (AddCircle (1 : ℝ))) (S (e ij)) :=
          (Fintype.prod_prod_type (fun ij : Fin N × Fin d =>
            (volume : Measure (AddCircle (1 : ℝ))) (S (e ij)))).symm
      _ = _ := e.prod_comp (fun k => (volume : Measure (AddCircle (1 : ℝ))) (S k))

  let flatVector (d N : ℕ)
      (y : EuclideanSpace ℝ (Fin N × Fin d)) : EuclideanSpace ℝ (Fin (N*d)) :=
    WithLp.toLp 2 (fun k => y ((finProdFinEquiv.symm k).1,(finProdFinEquiv.symm k).2))

  have flatVector_norm_sq (d N : ℕ) (y : EuclideanSpace ℝ (Fin N × Fin d)) :
      ‖flatVector d N y‖^2 = ‖y‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    let e : Fin (N*d) ≃ Fin N × Fin d := finProdFinEquiv.symm
    exact e.sum_comp (fun ij => y ij ^ 2)

  have quotient_commutes (d N : ℕ) (y : EuclideanSpace ℝ (Fin N × Fin d)) :
      ConfigurationFlatten d N (ConfigurationLift d N y) = TorusLift (N*d) (flatVector d N y) := by
    rfl

  let flatLinearEquiv (d N : ℕ) :
      EuclideanSpace ℝ (Fin N × Fin d) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (N*d)) :=
    (WithLp.linearEquiv 2 ℝ (Fin N × Fin d → ℝ)).trans
      ((LinearEquiv.piCongrLeft ℝ (fun _ : Fin (N*d) => ℝ)
        (finProdFinEquiv)).trans
          (WithLp.linearEquiv 2 ℝ (Fin (N*d) → ℝ)).symm)

  let flatCLE (d N : ℕ) :
      EuclideanSpace ℝ (Fin N × Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin (N*d)) :=
    (flatLinearEquiv d N).toContinuousLinearEquiv

  have flatCLE_apply (d N : ℕ) (y : EuclideanSpace ℝ (Fin N × Fin d)) :
      flatCLE d N y = flatVector d N y := by
    ext k
    simp [flatCLE, flatLinearEquiv, flatVector, LinearEquiv.piCongrLeft]

  have quotient_inverse_commutes (d N : ℕ) (z : EuclideanSpace ℝ (Fin (N*d))) :
      ConfigurationLift d N ((flatCLE d N).symm z) =
        (ConfigurationFlatten d N).symm (TorusLift (N*d) z) := by
    apply (ConfigurationFlatten d N).injective
    rw [Equiv.apply_symm_apply, quotient_commutes]
    rw [← flatCLE_apply, ContinuousLinearEquiv.apply_symm_apply]

  have smooth_iff (d N : ℕ) (f : Configuration d N → ℝ) :
      f ∈ SmoothCore d N ↔
        TorusSmooth (fun x => f ((ConfigurationFlatten d N).symm x)) := by
    change ContDiff ℝ ∞ (fun y => f (ConfigurationLift d N y)) ↔
      ContDiff ℝ ∞ (fun z => f ((ConfigurationFlatten d N).symm (TorusLift (N*d) z)))
    constructor
    · intro hf
      have h := hf.comp (flatCLE d N).symm.contDiff
      simpa only [Function.comp_def, quotient_inverse_commutes] using h
    · intro hf
      have h := hf.comp (flatCLE d N).contDiff
      simpa only [Function.comp_def, flatCLE_apply, ← quotient_commutes,
        Equiv.symm_apply_apply] using h

  have flatCLE_symm_single (d N : ℕ) (k : Fin (N*d)) :
      (flatCLE d N).symm (EuclideanSpace.single k 1) =
        EuclideanSpace.single ((finProdFinEquiv.symm k).1,
          (finProdFinEquiv.symm k).2) 1 := by
    ext ij
    change (Pi.single k (1 : ℝ) : Fin (N*d) → ℝ) (finProdFinEquiv ij) =
      (Pi.single ((finProdFinEquiv.symm k).1,(finProdFinEquiv.symm k).2) (1 : ℝ) : Fin N × Fin d → ℝ) ij
    have he : finProdFinEquiv ij = k ↔
        ij = ((finProdFinEquiv.symm k).1,(finProdFinEquiv.symm k).2) := by
      constructor
      · intro h
        have hh := congrArg finProdFinEquiv.symm h
        rw [Equiv.symm_apply_apply] at hh
        exact Prod.ext (congrArg Prod.fst hh) (congrArg Prod.snd hh)
      · intro h
        rw [h]
        exact finProdFinEquiv.apply_symm_apply k
    simp only [Pi.single_apply, he]

  have canonical_commutes (d N : ℕ) (X : Configuration d N) :
      flatCLE d N (WithLp.toLp 2 (fun ij =>
        (AddCircle.equivIco (1 : ℝ) 0 (X ij.1 ij.2) : ℝ))) =
      WithLp.toLp 2 (fun k =>
        (AddCircle.equivIco (1 : ℝ) 0 ((ConfigurationFlatten d N X) k) : ℝ)) := by
    rw [flatCLE_apply]
    rfl

  have gradient_commutes (d N : ℕ) (f : Configuration d N → ℝ)
      (hf : f ∈ SmoothCore d N) (X : Configuration d N) :
      flatVector d N (CoordinateGradient f X) =
        TorusGradient (fun x => f ((ConfigurationFlatten d N).symm x))
          (ConfigurationFlatten d N X) := by
    let q := fun y => f (ConfigurationLift d N y)
    let yX : EuclideanSpace ℝ (Fin N × Fin d) := WithLp.toLp 2
      (fun ij => (AddCircle.equivIco (1 : ℝ) 0 (X ij.1 ij.2) : ℝ))
    let yx : EuclideanSpace ℝ (Fin (N*d)) := WithLp.toLp 2
      (fun k => (AddCircle.equivIco (1 : ℝ) 0 ((ConfigurationFlatten d N X) k) : ℝ))
    have hrep : (flatCLE d N).symm yx = yX := by
      rw [← show flatCLE d N yX = yx from canonical_commutes d N X]
      exact (flatCLE d N).symm_apply_apply yX
    have hdq : Differentiable ℝ q := (show ContDiff ℝ ∞ q from hf).differentiable (by simp)
    have hfun : (fun z => f ((ConfigurationFlatten d N).symm (TorusLift (N*d) z))) =
        q ∘ (flatCLE d N).symm := by
      funext z
      exact congrArg f (quotient_inverse_commutes d N z).symm
    ext k
    change fderiv ℝ q yX (EuclideanSpace.single
        ((finProdFinEquiv.symm k).1,(finProdFinEquiv.symm k).2) 1) =
      fderiv ℝ (fun z => f ((ConfigurationFlatten d N).symm (TorusLift (N*d) z))) yx
        (EuclideanSpace.single k 1)
    rw [hfun, fderiv_comp yx hdq.differentiableAt (flatCLE d N).symm.differentiableAt,
      ContinuousLinearEquiv.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      hrep, flatCLE_symm_single]

  have configurationLift_quotient (d N : ℕ) :
      IsOpenQuotientMap (ConfigurationLift d N) := by
    have hc : IsOpenQuotientMap ((↑) : ℝ → AddCircle (1 : ℝ)) :=
      QuotientAddGroup.isOpenQuotientMap_mk
    have hp : IsOpenQuotientMap
        (Pi.map (fun _ : Fin N × Fin d => ((↑) : ℝ → AddCircle (1 : ℝ)))) :=
      IsOpenQuotientMap.piMap (fun _ => hc)
    have he := (PiLp.homeomorph 2 (fun _ : Fin N × Fin d => ℝ)).isOpenQuotientMap
    have hh := (Homeomorph.piCurry (X := Fin N) (Y := Fin d)
      (Z := AddCircle (1 : ℝ))).isOpenQuotientMap
    exact hh.comp (hp.comp he)

  have smoothCore_continuous {d N : ℕ} {f : Configuration d N → ℝ}
      (hf : f ∈ SmoothCore d N) : Continuous f := by
    apply (configurationLift_quotient d N).continuous_comp_iff.mp
    exact (show ContDiff ℝ ∞ (fun y => f (ConfigurationLift d N y)) from hf).continuous

  have smoothCore_bounded {d N : ℕ} {f : Configuration d N → ℝ}
      (hf : f ∈ SmoothCore d N) : ∃ C : ℝ, ∀ X, |f X| ≤ C := by
    have hc := (smoothCore_continuous hf).abs
    rcases isCompact_univ.exists_isMaxOn Set.univ_nonempty hc.continuousOn with ⟨X0,hX0,hmax⟩
    exact ⟨|f X0|, fun X => hmax (Set.mem_univ X)⟩

  -- Derivative descent is the only remaining topological step.
  have lift_translation_eq {d N : ℕ} (y z : EuclideanSpace ℝ (Fin N × Fin d))
      (h : ConfigurationLift d N y = ConfigurationLift d N z)
      (x : EuclideanSpace ℝ (Fin N × Fin d)) :
      ConfigurationLift d N (x + (z-y)) = ConfigurationLift d N x := by
    funext i j
    have hj := congrFun (congrFun h i) j
    change (y (i,j) : AddCircle (1 : ℝ)) = (z (i,j) : AddCircle (1 : ℝ)) at hj
    simp only [ConfigurationLift, PiLp.add_apply, PiLp.sub_apply]
    rw [AddCircle.coe_add, AddCircle.coe_sub, ← hj, sub_self, add_zero]

  have lift_fderiv_eq {d N : ℕ} (f : Configuration d N → ℝ)
      (y z : EuclideanSpace ℝ (Fin N × Fin d))
      (h : ConfigurationLift d N y = ConfigurationLift d N z) :
      fderiv ℝ (fun x => f (ConfigurationLift d N x)) y =
        fderiv ℝ (fun x => f (ConfigurationLift d N x)) z := by
    let q := fun x => f (ConfigurationLift d N x)
    have hfun : (fun x => q (x+(z-y))) = q := by
      funext x
      exact congrArg f (lift_translation_eq y z h x)
    have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := q) (x := y) (z-y)
    rw [hfun] at hd
    simpa using hd

  have coordinateGradient_on_lift {d N : ℕ} (f : Configuration d N → ℝ)
      (y : EuclideanSpace ℝ (Fin N × Fin d)) (ij : Fin N × Fin d) :
      CoordinateGradient f (ConfigurationLift d N y) ij =
        fderiv ℝ (fun x => f (ConfigurationLift d N x)) y
          (EuclideanSpace.single ij 1) := by
    let z : EuclideanSpace ℝ (Fin N × Fin d) := WithLp.toLp 2
      (fun ij => (AddCircle.equivIco (1 : ℝ) 0 (ConfigurationLift d N y ij.1 ij.2) : ℝ))
    have hz : ConfigurationLift d N z = ConfigurationLift d N y := by
      funext i j
      simp [ConfigurationLift, z, AddCircle.coe_equivIco]
    change fderiv ℝ (fun x => f (ConfigurationLift d N x)) z (EuclideanSpace.single ij 1) = _
    rw [lift_fderiv_eq f z y hz]

  have coordinateGradient_energy_continuous {d N : ℕ} {f : Configuration d N → ℝ}
      (hf : f ∈ SmoothCore d N) : Continuous (fun X => ‖CoordinateGradient f X‖^2) := by
    apply (configurationLift_quotient d N).continuous_comp_iff.mp
    have hF : ContDiff ℝ ∞ (fun y => f (ConfigurationLift d N y)) := hf
    have hc : Continuous (fun y : EuclideanSpace ℝ (Fin N × Fin d) =>
        WithLp.toLp 2 (fun ij => fderiv ℝ (fun x => f (ConfigurationLift d N x)) y
          (EuclideanSpace.single ij 1))) := by
      apply (PiLp.continuous_toLp 2 (fun _ : Fin N × Fin d => ℝ)).comp
      apply continuous_pi
      intro ij
      exact (hF.continuous_fderiv_apply (by simp)).comp
        (continuous_id.prodMk continuous_const)
    have he : (fun y => CoordinateGradient f (ConfigurationLift d N y)) =
        (fun y : EuclideanSpace ℝ (Fin N × Fin d) =>
          WithLp.toLp 2 (fun ij => fderiv ℝ (fun x => f (ConfigurationLift d N x)) y
            (EuclideanSpace.single ij 1))) := by
      funext y
      ext ij
      exact coordinateGradient_on_lift f y ij
    have hg : Continuous (fun y => CoordinateGradient f (ConfigurationLift d N y)) := by
      rw [he]
      exact hc
    exact hg.norm.pow 2

  have coordinateGradient_energy_bounded {d N : ℕ} {f : Configuration d N → ℝ}
      (hf : f ∈ SmoothCore d N) : ∃ C : ℝ, ∀ X, ‖CoordinateGradient f X‖^2 ≤ C := by
    have hc := coordinateGradient_energy_continuous hf
    rcases isCompact_univ.exists_isMaxOn Set.univ_nonempty hc.continuousOn with ⟨X0,hX0,hmax⟩
    exact ⟨‖CoordinateGradient f X0‖^2, fun X => hmax (Set.mem_univ X)⟩

  let FiberLift {d N : ℕ} (X : Configuration d N) (i : Fin N)
      (v : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin N × Fin d) :=
    WithLp.toLp 2 (fun ij => if ij.1 = i then v ij.2 else
      (AddCircle.equivIco (1 : ℝ) 0 (X ij.1 ij.2) : ℝ))

  have fiberLift_contDiff {d N : ℕ} (X : Configuration d N) (i : Fin N) :
      ContDiff ℝ ∞ (FiberLift X i) := by
    apply (contDiff_piLp 2).2
    intro ij
    dsimp [FiberLift]
    split_ifs
    · exact contDiff_piLp_apply 2
    · exact contDiff_const

  have fiberLift_configuration {d N : ℕ} (X : Configuration d N) (i : Fin N)
      (v : EuclideanSpace ℝ (Fin d)) :
      ConfigurationLift d N (FiberLift X i v) = Replacement X i (TorusLift d v) := by
    funext k j
    by_cases h : k = i
    · subst k
      simp [ConfigurationLift, FiberLift, Replacement, TorusLift]
    · simp [ConfigurationLift, FiberLift, Replacement, h, AddCircle.coe_equivIco]

  have smoothCore_fiberSmooth {d N : ℕ} {f : Configuration d N → ℝ}
      (hf : f ∈ SmoothCore d N) (X : Configuration d N) (i : Fin N) :
      TorusSmooth (fun z => f (Replacement X i z)) := by
    have hF : ContDiff ℝ ∞ (fun y => f (ConfigurationLift d N y)) := hf
    have h := hF.comp (fiberLift_contDiff X i)
    simpa only [TorusSmooth, Function.comp_def, fiberLift_configuration] using h


  let FiberInjection {d N : ℕ} (i : Fin N) :
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin N × Fin d) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N × Fin d => ℝ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (fun ij => if ij.1 = i then
        (ContinuousLinearMap.proj ij.2).comp
          (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toContinuousLinearMap
        else 0))

  have fiberInjection_apply {d N : ℕ} (i : Fin N) (v : EuclideanSpace ℝ (Fin d))
      (ij : Fin N × Fin d) :
      FiberInjection i v ij = if ij.1 = i then v ij.2 else 0 := by
    by_cases h : ij.1 = i
    · simp [FiberInjection, h]
    · simp [FiberInjection, h]

  have fiberLift_eq_affine {d N : ℕ} (X : Configuration d N) (i : Fin N)
      (v : EuclideanSpace ℝ (Fin d)) :
      FiberLift X i v = FiberInjection i v + FiberLift X i 0 := by
    ext ij
    by_cases h : ij.1 = i <;> simp [FiberLift, fiberInjection_apply, h]

  have fiberLift_hasFDerivAt {d N : ℕ} (X : Configuration d N) (i : Fin N)
      (v : EuclideanSpace ℝ (Fin d)) :
      HasFDerivAt (FiberLift X i) (FiberInjection i) v := by
    have h := ((FiberInjection i).hasFDerivAt (x := v)).add_const (FiberLift X i 0)
    simpa only [← fiberLift_eq_affine] using h

  have fiberInjection_single {d N : ℕ} (i : Fin N) (j : Fin d) :
      FiberInjection i (EuclideanSpace.single j 1) = EuclideanSpace.single (i,j) 1 := by
    ext ij
    simp [fiberInjection_apply]
    aesop

  have smoothCore_fiber_fderiv {d N : ℕ} {f : Configuration d N → ℝ}
      (hf : f ∈ SmoothCore d N) (X : Configuration d N) (i : Fin N)
      (v : EuclideanSpace ℝ (Fin d)) (j : Fin d) :
      fderiv ℝ (fun y => f (Replacement X i (TorusLift d y))) v
        (EuclideanSpace.single j 1) =
      fderiv ℝ (fun y => f (ConfigurationLift d N y)) (FiberLift X i v)
        (EuclideanSpace.single (i,j) 1) := by
    have hF : ContDiff ℝ ∞ (fun y => f (ConfigurationLift d N y)) := hf
    have hdF := (hF.differentiable (by simp)).differentiableAt (x := FiberLift X i v)
    have h := hdF.hasFDerivAt.comp v (fiberLift_hasFDerivAt X i v)
    have heq := h.fderiv
    have hfun : (fun y => f (ConfigurationLift d N (FiberLift X i y))) =
        (fun y => f (Replacement X i (TorusLift d y))) := by
      funext y
      rw [fiberLift_configuration]
    change fderiv ℝ (fun y => f (Replacement X i (TorusLift d y))) v
      (EuclideanSpace.single j 1) = _
    dsimp [Function.comp_def] at heq
    rw [← hfun, heq]
    simp [fiberInjection_single]


  have fiberLift_canonical {d N : ℕ} (X : Configuration d N) (i : Fin N)
      (z : UnitAddTorus (Fin d)) :
      FiberLift X i (WithLp.toLp 2 (fun j =>
        (AddCircle.equivIco (1 : ℝ) 0 (z j) : ℝ))) =
      WithLp.toLp 2 (fun ij => (AddCircle.equivIco (1 : ℝ) 0
        ((Replacement X i z) ij.1 ij.2) : ℝ)) := by
    ext ij
    by_cases h : ij.1 = i
    · simp [FiberLift, Replacement, h]
    · simp [FiberLift, Replacement, h]

  have smoothCore_fiber_gradient_component {d N : ℕ} {f : Configuration d N → ℝ}
      (hf : f ∈ SmoothCore d N) (X : Configuration d N) (i : Fin N)
      (z : UnitAddTorus (Fin d)) (j : Fin d) :
      TorusGradient (fun z => f (Replacement X i z)) z j =
        CoordinateGradient f (Replacement X i z) (i,j) := by
    change fderiv ℝ (fun y => f (Replacement X i (TorusLift d y)))
        (WithLp.toLp 2 (fun j => (AddCircle.equivIco (1 : ℝ) 0 (z j) : ℝ)))
        (EuclideanSpace.single j 1) = _
    rw [smoothCore_fiber_fderiv hf X i, fiberLift_canonical]
    rfl

  have smoothCore_fiber_gradient_norm {d N : ℕ} {f : Configuration d N → ℝ}
      (hf : f ∈ SmoothCore d N) (X : Configuration d N) (i : Fin N)
      (z : UnitAddTorus (Fin d)) :
      ‖TorusGradient (fun z => f (Replacement X i z)) z‖^2 =
        ∑ j : Fin d, (CoordinateGradient f (Replacement X i z) (i,j))^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro j hj
    rw [smoothCore_fiber_gradient_component hf X i]

  have coordinateGradient_norm_sum {d N : ℕ} (f : Configuration d N → ℝ)
      (X : Configuration d N) :
      ‖CoordinateGradient f X‖^2 =
        ∑ i : Fin N, ∑ j : Fin d, (CoordinateGradient f X (i,j))^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Fintype.sum_prod_type _

  have flatten_symm_measurable (d N : ℕ) : Measurable (ConfigurationFlatten d N).symm := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    exact measurable_pi_apply (finProdFinEquiv (i,j))

  refine ⟨flatten_measurable d N, flatten_symm_measurable d N,
    (flatten_preserves_volume d N).map_eq, ?_⟩
  intro f hf
  refine ⟨(smooth_iff d N f).mp hf, (smoothCore_continuous hf).measurable,
    smoothCore_bounded hf, (coordinateGradient_energy_continuous hf).measurable,
    coordinateGradient_energy_bounded hf, ?_, ?_, ?_⟩
  · intro X
    rw [← gradient_commutes d N f hf X, flatVector_norm_sq]
  · intro X i
    exact ⟨smoothCore_fiberSmooth hf X i, smoothCore_fiber_gradient_norm hf X i⟩
  · exact coordinateGradient_norm_sum f
