module

public import Tablet.RelativePairCoordinates
public import Tablet.ParticlePosition
public import Tablet.GradientNormIdentity
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000

-- [TABLET NODE: PairRelativeGradient]
theorem PairRelativeGradient {d N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (u : OneParticle d → ℝ) (hu : ContDiff ℝ 1 u) (X : ParticleConfig d N) :
    ‖EuclideanGradient (fun Y => u (ParticlePosition Y i - ParticlePosition Y j)) X‖ =
      Real.sqrt 2 * ‖EuclideanGradient u (ParticlePosition X i - ParticlePosition X j)‖ := by
-- BODY
  classical
  obtain ⟨e, he, _, _⟩ := RelativePairCoordinates (d := d) i j hij
  let L : ParticleConfig d N →L[ℝ] OneParticle d :=
    Real.sqrt 2 • ((WithLp.fstL 2 ℝ (OneParticle d)
      (EuclideanSpace ℝ {p : Fin N × Fin d // p.1 ≠ i})).comp
        e.toContinuousLinearEquiv.toContinuousLinearMap)
  have hL (Y : ParticleConfig d N) : L Y = ParticlePosition Y i - ParticlePosition Y j := by
    ext l
    change Real.sqrt 2 * (WithLp.ofLp (e Y)).1 l = Y (i, l) - Y (j, l)
    rw [he]
    have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
  let v := EuclideanGradient u (L X)
  let z : ParticleConfig d N := Real.sqrt 2 • e.symm (WithLp.toLp 2 (v, 0))
  have heinner (h : ParticleConfig d N) :
      inner ℝ (e.symm (WithLp.toLp 2 (v, 0))) h = inner ℝ v (WithLp.ofLp (e h)).1 := by
    have hh := e.inner_map_map (e.symm (WithLp.toLp 2 (v, 0))) h
    rw [e.apply_symm_apply] at hh
    simpa only [WithLp.prod_inner_apply, inner_zero_left, add_zero] using hh.symm
  have hdual : fderiv ℝ u (L X) = innerSL ℝ v := by
    symm
    change (InnerProductSpace.toDual ℝ (OneParticle d)) (gradient u (L X)) = _
    exact toDual_gradient
  have hcomp : (innerSL ℝ v).comp L = innerSL ℝ z := by
    ext h
    simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, L,
      ContinuousLinearMap.smul_apply, z, real_inner_smul_left, real_inner_smul_right,
      heinner]
    rfl
  have hd := ((hu.differentiable (by norm_num) (L X)).hasFDerivAt).comp X L.hasFDerivAt
  rw [hdual, hcomp] at hd
  have hgrad : EuclideanGradient (u ∘ L) X = z := by
    apply (InnerProductSpace.toDual ℝ (ParticleConfig d N)).injective
    rw [EuclideanGradient, toDual_gradient, hd.fderiv]
    rfl
  have hfun : (fun Y : ParticleConfig d N => u (ParticlePosition Y i - ParticlePosition Y j)) = u ∘ L := by
    funext Y
    simp only [Function.comp_apply, hL]
  rw [hfun, hgrad]
  dsimp only [z]
  rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg 2), e.symm.norm_map,
    WithLp.norm_toLp_fst]
  simp only [v, hL]
