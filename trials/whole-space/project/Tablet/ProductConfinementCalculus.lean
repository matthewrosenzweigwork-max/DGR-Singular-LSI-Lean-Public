module

public import Tablet.ParticlePosition
public import Tablet.GradientNormIdentity
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000

-- [TABLET NODE: ProductConfinementCalculus]
theorem ProductConfinementCalculus (d N : ℕ) (V : OneParticle d → ℝ)
    (hV : ContDiff ℝ 2 V) :
    let W := fun X : ParticleConfig d N => ∑ i : Fin N, V (ParticlePosition X i)
    ContDiff ℝ 2 W ∧ ∀ X,
      ‖EuclideanGradient W X‖^2 = ∑ i : Fin N, ‖EuclideanGradient V (ParticlePosition X i)‖^2 ∧
      EuclideanLaplacian W X = ∑ i : Fin N, EuclideanLaplacian V (ParticlePosition X i) := by
-- BODY
  classical
  let P (i : Fin N) : ParticleConfig d N →L[ℝ] OneParticle d :=
    (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin d)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (fun k : Fin d => EuclideanSpace.proj (i,k)))
  have hP (i : Fin N) (X : ParticleConfig d N) : P i X = ParticlePosition X i := rfl
  have hPb (i : Fin N) (k : Fin d) :
      P i (EuclideanSpace.basisFun (Fin N × Fin d) ℝ (i,k)) = EuclideanSpace.basisFun (Fin d) ℝ k := by
    ext l
    change (EuclideanSpace.basisFun (Fin N × Fin d) ℝ (i,k)) (i,l) =
      (EuclideanSpace.basisFun (Fin d) ℝ k) l
    simp [EuclideanSpace.basisFun_apply]
  let W := fun X : ParticleConfig d N => ∑ i : Fin N, V (ParticlePosition X i)
  have hW : ContDiff ℝ 2 W := by
    apply ContDiff.sum
    intro i _
    exact hV.comp (P i).contDiff
  have hg (X : ParticleConfig d N) : EuclideanGradient W X =
      WithLp.toLp 2 (fun p : Fin N × Fin d => EuclideanGradient V (ParticlePosition X p.1) p.2) := by
    let g : ParticleConfig d N := WithLp.toLp 2
      (fun p : Fin N × Fin d => EuclideanGradient V (ParticlePosition X p.1) p.2)
    have heach (i : Fin N) (_ : i ∈ (Finset.univ : Finset (Fin N))) :=
      ((hV.differentiable (by norm_num) (ParticlePosition X i)).hasGradientAt.hasFDerivAt).comp X
        (P i).hasFDerivAt
    have hd := HasFDerivAt.fun_sum heach
    have heq : (∑ i : Fin N, (InnerProductSpace.toDual ℝ (OneParticle d)
        (gradient V (ParticlePosition X i))).comp (P i)) = innerSL ℝ g := by
      ext Y
      simp only [sum_apply, ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply,
        hP, innerSL_apply_apply, PiLp.inner_apply, Fintype.sum_prod_type,
        g, ParticlePosition, EuclideanGradient, Real.inner_apply]
    rw [heq] at hd
    change HasFDerivAt W (innerSL ℝ g) X at hd
    apply (InnerProductSpace.toDual ℝ (ParticleConfig d N)).injective
    change (InnerProductSpace.toDual ℝ (ParticleConfig d N)) (gradient W X) = _
    rw [toDual_gradient, hd.fderiv]
    rfl
  let D {ι : Type} [Fintype ι] (f : EuclideanSpace ℝ ι → ℝ)
      (v x : EuclideanSpace ℝ ι) : ℝ := fderiv ℝ f x v
  have hcd {ι : Type} [Fintype ι] (f : EuclideanSpace ℝ ι → ℝ)
      (hf : ContDiff ℝ 2 f) (v : EuclideanSpace ℝ ι) : ContDiff ℝ 1 (D f v) := by
    exact (hf.contDiff_fderiv_apply (m := 1) (by norm_num)).comp
      (contDiff_id.prodMk contDiff_const)
  have htrace {ι : Type} [Fintype ι] (f : EuclideanSpace ℝ ι → ℝ)
      (hf : ContDiff ℝ 2 f) (x : EuclideanSpace ℝ ι) :
      EuclideanLaplacian f x = ∑ k : ι,
        D (D f (EuclideanSpace.basisFun ι ℝ k)) (EuclideanSpace.basisFun ι ℝ k) x := by
    rw [(EuclideanDerivativeCoordinates f x).2]
    apply Finset.sum_congr rfl
    intro k _
    let v := EuclideanSpace.basisFun ι ℝ k
    have hcf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
    have hfd : DifferentiableAt ℝ (fderiv ℝ f) x := hcf.differentiable (by norm_num) x
    have h := (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp x hfd.hasFDerivAt
    simp only [Function.comp_def, ContinuousLinearMap.apply_apply] at h
    change (fderiv ℝ (fderiv ℝ f) x v) v = fderiv ℝ (fun z => fderiv ℝ f z v) x v
    rw [h.fderiv]
    rfl
  have hfirst (i : Fin N) (k : Fin d) (X : ParticleConfig d N) :
      D W (EuclideanSpace.basisFun (Fin N × Fin d) ℝ (i,k)) X =
        D V (EuclideanSpace.basisFun (Fin d) ℝ k) (ParticlePosition X i) := by
    have hc := congrArg (fun L : ParticleConfig d N →L[ℝ] ℝ =>
      L (EuclideanSpace.basisFun (Fin N × Fin d) ℝ (i,k)))
      (toDual_gradient (𝕜 := ℝ) (f := W) (x := X))
    have ho := congrArg (fun L : OneParticle d →L[ℝ] ℝ =>
      L (EuclideanSpace.basisFun (Fin d) ℝ k))
      (toDual_gradient (𝕜 := ℝ) (f := V) (x := ParticlePosition X i))
    simp only [InnerProductSpace.toDual_apply_apply, EuclideanSpace.inner_basisFun_real] at hc ho
    have hgc := congrArg (fun Z : ParticleConfig d N => Z (i,k)) (hg X)
    change gradient W X (i,k) = gradient V (ParticlePosition X i) k at hgc
    exact hc.symm.trans (hgc.trans ho)
  have hsecond (i : Fin N) (k : Fin d) (X : ParticleConfig d N) :
      D (D W (EuclideanSpace.basisFun (Fin N × Fin d) ℝ (i,k)))
          (EuclideanSpace.basisFun (Fin N × Fin d) ℝ (i,k)) X =
        D (D V (EuclideanSpace.basisFun (Fin d) ℝ k))
          (EuclideanSpace.basisFun (Fin d) ℝ k) (ParticlePosition X i) := by
    have hf : D W (EuclideanSpace.basisFun (Fin N × Fin d) ℝ (i,k)) =
        D V (EuclideanSpace.basisFun (Fin d) ℝ k) ∘ P i := by
      funext Y
      exact hfirst i k Y
    rw [hf]
    dsimp only [D]
    rw [fderiv_comp X ((hcd V hV _).differentiable (by norm_num) _) (P i).differentiableAt,
      (P i).fderiv]
    simp only [ContinuousLinearMap.comp_apply, hPb, hP]
    rfl
  refine ⟨hW, ?_⟩
  intro X
  constructor
  · rw [hg]
    simp only [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  · rw [htrace W hW]
    simp only [Fintype.sum_prod_type, hsecond]
    apply Finset.sum_congr rfl
    intro i _
    rw [htrace V hV]
