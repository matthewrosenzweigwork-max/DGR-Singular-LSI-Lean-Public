module

public import Tablet.RelativePairCoordinates
public import Tablet.ParticlePosition
public import Tablet.EuclideanDerivativeCoordinates
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000

-- [TABLET NODE: PairRelativeLaplacian]
theorem PairRelativeLaplacian {d N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (u : OneParticle d → ℝ) (hu : ContDiff ℝ 2 u) (X : ParticleConfig d N) :
    EuclideanLaplacian (fun Y => u (ParticlePosition Y i - ParticlePosition Y j)) X =
      2 * EuclideanLaplacian u (ParticlePosition X i - ParticlePosition X j) := by
-- BODY
  classical
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
    have hfd : DifferentiableAt ℝ (fderiv ℝ f) x :=
      hcf.differentiable (by norm_num) x
    have h := (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp x hfd.hasFDerivAt
    simp only [Function.comp_def, ContinuousLinearMap.apply_apply] at h
    change (fderiv ℝ (fderiv ℝ f) x v) v = fderiv ℝ (fun z => fderiv ℝ f z v) x v
    rw [h.fderiv]
    rfl
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
  have hcomp (f : OneParticle d → ℝ) (hf : Differentiable ℝ f)
      (v Y : ParticleConfig d N) : D (f ∘ L) v Y = D f (L v) (L Y) := by
    dsimp only [D]
    rw [fderiv_comp Y (hf _) L.differentiableAt, L.fderiv]
    rfl
  have hsecond (v Y : ParticleConfig d N) :
      D (D (u ∘ L) v) v Y = D (D u (L v)) (L v) (L Y) := by
    have hd : D (u ∘ L) v = D u (L v) ∘ L := by
      funext Z
      exact hcomp u (hu.differentiable (by norm_num)) v Z
    rw [hd]
    exact hcomp (D u (L v)) ((hcd u hu _).differentiable (by norm_num)) v Y
  have hLb1 (k : Fin d) :
      L (EuclideanSpace.basisFun (Fin N × Fin d) ℝ (i,k)) = EuclideanSpace.basisFun (Fin d) ℝ k := by
    rw [hL]
    ext l
    change (EuclideanSpace.basisFun (Fin N × Fin d) ℝ (i,k)) (i,l) -
      (EuclideanSpace.basisFun (Fin N × Fin d) ℝ (i,k)) (j,l) =
      (EuclideanSpace.basisFun (Fin d) ℝ k) l
    simp [EuclideanSpace.basisFun_apply, hij, hij.symm]
  have hLb2 (k : Fin d) :
      L (EuclideanSpace.basisFun (Fin N × Fin d) ℝ (j,k)) = -EuclideanSpace.basisFun (Fin d) ℝ k := by
    rw [hL]
    ext l
    change (EuclideanSpace.basisFun (Fin N × Fin d) ℝ (j,k)) (i,l) -
      (EuclideanSpace.basisFun (Fin N × Fin d) ℝ (j,k)) (j,l) =
      -(EuclideanSpace.basisFun (Fin d) ℝ k) l
    simp [EuclideanSpace.basisFun_apply, hij, hij.symm]
  have hLbo (a : Fin N) (hai : a ≠ i) (haj : a ≠ j) (k : Fin d) :
      L (EuclideanSpace.basisFun (Fin N × Fin d) ℝ (a,k)) = 0 := by
    rw [hL]
    ext l
    change (EuclideanSpace.basisFun (Fin N × Fin d) ℝ (a,k)) (i,l) -
      (EuclideanSpace.basisFun (Fin N × Fin d) ℝ (a,k)) (j,l) = 0
    simp [EuclideanSpace.basisFun_apply, hai, haj]
  have hneg (v z : OneParticle d) : D (D u (-v)) (-v) z = D (D u v) v z := by
    have hd : D u (-v) = fun w => -D u v w := by
      funext w
      simp [D]
    rw [hd]
    dsimp only [D]
    rw [fderiv_fun_neg]
    simp
  have hrows (f : Fin N → ℝ) : (∑ a, f a) =
      f i + f j + ∑ a ∈ (Finset.univ.erase i).erase j, f a := by
    have hi : i ∈ (Finset.univ : Finset (Fin N)) := Finset.mem_univ i
    have hj : j ∈ (Finset.univ.erase i : Finset (Fin N)) := by simp [hij.symm]
    rw [← Finset.add_sum_erase _ _ hi, ← Finset.add_sum_erase _ _ hj]
    ring
  have hfun : (fun Y : ParticleConfig d N => u (ParticlePosition Y i - ParticlePosition Y j)) = u ∘ L := by
    funext Y
    simp only [Function.comp_apply, hL]
  rw [hfun, htrace _ (hu.comp L.contDiff), htrace u hu, Fintype.sum_prod_type, hrows]
  have hfirst (k : Fin d) := hsecond (EuclideanSpace.basisFun (Fin N × Fin d) ℝ (i,k)) X
  simp only [hLb1] at hfirst
  have hlast (k : Fin d) := hsecond (EuclideanSpace.basisFun (Fin N × Fin d) ℝ (j,k)) X
  simp only [hLb2, hneg] at hlast
  have hrest : (∑ a ∈ (Finset.univ.erase i).erase j, ∑ k : Fin d,
      D (D (u ∘ L) (EuclideanSpace.basisFun (Fin N × Fin d) ℝ (a,k)))
        (EuclideanSpace.basisFun (Fin N × Fin d) ℝ (a,k)) X) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    have hai : a ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
    have haj : a ≠ j := (Finset.mem_erase.mp ha).1
    apply Finset.sum_eq_zero
    intro k _
    rw [hsecond, hLbo a hai haj]
    simp [D]
  simp_rw [hfirst, hlast]
  rw [hrest, hL]
  ring
