module

public import Tablet.RieszKernel
public import Tablet.EuclideanDerivativeCoordinates
public import Mathlib.Tactic

@[expose] public section
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace AtomicInteractionSource
private noncomputable def D {d : ℕ} (u : OneParticle d → ℝ) (v x : OneParticle d) := fderiv ℝ u x v
private noncomputable def softKernel (d : ℕ) (s ε : ℝ) (z : OneParticle d) :=
  (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2) / s
private noncomputable def softForce (d : ℕ) (s ε : ℝ) (z : OneParticle d) :=
  -((‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1) • z)
private noncomputable def basisLaplacian {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (OneParticle d)) (u : OneParticle d → ℝ) (x : OneParticle d) :=
  ∑ i, D (D u (b i)) (b i) x
private theorem contDiff_D {d : ℕ} {u : OneParticle d → ℝ}
    (hu : ContDiff ℝ 2 u) (v : OneParticle d) : ContDiff ℝ 1 (D u v) := by
  exact (hu.contDiff_fderiv_apply (m := 1) (by norm_num)).comp
    (contDiff_id.prodMk contDiff_const)
private theorem softKernel_hasFDerivAt (d : ℕ) (s ε : ℝ) (hs : 0 < s) (hε : 0 < ε)
    (z : OneParticle d) : HasFDerivAt (softKernel d s ε) (innerSL ℝ (softForce d s ε z)) z := by
  have hbase : 0 < ‖z‖ ^ 2 + ε ^ 2 := by positivity
  have hder := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.add_const (ε ^ 2)).rpow_const
    (p := -s / 2) (Or.inl hbase.ne')
  have hscaled := hder.const_smul s⁻¹
  have heq : s⁻¹ • ((-s / 2 * (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1)) •
      (2 • innerSL ℝ z)) = innerSL ℝ (softForce d s ε z) := by
    ext h
    simp only [smul_apply, smul_eq_mul, nsmul_eq_mul, innerSL_apply_apply,
      softForce, inner_neg_left, real_inner_smul_left]
    field_simp
    ring
  rw [heq] at hscaled
  have hf : (s⁻¹ • fun x : OneParticle d => (‖x‖ ^ 2 + ε ^ 2) ^ (-s / 2)) = softKernel d s ε := by
    funext x
    simp only [Pi.smul_apply, softKernel, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [hf] at hscaled
  exact hscaled
private theorem softKernel_directional (d : ℕ) (s ε : ℝ) (hs : 0 < s) (hε : 0 < ε)
    (v z : OneParticle d) :
    D (softKernel d s ε) v z =
      -((‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1) * inner ℝ v z) := by
  rw [D, (softKernel_hasFDerivAt d s ε hs hε z).fderiv]
  simp only [innerSL_apply_apply, softForce, inner_neg_left, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm]

private theorem softKernel_second_directional (d : ℕ) (s ε : ℝ) (hs : 0 < s) (hε : 0 < ε)
    (v z : OneParticle d) :
    D (D (softKernel d s ε) v) v z =
      (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 2) *
        ((s + 2) * (inner ℝ v z) ^ 2 - (‖z‖ ^ 2 + ε ^ 2) * ‖v‖ ^ 2) := by
  have hbase : 0 < ‖z‖ ^ 2 + ε ^ 2 := by positivity
  have hd := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.add_const (ε ^ 2)).rpow_const
    (p := -s / 2 - 1) (Or.inl hbase.ne')
  have hp := (hd.mul (innerSL ℝ v).hasFDerivAt).neg
  have hfun : -((fun x : OneParticle d => (‖x‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1)) * (innerSL ℝ v)) =
      (fun x : OneParticle d => -((‖x‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1) * inner ℝ v x)) := by
    funext x
    simp only [Pi.neg_apply, Pi.mul_apply, innerSL_apply_apply]
  rw [hfun] at hp
  have heq : D (softKernel d s ε) v =
      (fun z : OneParticle d => -((‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1) * inner ℝ v z)) := by
    funext z
    exact softKernel_directional d s ε hs hε v z
  rw [heq, D, hp.fderiv]
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, innerSL_apply_apply,
    real_inner_self_eq_norm_sq, real_inner_comm]
  have hexp : -s / 2 - 1 - 1 = -s / 2 - 2 := by ring
  rw [hexp]
  have hpow : (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1) =
      (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 2) * (‖z‖ ^ 2 + ε ^ 2) := by
    calc
      _ = (‖z‖ ^ 2 + ε ^ 2) ^ ((-s / 2 - 2) + 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hbase, Real.rpow_one]
  rw [hpow]
  ring

-- Correct actual radial Hessian trace, including the critical s=d−2 endpoint.
private theorem softKernel_laplacian (d : ℕ) (s ε : ℝ) (hs : 0 < s) (hε : 0 < ε) (z : OneParticle d) :
    basisLaplacian (EuclideanSpace.basisFun (Fin d) ℝ) (softKernel d s ε) z =
      (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 2) *
        ((s + 2 - (d : ℝ)) * ‖z‖ ^ 2 - (d : ℝ) * ε ^ 2) := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hsum : (∑ i : Fin d, (inner ℝ (b i) z) ^ 2) = ‖z‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs, real_inner_comm] using b.sum_sq_norm_inner_left z
  have hnorm : ∀ i : Fin d, ‖b i‖ ^ 2 = 1 := by
    intro i
    simp [b]
  change (∑ i : Fin d, D (D (softKernel d s ε) (b i)) (b i) z) = _
  simp only [softKernel_second_directional d s ε hs hε, hnorm]
  rw [← Finset.mul_sum]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  ring

private theorem softKernel_contDiff (d : ℕ) (s ε : ℝ) (hε : 0 < ε) {n : ℕ∞} :
    ContDiff ℝ n (softKernel d s ε) := by
  unfold softKernel
  exact (((contDiff_norm_sq ℝ).add contDiff_const).rpow_const_of_ne
    (fun z => ne_of_gt (by positivity : 0 < ‖z‖ ^ 2 + ε ^ 2))).div_const s

private theorem D_translate {d : ℕ} (u : OneParticle d → ℝ) (hu : Differentiable ℝ u) (y v x : OneParticle d) :
    D (fun z => u (z - y)) v x = D u v (x - y) := by
  have H := (hu (x - y)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const y)
  simp only [ContinuousLinearMap.comp_id] at H
  simp only [Function.comp_def] at H
  exact congrArg (fun L : OneParticle d →L[ℝ] ℝ => L v) H.fderiv

private theorem D_const_mul {d : ℕ} (u : OneParticle d → ℝ) (hu : Differentiable ℝ u) (a : ℝ) (v x : OneParticle d) :
    D (fun z => a * u z) v x = a * D u v x := by
  rw [D, fderiv_const_mul (hu x)]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, D]

private theorem D_finite_sum {d : ℕ} {ι : Type*} (J : Finset ι) (u : ι → OneParticle d → ℝ)
    (hu : ∀ j ∈ J, Differentiable ℝ (u j)) (v x : OneParticle d) :
    D (fun z => ∑ j ∈ J, u j z) v x = ∑ j ∈ J, D (u j) v x := by
  rw [D, fderiv_fun_sum (fun j hj => hu j hj x)]
  simp only [ContinuousLinearMap.sum_apply, D]

private theorem translated_softKernel_second (d : ℕ) (s ε : ℝ) (hs : 0 < s) (hε : 0 < ε)
    (a : ℝ) (y v x : OneParticle d) :
    D (D (fun z => a * softKernel d s ε (z - y)) v) v x =
      a * D (D (softKernel d s ε) v) v (x - y) := by
  have hkd : ContDiff ℝ 2 (softKernel d s ε) := softKernel_contDiff d s ε hε
  have ht : ContDiff ℝ 2 (fun z => softKernel d s ε (z - y)) :=
    hkd.comp (contDiff_id.sub contDiff_const)
  have heq : D (fun z => a * softKernel d s ε (z - y)) v =
      (fun z => a * D (softKernel d s ε) v (z - y)) := by
    funext z
    rw [D_const_mul _ (ht.differentiable (by norm_num)), D_translate _ (hkd.differentiable (by norm_num))]
  rw [heq]
  have hder := contDiff_D hkd v
  have htD : Differentiable ℝ (fun z => D (softKernel d s ε) v (z - y)) := by
    simpa only [Function.comp_def, id_eq] using
      ((hder.comp (contDiff_id.sub contDiff_const)).differentiable (by norm_num))
  rw [D_const_mul _ htD, D_translate _ (hder.differentiable (by norm_num))]

private noncomputable def atomicU {d : ℕ} {ι : Type*} (J : Finset ι) (a : ι → ℝ)
    (y : ι → OneParticle d) (s ε : ℝ) (x : OneParticle d) : ℝ :=
  ∑ j ∈ J, a j * softKernel d s ε (x - y j)

private theorem atomicU_contDiff {d : ℕ} {ι : Type*} (J : Finset ι) (a : ι → ℝ)
    (y : ι → OneParticle d) (s ε : ℝ) (hε : 0 < ε) {n : ℕ∞} :
    ContDiff ℝ n (atomicU J a y s ε) := by
  apply ContDiff.sum
  intro j hj
  exact contDiff_const.mul ((softKernel_contDiff d s ε hε).comp (contDiff_id.sub contDiff_const))

private theorem atomicU_laplacian {d : ℕ} {ι : Type*} (J : Finset ι) (a : ι → ℝ)
    (y : ι → OneParticle d) (s ε : ℝ) (hs : 0 < s) (hε : 0 < ε) (x : OneParticle d) :
    basisLaplacian (EuclideanSpace.basisFun (Fin d) ℝ) (atomicU J a y s ε) x =
      ∑ j ∈ J, a j * basisLaplacian (EuclideanSpace.basisFun (Fin d) ℝ)
        (softKernel d s ε) (x - y j) := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hterm : ∀ j ∈ J, ContDiff ℝ 2 (fun z => a j * softKernel d s ε (z - y j)) := by
    intro j hj
    exact contDiff_const.mul ((softKernel_contDiff d s ε hε).comp (contDiff_id.sub contDiff_const))
  have hD : ∀ v : OneParticle d, D (atomicU J a y s ε) v =
      (fun z => ∑ j ∈ J, D (fun w => a j * softKernel d s ε (w - y j)) v z) := by
    intro v
    funext z
    exact D_finite_sum J _ (fun j hj => (hterm j hj).differentiable (by norm_num)) v z
  change (∑ i : Fin d, D (D (atomicU J a y s ε) (b i)) (b i) x) = _
  simp_rw [hD]
  simp_rw [D_finite_sum J _ (fun j hj => (contDiff_D (hterm j hj) _).differentiable (by norm_num)),
    translated_softKernel_second d s ε hs hε]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  change _ = a j * ∑ i : Fin d, D (D (softKernel d s ε) (b i)) (b i) (x - y j)
  rw [Finset.mul_sum]


private theorem basis_eq_actual {d : ℕ} (u : OneParticle d → ℝ)
    (hu : ContDiff ℝ 2 u) (x : OneParticle d) :
    basisLaplacian (EuclideanSpace.basisFun (Fin d) ℝ) u x = EuclideanLaplacian u x := by
  rw [(EuclideanDerivativeCoordinates u x).2]
  apply Finset.sum_congr rfl
  intro i hi
  let v := EuclideanSpace.basisFun (Fin d) ℝ i
  have hcd : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hfd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    hcd.differentiable (by norm_num) x
  have h := (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp x hfd.hasFDerivAt
  simp only [Function.comp_def, ContinuousLinearMap.apply_apply] at h
  change fderiv ℝ (fun z => fderiv ℝ u z v) x v = (fderiv ℝ (fderiv ℝ u) x v) v
  rw [h.fderiv]
  rfl
end AtomicInteractionSource
open AtomicInteractionSource
-- [TABLET NODE: AtomicInteractionSource]
theorem AtomicInteractionSource (d : ℕ) (s ε : ℝ) (hs : 0 < s)
    (hsd : s ≤ (d : ℝ) - 2) (hε : 0 < ε) {ι : Type*}
    (J : Finset ι) (a : ι → ℝ) (y : ι → OneParticle d)
    (ha : ∀ j ∈ J, 0 ≤ a j) :
    let U := fun x => ∑ j ∈ J, a j * RieszKernel s ε (x - y j)
    ContDiff ℝ 2 U ∧ ∀ x,
      -EuclideanLaplacian U x =
        ∑ j ∈ J, a j * (((d : ℝ) - s - 2) * ‖x - y j‖ ^ 2 + (d : ℝ) * ε ^ 2) *
          (‖x - y j‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 2) ∧
      0 ≤ -EuclideanLaplacian U x := by
-- BODY
  have he : (fun x => ∑ j ∈ J, a j * RieszKernel s ε (x - y j)) =
      atomicU J a y s ε := by
    funext x
    simp only [RieszKernel, if_neg (ne_of_gt hε), atomicU, softKernel]
  dsimp only
  rw [he]
  have hU : ContDiff ℝ 2 (atomicU J a y s ε) := atomicU_contDiff J a y s ε hε
  refine ⟨hU, ?_⟩
  intro x
  have hformula : -EuclideanLaplacian (atomicU J a y s ε) x =
      ∑ j ∈ J, a j * (((d : ℝ) - s - 2) * ‖x - y j‖ ^ 2 + (d : ℝ) * ε ^ 2) *
        (‖x - y j‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 2) := by
    rw [← basis_eq_actual _ hU, atomicU_laplacian J a y s ε hs hε,
      ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [softKernel_laplacian d s ε hs hε]
    ring
  refine ⟨hformula, ?_⟩
  rw [hformula]
  apply Finset.sum_nonneg
  intro j hj
  have hc : 0 ≤ (d : ℝ) - s - 2 := by linarith
  have haj := ha j hj
  positivity
