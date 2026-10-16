import Tablet.EuclideanDerivativeCoordinates
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic
set_option maxHeartbeats 1600000
open MeasureTheory Measure
namespace EuclideanGroundState

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private noncomputable def D (u : E → ℝ) (v : E) (x : E) : ℝ := fderiv ℝ u x v

private theorem continuous_D {u : E → ℝ} (hu : ContDiff ℝ 1 u) (v : E) :
    Continuous (D u v) := by
  exact (hu.continuous_fderiv_apply (by norm_num)).comp
    (continuous_id.prodMk continuous_const)

private theorem contDiff_D {u : E → ℝ} (hu : ContDiff ℝ 2 u) (v : E) :
    ContDiff ℝ 1 (D u v) := by
  exact (hu.contDiff_fderiv_apply (m := 1) (by norm_num)).comp
    (contDiff_id.prodMk contDiff_const)

private theorem compact_D {u : E → ℝ} (hu : HasCompactSupport u) (v : E) :
    HasCompactSupport (D u v) := by
  exact hu.fderiv_apply ℝ v

variable (μ : Measure E) [IsAddHaarMeasure μ]

private theorem integrable_product_compact (a b : E → ℝ) (ha : Continuous a)
    (hb : Continuous b) (hcb : HasCompactSupport b) :
    Integrable (fun x => a x * b x) μ := by
  exact (ha.mul hb).integrable_of_hasCompactSupport hcb.mul_left

private theorem compact_cross_ibp (H ψ : E → ℝ) (hH : ContDiff ℝ 2 H)
    (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) (v : E) :
    (∫ x, D H v x * ψ x * D ψ v x ∂μ) =
      -(1 / 2 : ℝ) * ∫ x, D (D H v) v x * ψ x ^ 2 ∂μ := by
  have hDH := contDiff_D hH v
  have hcDH := continuous_D (hH.of_le (by norm_num)) v
  have hcDDH := continuous_D hDH v
  have hcDψ := continuous_D hψ v
  have hcψ2 : HasCompactSupport (fun x => ψ x ^ 2) := by
    simpa [Function.comp_def] using hcψ.comp_left (g := fun z : ℝ => z^2) (by simp)
  have hdiffψ : ∀ x, DifferentiableAt ℝ ψ x := hψ.differentiable (by norm_num)
  have hdψ2 (x : E) : D (fun y => ψ y ^ 2) v x = 2 * ψ x * D ψ v x := by
    simp [D, fderiv_fun_pow 2 (hdiffψ x), ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hA : Integrable (fun x => D (D H v) v x * ψ x ^ 2) μ :=
    integrable_product_compact μ _ _ hcDDH (hψ.continuous.pow 2) hcψ2
  have hB : Integrable (fun x => D H v x * D (fun y => ψ y ^ 2) v x) μ := by
    apply integrable_product_compact μ _ _ hcDH
    · exact continuous_D (hψ.pow 2) v
    · exact compact_D hcψ2 v
  have hC : Integrable (fun x => D H v x * ψ x ^ 2) μ :=
    integrable_product_compact μ _ _ hcDH (hψ.continuous.pow 2) hcψ2
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := μ) (f := D H v) (g := fun y => ψ y ^ 2) (v := v)
    hA hB hC (fun x _ => hDH.differentiable (by norm_num) x)
    (fun x _ => (hψ.pow 2).differentiable (by norm_num) x)
  change (∫ x, D H v x * D (fun y => ψ y ^ 2) v x ∂μ) =
    -(∫ x, D (D H v) v x * ψ x ^ 2 ∂μ) at h
  simp_rw [hdψ2] at h
  have heq : (∫ x, D H v x * (2 * ψ x * D ψ v x) ∂μ) =
      2 * (∫ x, D H v x * ψ x * D ψ v x ∂μ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by ring)
  rw [heq] at h
  linarith

private noncomputable def groundState (H f : E → ℝ) (x : E) : ℝ :=
  Real.exp (-H x / 2) * f x

private theorem groundState_contDiff (H f : E → ℝ) (hH : ContDiff ℝ 2 H)
    (hf : ContDiff ℝ 1 f) : ContDiff ℝ 1 (groundState H f) := by
  have hH1 : ContDiff ℝ 1 H := hH.of_le (by norm_num)
  exact (hH1.neg.div_const 2).exp.mul hf

private theorem groundState_compact (H f : E → ℝ) (hcf : HasCompactSupport f) :
    HasCompactSupport (groundState H f) := by
  exact hcf.mul_left

private theorem groundState_D (H f : E → ℝ) (hH : ContDiff ℝ 2 H)
    (hf : ContDiff ℝ 1 f) (v x : E) :
    D (groundState H f) v x =
      Real.exp (-H x / 2) * (D f v x - (D H v x / 2) * f x) := by
  have hdH := (hH.differentiable (by norm_num) x).hasFDerivAt
  have hdf := (hf.differentiable (by norm_num) x).hasFDerivAt
  have h := ((hdH.const_mul (-1/2)).exp.mul hdf).fderiv
  have hh : (fun y => Real.exp ((-1/2) * H y) * f y) = groundState H f := by
    funext y
    dsimp [groundState]
    congr 2
    ring
  change fderiv ℝ (fun y => Real.exp ((-1/2) * H y) * f y) x = _ at h
  rw [hh] at h
  have heval := congrArg (fun L : E →L[ℝ] ℝ => L v) h
  have harg : (-1/2 : ℝ) * H x = -H x / 2 := by ring
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, harg] at heval
  dsimp [D]
  rw [heval]
  ring

private theorem groundState_energy_pointwise (H f : E → ℝ) (hH : ContDiff ℝ 2 H)
    (hf : ContDiff ℝ 1 f) (v x : E) :
    (D f v x)^2 * Real.exp (-H x) =
      (D (groundState H f) v x + (D H v x / 2) * groundState H f x)^2 := by
  have he : (Real.exp (-H x / 2))^2 = Real.exp (-H x) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hd : D (groundState H f) v x + (D H v x / 2) * groundState H f x =
      Real.exp (-H x / 2) * D f v x := by
    rw [groundState_D H f hH hf v x]
    dsimp [groundState]
    ring
  rw [hd, mul_pow, he]
  ring

/-- Genuine compact-test ground-state identity in a direction, on any finite
dimensional real Euclidean Haar measure. Integrability and IBP are discharged
from C² Hamiltonian, C¹ test and compact support, with no assumed identity. -/
private theorem compact_groundState_directional (H f : E → ℝ) (hH : ContDiff ℝ 2 H)
    (hf : ContDiff ℝ 1 f) (hcf : HasCompactSupport f) (v : E) :
    (∫ x, (D f v x)^2 * Real.exp (-H x) ∂μ) =
      (∫ x, (D (groundState H f) v x)^2 ∂μ) +
      ∫ x, ((D H v x)^2 / 4 - D (D H v) v x / 2) *
        (groundState H f x)^2 ∂μ := by
  let ψ := groundState H f
  have hψ : ContDiff ℝ 1 ψ := groundState_contDiff H f hH hf
  have hcψ : HasCompactSupport ψ := groundState_compact H f hcf
  have hDH := contDiff_D hH v
  have hcDH := continuous_D (hH.of_le (by norm_num)) v
  have hcDDH := continuous_D hDH v
  have hcDψ := continuous_D hψ v
  have hcψ2 : HasCompactSupport (fun x => ψ x^2) := by
    simpa [Function.comp_def] using hcψ.comp_left (g := fun z : ℝ => z^2) (by simp)
  have hcDψ2 : HasCompactSupport (fun x => (D ψ v x)^2) := by
    simpa [Function.comp_def] using (compact_D hcψ v).comp_left
      (g := fun z : ℝ => z^2) (by simp)
  have hiA : Integrable (fun x => (D ψ v x)^2) μ :=
    (hcDψ.pow 2).integrable_of_hasCompactSupport hcDψ2
  have hiB : Integrable (fun x => (D H v x)^2 / 4 * ψ x^2) μ :=
    integrable_product_compact μ _ _ ((hcDH.pow 2).div_const 4)
      (hψ.continuous.pow 2) hcψ2
  have hiD : Integrable (fun x => D (D H v) v x * ψ x^2) μ :=
    integrable_product_compact μ _ _ hcDDH (hψ.continuous.pow 2) hcψ2
  have hiC : Integrable (fun x => D H v x * ψ x * D ψ v x) μ := by
    have hi := integrable_product_compact μ (fun x => D H v x * D ψ v x) ψ
      (hcDH.mul hcDψ) hψ.continuous hcψ
    convert hi using 1
    funext x
    ring
  have hcross := compact_cross_ibp μ H ψ hH hψ hcψ v
  have hL : (∫ x, (D f v x)^2 * Real.exp (-H x) ∂μ) =
      (∫ x, (D ψ v x)^2 ∂μ) + (∫ x, (D H v x)^2 / 4 * ψ x^2 ∂μ) +
      (∫ x, D H v x * ψ x * D ψ v x ∂μ) := by
    calc
      _ = ∫ x, ((D ψ v x)^2 + (D H v x)^2 / 4 * ψ x^2) +
          D H v x * ψ x * D ψ v x ∂μ := by
        apply integral_congr_ae
        refine Filter.Eventually.of_forall (fun x => ?_)
        change (D f v x)^2 * Real.exp (-H x) = _
        rw [groundState_energy_pointwise H f hH hf v x]
        change (D ψ v x + D H v x / 2 * ψ x)^2 = _
        ring
      _ = _ := by
        rw [integral_add (f := fun x => (D ψ v x)^2 + (D H v x)^2 / 4 * ψ x^2)
          (g := fun x => D H v x * ψ x * D ψ v x) (hiA.add hiB) hiC,
          integral_add (f := fun x => (D ψ v x)^2)
            (g := fun x => (D H v x)^2 / 4 * ψ x^2) hiA hiB]
  have hP : (∫ x, ((D H v x)^2 / 4 - D (D H v) v x / 2) * ψ x^2 ∂μ) =
      (∫ x, (D H v x)^2 / 4 * ψ x^2 ∂μ) -
      (1/2 : ℝ) * (∫ x, D (D H v) v x * ψ x^2 ∂μ) := by
    calc
      _ = ∫ x, ((D H v x)^2 / 4 * ψ x^2) -
          (1/2 : ℝ) * (D (D H v) v x * ψ x^2) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by ring)
      _ = _ := by rw [integral_sub hiB (hiD.const_mul _), integral_const_mul]
  change (∫ x, (D f v x)^2 * Real.exp (-H x) ∂μ) =
    (∫ x, (D ψ v x)^2 ∂μ) +
      ∫ x, ((D H v x)^2 / 4 - D (D H v) v x / 2) * ψ x^2 ∂μ
  rw [hL, hP, hcross]
  ring

private theorem compact_directional_energy_integrable (H f : E → ℝ)
    (hH : ContDiff ℝ 2 H) (hf : ContDiff ℝ 1 f) (hcf : HasCompactSupport f) (v : E) :
    Integrable (fun x => (D f v x)^2 * Real.exp (-H x)) μ := by
  have hc : HasCompactSupport (fun x => (D f v x)^2) := by
    simpa [Function.comp_def] using (compact_D hcf v).comp_left
      (g := fun z : ℝ => z^2) (by simp)
  exact (((continuous_D hf v).pow 2).mul (Real.continuous_exp.comp hH.continuous.neg)).integrable_of_hasCompactSupport
    hc.mul_right

private theorem compact_directional_potential_integrable (H ψ : E → ℝ)
    (hH : ContDiff ℝ 2 H) (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) (v : E) :
    Integrable (fun x => ((D H v x)^2 / 4 - D (D H v) v x / 2) * ψ x^2) μ := by
  have hc : HasCompactSupport (fun x => ψ x^2) := by
    simpa [Function.comp_def] using hcψ.comp_left (g := fun z : ℝ => z^2) (by simp)
  exact integrable_product_compact μ _ _
    (((continuous_D (hH.of_le (by norm_num)) v).pow 2).div_const 4 |>.sub
      ((continuous_D (contDiff_D hH v) v).div_const 2)) (hψ.continuous.pow 2) hc

section InnerProduct

variable [CompleteSpace E]
  {ι : Type*} [Fintype ι]

private theorem sum_D_sq_eq_gradient_norm (b : OrthonormalBasis ι ℝ E) (u : E → ℝ) (x : E) :
    ∑ i, (D u (b i) x)^2 = ‖gradient u x‖^2 := by
  have hi (i : ι) : D u (b i) x = inner ℝ (gradient u x) (b i) := by
    dsimp [D]
    have h := congrArg (fun L : E →L[ℝ] ℝ => L (b i))
      (toDual_gradient (𝕜 := ℝ) (f := u) (x := x))
    simpa [InnerProductSpace.toDual_apply_apply] using h.symm
  calc
    _ = ∑ i, ‖inner ℝ (gradient u x) (b i)‖^2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hi, Real.norm_eq_abs, sq_abs]
    _ = _ := b.sum_sq_norm_inner_left (gradient u x)

private noncomputable def basisLaplacian (b : OrthonormalBasis ι ℝ E) (H : E → ℝ) (x : E) : ℝ :=
  ∑ i, D (D H (b i)) (b i) x

/-- Full ordinary-gradient ground-state identity, with the actual Fréchet
gradient and Hessian trace over an orthonormal basis. -/
private theorem compact_groundState_full (b : OrthonormalBasis ι ℝ E) (H f : E → ℝ)
    (hH : ContDiff ℝ 2 H) (hf : ContDiff ℝ 1 f) (hcf : HasCompactSupport f) :
    (∫ x, ‖gradient f x‖^2 * Real.exp (-H x) ∂μ) =
      (∫ x, ‖gradient (groundState H f) x‖^2 ∂μ) +
      ∫ x, (‖gradient H x‖^2 / 4 - basisLaplacian b H x / 2) *
        (groundState H f x)^2 ∂μ := by
  let ψ := groundState H f
  have hψ : ContDiff ℝ 1 ψ := groundState_contDiff H f hH hf
  have hcψ : HasCompactSupport ψ := groundState_compact H f hcf
  have hiL (i : ι) := compact_directional_energy_integrable μ H f hH hf hcf (b i)
  have hiA (i : ι) : Integrable (fun x => (D ψ (b i) x)^2) μ := by
    have hc : HasCompactSupport (fun x => (D ψ (b i) x)^2) := by
      simpa [Function.comp_def] using (compact_D hcψ (b i)).comp_left
        (g := fun z : ℝ => z^2) (by simp)
    exact ((continuous_D hψ (b i)).pow 2).integrable_of_hasCompactSupport hc
  have hiP (i : ι) := compact_directional_potential_integrable μ H ψ hH hψ hcψ (b i)
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => compact_groundState_directional μ H f hH hf hcf (b i))
  rw [Finset.sum_add_distrib] at hsum
  rw [← integral_finsetSum Finset.univ (fun i _ => hiL i),
      ← integral_finsetSum Finset.univ (fun i _ => hiA i),
      ← integral_finsetSum Finset.univ (fun i _ => hiP i)] at hsum
  have hleft : (fun x => ∑ i, (D f (b i) x)^2 * Real.exp (-H x)) =
      (fun x => ‖gradient f x‖^2 * Real.exp (-H x)) := by
    funext x
    rw [← Finset.sum_mul, sum_D_sq_eq_gradient_norm]
  have hA : (fun x => ∑ i, (D ψ (b i) x)^2) = (fun x => ‖gradient ψ x‖^2) := by
    funext x
    exact sum_D_sq_eq_gradient_norm b ψ x
  have hP : (fun x => ∑ i, ((D H (b i) x)^2 / 4 - D (D H (b i)) (b i) x / 2) * ψ x^2) =
      (fun x => (‖gradient H x‖^2 / 4 - basisLaplacian b H x / 2) * ψ x^2) := by
    funext x
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div,
      sum_D_sq_eq_gradient_norm]
    rfl
  rw [hleft, hA, hP] at hsum
  exact hsum

end InnerProduct

end EuclideanGroundState

-- [TABLET NODE: EuclideanGroundState]
theorem EuclideanGroundState {ι : Type*} [Fintype ι]
    (H f : EuclideanSpace ℝ ι → ℝ) (hH : ContDiff ℝ 2 H)
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    let ψ := fun x => f x * Real.exp (-H x / 2)
    (∫ x, ‖EuclideanGradient f x‖^2 * Real.exp (-H x)) =
      (∫ x, ‖EuclideanGradient ψ x‖^2) +
      ∫ x, (‖EuclideanGradient H x‖^2 / 4 - EuclideanLaplacian H x / 2) * (ψ x)^2 := by
-- BODY
  have hL (x : EuclideanSpace ℝ ι) :
      EuclideanGroundState.basisLaplacian (EuclideanSpace.basisFun ι ℝ) H x =
        EuclideanLaplacian H x := by
    rw [(EuclideanDerivativeCoordinates H x).2]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [EuclideanGroundState.D, EuclideanHessian]
    change (fderiv ℝ (fun z => fderiv ℝ H z ((EuclideanSpace.basisFun ι ℝ) k)) x)
      ((EuclideanSpace.basisFun ι ℝ) k) = _
    have hH' : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) H := by convert hH using 1 <;> norm_num
    have hfd := (contDiff_succ_iff_fderiv.mp hH').2.2
    rw [fderiv_clm_apply ((hfd.differentiable (by norm_num)) x) (differentiableAt_const _)]
    simp
  have he := EuclideanGroundState.compact_groundState_full volume
    (EuclideanSpace.basisFun ι ℝ) H f hH hf hc
  have heq : EuclideanGroundState.groundState H f = fun x => f x * Real.exp (-H x / 2) := by
    funext x
    exact mul_comm _ _
  rw [heq] at he
  simpa only [hL, EuclideanGradient] using he
