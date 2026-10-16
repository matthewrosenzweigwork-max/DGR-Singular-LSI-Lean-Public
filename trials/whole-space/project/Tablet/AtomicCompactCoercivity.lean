import Tablet.AtomicForceForm
import Tablet.EuclideanGroundState
import Tablet.UniformTraceAbsorption
import Mathlib.Tactic
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace AtomicCompactCoercivity
private noncomputable def atomicU {d : ℕ} {ι : Type*} (J : Finset ι)
    (charges : ι → ℝ) (y : ι → OneParticle d) (s ε : ℝ) :=
  fun x => ∑ j ∈ J, charges j * RieszKernel s ε (x - y j)
private noncomputable def groundState {d : ℕ} (H f : OneParticle d → ℝ) :=
  fun x => f x * Real.exp (-H x / 2)
private theorem atomicU_contDiff {d : ℕ} {ι : Type*} (J : Finset ι)
    (charges : ι → ℝ) (y : ι → OneParticle d) (s ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ 2 (atomicU J charges y s ε) := by
  apply ContDiff.sum
  intro j hj
  have hk : ContDiff ℝ 2 (RieszKernel (d := d) s ε) := by
    unfold RieszKernel
    simp only [if_neg (ne_of_gt hε)]
    exact (((contDiff_norm_sq ℝ).add contDiff_const).rpow_const_of_ne
      (fun z => (show 0 < ‖z‖^2 + ε^2 by positivity).ne')).div_const s
  exact contDiff_const.mul (hk.comp (contDiff_id.sub contDiff_const))
private theorem groundState_contDiff {d : ℕ} (H f : OneParticle d → ℝ)
    (hH : ContDiff ℝ 2 H) (hf : ContDiff ℝ 1 f) : ContDiff ℝ 1 (groundState H f) := by
  exact hf.mul (((hH.of_le (by norm_num)).neg.div_const 2).exp)
private theorem groundState_compact {d : ℕ} (H f : OneParticle d → ℝ)
    (hc : HasCompactSupport f) : HasCompactSupport (groundState H f) := hc.mul_right
private theorem continuous_gradient {d : ℕ} (u : OneParticle d → ℝ) (hu : ContDiff ℝ 1 u) :
    Continuous (EuclideanGradient u) :=
  (InnerProductSpace.toDual ℝ (OneParticle d)).symm.continuous.comp (hu.continuous_fderiv (by norm_num))
private theorem gradient_add_actual {d : ℕ} (u v : OneParticle d → ℝ)
    (hu : Differentiable ℝ u) (hv : Differentiable ℝ v) (x : OneParticle d) :
    EuclideanGradient (fun z => u z + v z) x = EuclideanGradient u x + EuclideanGradient v x := by
  apply (InnerProductSpace.toDual ℝ (OneParticle d)).injective
  rw [map_add, EuclideanGradient, EuclideanGradient, EuclideanGradient,
    toDual_gradient, toDual_gradient, toDual_gradient, fderiv_fun_add (hu x) (hv x)]
private theorem continuous_laplacian {d : ℕ} (u : OneParticle d → ℝ) (hu : ContDiff ℝ 2 u) :
    Continuous (EuclideanLaplacian u) := by
  have hfd : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hffd := hfd.continuous_fderiv (by norm_num)
  have he : EuclideanLaplacian u = fun x => ∑ k,
      EuclideanHessian u x (EuclideanSpace.basisFun (Fin d) ℝ k)
        (EuclideanSpace.basisFun (Fin d) ℝ k) :=
    funext (fun x => (EuclideanDerivativeCoordinates u x).2)
  rw [he]
  unfold EuclideanHessian
  fun_prop
private theorem laplacian_add_actual {d : ℕ} (u v : OneParticle d → ℝ)
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (x : OneParticle d) :
    EuclideanLaplacian (fun z => u z + v z) x = EuclideanLaplacian u x + EuclideanLaplacian v x := by
  exact hu.contDiffAt.laplacian_add hv.contDiffAt
private theorem compact_weight_integrable {d : ℕ} (a ψ : OneParticle d → ℝ)
    (ha : Continuous a) (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) :
    Integrable (fun x => a x * ψ x^2) (volume : Measure (OneParticle d)) := by
  have hc : HasCompactSupport (fun x => ψ x^2) := hcψ.comp_left (g := fun z : ℝ => z^2) (by simp)
  exact (ha.mul (hψ.continuous.pow 2)).integrable_of_hasCompactSupport hc.mul_left
private theorem compact_gradient_energy_integrable {d : ℕ} (ψ : OneParticle d → ℝ)
    (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) :
    Integrable (fun x => ‖EuclideanGradient ψ x‖^2) (volume : Measure (OneParticle d)) := by
  have hc : HasCompactSupport (fun x => ‖fderiv ℝ ψ x‖^2) :=
    (hcψ.fderiv ℝ).comp_left (g := fun L : OneParticle d →L[ℝ] ℝ => ‖L‖^2) (by simp)
  have hi := ((hψ.continuous_fderiv (by norm_num)).norm.pow 2).integrable_of_hasCompactSupport
    (μ := (volume : Measure (OneParticle d))) hc
  have hi' : Integrable (fun x => ‖fderiv ℝ ψ x‖^2) (volume : Measure (OneParticle d)) :=
    hi.congr (Eventually.of_forall (fun _ => rfl))
  exact hi'.congr (Eventually.of_forall (fun x => by dsimp only; rw [(GradientNormIdentity ψ x).2]))

end AtomicCompactCoercivity
open AtomicCompactCoercivity
-- [TABLET NODE: AtomicCompactCoercivity]
theorem AtomicCompactCoercivity (d : ℕ) (hd : 3 ≤ d) (s A : ℝ)
    (hs : 0 < s) (hsd : s ≤ (d : ℝ) - 2) (hA0 : 0 ≤ A) (Ca : ℝ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ V : OneParticle d → ℝ, ContDiff ℝ 2 V →
      (∀ a : ℝ, 0 < a → ∀ x, EuclideanLaplacian V x ≤
        a * ‖EuclideanGradient V x‖ ^ (2 / (s + 1)) + Ca a) →
      ∀ {ι : Type*} (J : Finset ι) (charges : ι → ℝ) (y : ι → OneParticle d) (ε : ℝ),
      (∀ j ∈ J, 0 ≤ charges j) → (∑ j ∈ J, charges j ≤ A) → 0 < ε →
      ∀ f : OneParticle d → ℝ, ContDiff ℝ 1 f → HasCompactSupport f →
      let U := fun x => ∑ j ∈ J, charges j * RieszKernel s ε (x - y j)
      let ψ := fun x => f x * Real.exp (-(V x + U x) / 2)
      (∫ x, ‖EuclideanGradient ψ x‖ ^ 2) / 2 +
        (∫ x, ‖EuclideanGradient V x + EuclideanGradient U x‖ ^ 2 * ψ x ^ 2) / 8 +
        (∫ x, -EuclideanLaplacian U x * ψ x ^ 2) / 2 ≤
      (∫ x, ‖EuclideanGradient f x‖ ^ 2 * Real.exp (-(V x + U x))) + C * (∫ x, ψ x ^ 2) := by
-- BODY
  obtain ⟨K, hK⟩ := AtomicForceForm d hd s hs hsd
  let θ := 2 / (s + 1)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθ2 : θ < 2 := (ForceExponentRange s hs).2
  let H := (K : ℝ) * A ^ θ
  have hH : 0 ≤ H := mul_nonneg K.coe_nonneg (Real.rpow_nonneg hA0 _)
  let c := (2 : ℝ) ^ θ
  let a₀ := 1 / (4 * c * (1 + H))
  have ha₀ : 0 < a₀ := by dsimp [a₀, c]; positivity
  let C := max 0 ((Ca a₀ + a₀ * c) / 2)
  refine ⟨C, le_max_left _ _, ?_⟩
  intro V hV hgrowth ι J charges y ε ha hmass hε f hf hcf
  let U := atomicU J charges y s ε
  let Htot := fun x => V x + U x
  let ψ := groundState Htot f
  have hU : ContDiff ℝ 2 U := atomicU_contDiff J charges y s ε hε
  have hHtot : ContDiff ℝ 2 Htot := hV.add hU
  have hψ : ContDiff ℝ 1 ψ := groundState_contDiff Htot f hHtot hf
  have hcψ : HasCompactSupport ψ := groundState_compact Htot f hcf
  have hV1 : ContDiff ℝ 1 V := hV.of_le (by norm_num)
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by norm_num)
  have himass : Integrable (fun x => ψ x ^ 2) := by
    simpa only [one_mul] using compact_weight_integrable (fun _ => 1) ψ continuous_const hψ hcψ
  have hiG := compact_gradient_energy_integrable ψ hψ hcψ
  have hiT := compact_weight_integrable (fun x => ‖EuclideanGradient V x + EuclideanGradient U x‖ ^ 2) ψ
    (((continuous_gradient V hV1).add (continuous_gradient U hU1)).norm.pow 2) hψ hcψ
  have hiF : Integrable (fun x => ‖EuclideanGradient U x‖ ^ θ * ψ x ^ 2) := by
    simpa only [Function.comp_def] using compact_weight_integrable _ ψ
      ((Real.continuous_rpow_const hθ.le).comp (continuous_gradient U hU1).norm) hψ hcψ
  have hiQ := compact_weight_integrable _ ψ (continuous_laplacian V hV) hψ hcψ
  have hiS : Integrable (fun x => -EuclideanLaplacian U x * ψ x ^ 2) := by
    simpa only [Pi.neg_apply] using compact_weight_integrable _ ψ (continuous_laplacian U hU).neg hψ hcψ
  have hform : (∫ x, ‖EuclideanGradient U x‖ ^ θ * ψ x ^ 2) ≤ H * (∫ x, ‖EuclideanGradient ψ x‖ ^ 2) :=
    (hK J charges y ε A ha hmass hA0 hε ψ hψ hcψ).2
  have hID := EuclideanGroundState Htot f hHtot hf hcf
  have hpot : (fun x => (‖EuclideanGradient Htot x‖ ^ 2 / 4 -
      EuclideanLaplacian Htot x / 2) * ψ x ^ 2) =
      (fun x => 1 / 4 * (‖EuclideanGradient V x + EuclideanGradient U x‖ ^ 2 * ψ x ^ 2) -
        1 / 2 * (EuclideanLaplacian V x * ψ x ^ 2) +
        1 / 2 * (-EuclideanLaplacian U x * ψ x ^ 2)) := by
    funext x
    rw [gradient_add_actual V U (hV.differentiable (by norm_num)) (hU.differentiable (by norm_num)),
      laplacian_add_actual V U hV hU]
    ring
  change (∫ x, ‖EuclideanGradient f x‖ ^ 2 * Real.exp (-Htot x)) =
    (∫ x, ‖EuclideanGradient ψ x‖ ^ 2) + ∫ x,
      (‖EuclideanGradient Htot x‖ ^ 2 / 4 - EuclideanLaplacian Htot x / 2) * ψ x ^ 2 at hID
  have hisub : Integrable (fun x => 1 / 4 * (‖EuclideanGradient V x + EuclideanGradient U x‖ ^ 2 * ψ x ^ 2) -
      1 / 2 * (EuclideanLaplacian V x * ψ x ^ 2)) :=
    ((hiT.const_mul (1 / 4)).sub (hiQ.const_mul (1 / 2))).congr (Eventually.of_forall (fun _ => rfl))
  rw [hpot, integral_add hisub (hiS.const_mul (1 / 2)),
    integral_sub (hiT.const_mul (1 / 4)) (hiQ.const_mul (1 / 2)), integral_const_mul,
    integral_const_mul, integral_const_mul] at hID
  have hground : (∫ x, ‖EuclideanGradient ψ x‖ ^ 2) +
      (∫ x, ‖EuclideanGradient V x + EuclideanGradient U x‖ ^ 2 * ψ x ^ 2) / 4 +
      (∫ x, -EuclideanLaplacian U x * ψ x ^ 2) / 2 =
      (∫ x, ‖EuclideanGradient f x‖ ^ 2 * Real.exp (-Htot x)) +
      (∫ x, EuclideanLaplacian V x * ψ x ^ 2) / 2 := by linarith
  have Habs := UniformTraceAbsorption volume ψ
    (EuclideanLaplacian V) (EuclideanGradient V) (EuclideanGradient U)
    θ H (∫ x, ‖EuclideanGradient ψ x‖ ^ 2)
    (∫ x, -EuclideanLaplacian U x * ψ x ^ 2)
    (∫ x, ‖EuclideanGradient f x‖ ^ 2 * Real.exp (-Htot x)) (Ca a₀)
    hθ hθ2 hH (integral_nonneg (fun x => sq_nonneg _)) himass hiQ hiT hiF hform hground
    (hgrowth a₀ ha₀)
  have hMC : ((Ca a₀ + a₀ * c) / 2) * (∫ x, ψ x ^ 2) ≤ C * (∫ x, ψ x ^ 2) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (integral_nonneg (fun x => sq_nonneg _))
  exact Habs.trans (add_le_add_right hMC _)
