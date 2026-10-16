module

public import Tablet.AtomicCompactCoercivity
public import Tablet.AtomicInteractionSource
public import Tablet.WeightedSpatialApproximation
public import Tablet.ConvexReferenceNormalization
public import Mathlib.Tactic

@[expose] public section
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace AtomicSquaredTestTail
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
private theorem squared_test_tail_pointwise {d : ℕ} (v F : OneParticle d → OneParticle d) (ψ : OneParticle d → ℝ)
    (κ θ R : ℝ) (hκ : 0 < κ) (hθ : 0 < θ) (hR : 0 < R)
    (hdrift : ∀ x, κ * ‖x‖ ≤ ‖v x‖) (x : OneParticle d) :
    ({x : OneParticle d | R < ‖x‖}).indicator (fun x => ψ x ^ 2) x ≤
      (4 / (κ ^ 2 * R ^ 2) * ‖v x + F x‖ ^ 2 +
        (2 / (κ * R)) ^ θ * ‖F x‖ ^ θ) * ψ x ^ 2 := by
  have hden : 0 < κ ^ 2 * R ^ 2 := by positivity
  have hc0 : 0 ≤ 4 / (κ ^ 2 * R ^ 2) := by positivity
  have hf0 : 0 ≤ (2 / (κ * R)) ^ θ * ‖F x‖ ^ θ := by positivity
  by_cases hx : R < ‖x‖
  · simp only [Set.indicator, Set.mem_setOf_eq, if_pos hx]
    have htriangle : ‖v x‖ ≤ ‖v x + F x‖ + ‖F x‖ := by
      calc
        ‖v x‖ = ‖(v x + F x) - F x‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    by_cases hF : ‖F x‖ ≤ κ * R / 2
    · have htotal : κ * R / 2 ≤ ‖v x + F x‖ := by
        have hh := mul_lt_mul_of_pos_left hx hκ
        linarith [hdrift x]
      have hs : κ ^ 2 * R ^ 2 / 4 ≤ ‖v x + F x‖ ^ 2 := by
        have hh := pow_le_pow_left₀ (by positivity : 0 ≤ κ * R / 2) htotal 2
        nlinarith [hh]
      have hc : 1 ≤ 4 / (κ ^ 2 * R ^ 2) * ‖v x + F x‖ ^ 2 := by
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hden).2
        nlinarith [hs]
      have hcoef : 1 ≤ 4 / (κ ^ 2 * R ^ 2) * ‖v x + F x‖ ^ 2 + (2 / (κ * R)) ^ θ * ‖F x‖ ^ θ := by linarith
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoef (sq_nonneg (ψ x))
    · have hF' : κ * R / 2 ≤ ‖F x‖ := (lt_of_not_ge hF).le
      have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ κ * R / 2) hF' hθ.le
      have hid : (2 / (κ * R)) ^ θ * (κ * R / 2) ^ θ = 1 := by
        rw [← Real.mul_rpow (by positivity) (by positivity)]
        have hh : 2 / (κ * R) * (κ * R / 2) = 1 := by field_simp
        rw [hh, Real.one_rpow]
      have hc : 1 ≤ (2 / (κ * R)) ^ θ * ‖F x‖ ^ θ := by
        rw [← hid]
        exact mul_le_mul_of_nonneg_left hpow (by positivity)
      have hαT := mul_nonneg hc0 (sq_nonneg ‖v x + F x‖)
      have hcoef : 1 ≤ 4 / (κ ^ 2 * R ^ 2) * ‖v x + F x‖ ^ 2 + (2 / (κ * R)) ^ θ * ‖F x‖ ^ θ := by linarith
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoef (sq_nonneg (ψ x))
  · simp only [Set.indicator, Set.mem_setOf_eq, if_neg hx]
    positivity

-- This is a tail of the arbitrary squared test, not tightness of the law alone.
private theorem squared_test_tail_integral {d : ℕ} (v F : OneParticle d → OneParticle d) (ψ : OneParticle d → ℝ)
    (κ θ R : ℝ) (hκ : 0 < κ) (hθ : 0 < θ) (hR : 0 < R)
    (hdrift : ∀ x, κ * ‖x‖ ≤ ‖v x‖)
    (hmass : Integrable (fun x => ψ x ^ 2))
    (htotal : Integrable (fun x => ‖v x + F x‖ ^ 2 * ψ x ^ 2))
    (hforce : Integrable (fun x => ‖F x‖ ^ θ * ψ x ^ 2)) :
    (∫ x in {x : OneParticle d | R < ‖x‖}, ψ x ^ 2) ≤
      4 / (κ ^ 2 * R ^ 2) * (∫ x, ‖v x + F x‖ ^ 2 * ψ x ^ 2) +
        (2 / (κ * R)) ^ θ * (∫ x, ‖F x‖ ^ θ * ψ x ^ 2) := by
  have hset : MeasurableSet {x : OneParticle d | R < ‖x‖} := measurableSet_lt measurable_const continuous_norm.measurable
  have H := integral_mono (hmass.indicator hset)
    ((htotal.const_mul (4 / (κ ^ 2 * R ^ 2))).add (hforce.const_mul ((2 / (κ * R)) ^ θ)))
    (fun x => by simpa only [Pi.add_apply, add_mul, mul_assoc] using
      squared_test_tail_pointwise v F ψ κ θ R hκ hθ hR hdrift x)
  simp only [Pi.add_apply] at H
  rw [integral_indicator hset, integral_add (htotal.const_mul _) (hforce.const_mul _),
    integral_const_mul, integral_const_mul] at H
  exact H





private theorem squared_test_coercive_tail {d : ℕ} (v F : OneParticle d → OneParticle d) (ψ : OneParticle d → ℝ)
    (κ θ R G S B H : ℝ) (hκ : 0 < κ) (hθ : 0 < θ) (hR : 0 < R)
    (hdrift : ∀ x, κ * ‖x‖ ≤ ‖v x‖)
    (hmass : Integrable (fun x => ψ x ^ 2))
    (htotal : Integrable (fun x => ‖v x + F x‖ ^ 2 * ψ x ^ 2))
    (hforce : Integrable (fun x => ‖F x‖ ^ θ * ψ x ^ 2))
    (hG : 0 ≤ G) (hS : 0 ≤ S) (hH : 0 ≤ H)
    (hform : (∫ x, ‖F x‖ ^ θ * ψ x ^ 2) ≤ H * G)
    (hcoercive : G / 2 + (∫ x, ‖v x + F x‖ ^ 2 * ψ x ^ 2) / 8 + S / 2 ≤ B) :
    (∫ x in {x : OneParticle d | R < ‖x‖}, ψ x ^ 2) ≤
      (32 / κ ^ 2 * R ^ (-2 : ℝ) + 2 * H * (2 / κ) ^ θ * R ^ (-θ)) * B := by
  have hT : 0 ≤ (∫ x, ‖v x + F x‖ ^ 2 * ψ x ^ 2) := integral_nonneg (fun x => by positivity)
  have hGbound : G ≤ 2 * B := by linarith
  have hTbound : (∫ x, ‖v x + F x‖ ^ 2 * ψ x ^ 2) ≤ 8 * B := by linarith
  have Htail := squared_test_tail_integral v F ψ κ θ R hκ hθ hR hdrift hmass htotal hforce
  have hFbound : (∫ x, ‖F x‖ ^ θ * ψ x ^ 2) ≤ H * (2 * B) :=
    hform.trans (mul_le_mul_of_nonneg_left hGbound hH)
  have hα : 0 ≤ 4 / (κ ^ 2 * R ^ 2) := by positivity
  have hβ : 0 ≤ (2 / (κ * R)) ^ θ := by positivity
  have hscaledT := mul_le_mul_of_nonneg_left hTbound hα
  have hscaledF := mul_le_mul_of_nonneg_left hFbound hβ
  have hR2 : R ^ (-2 : ℝ) = (R ^ (2 : ℕ))⁻¹ := by
    rw [Real.rpow_neg hR.le]
    congr 1
    simpa only [Nat.cast_ofNat] using Real.rpow_natCast R 2
  have hRθ : (2 / (κ * R)) ^ θ = (2 / κ) ^ θ * R ^ (-θ) := by
    have hbase : 2 / (κ * R) = (2 / κ) * R⁻¹ := by ring
    rw [hbase, Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_neg_one R, ← Real.rpow_mul hR.le]
    congr 1
    ring
  have hid : 4 / (κ ^ 2 * R ^ 2) * (8 * B) + (2 / (κ * R)) ^ θ * (H * (2 * B)) =
      (32 / κ ^ 2 * R ^ (-2 : ℝ) + 2 * H * (2 / κ) ^ θ * R ^ (-θ)) * B := by
    rw [hR2, hRθ]
    ring
  exact Htail.trans ((add_le_add hscaledT hscaledF).trans_eq hid)

private theorem groundState_square {d : ℕ} (H f : OneParticle d → ℝ) (x : OneParticle d) :
    (groundState H f x) ^ 2 = f x ^ 2 * Real.exp (-H x) := by
  have he : (Real.exp (-H x / 2)) ^ 2 = Real.exp (-H x) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [groundState, mul_pow, he, mul_comm]

-- Actual Hessian lower bound and normalized minimizer discharge the spatial drift.
-- This bounds every weighted squared test, with one constant chosen before all V/atoms/eps/tests/R.
private theorem uniform_atomic_compact_squared_tail (d : ℕ) (hd : 3 ≤ d) (s A κ : ℝ)
    (hs : 0 < s) (hsd : s ≤ (d : ℝ) - 2) (hA0 : 0 ≤ A) (hκ : 0 < κ) (Ca : ℝ → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ V : OneParticle d → ℝ, ContDiff ℝ 2 V →
      (∀ x v, κ * ‖v‖ ^ 2 ≤ EuclideanHessian V x v v) →
      (∀ x, V 0 ≤ V x) →
      (∀ a : ℝ, 0 < a → ∀ x, EuclideanLaplacian V x ≤
        a * ‖EuclideanGradient V x‖ ^ (2 / (s + 1)) + Ca a) →
      ∀ {ι : Type*} (J : Finset ι) (charges : ι → ℝ) (y : ι → OneParticle d) (ε : ℝ),
      (∀ j ∈ J, 0 ≤ charges j) → (∑ j ∈ J, charges j ≤ A) → 0 < ε →
      ∀ f : OneParticle d → ℝ, ContDiff ℝ 1 f → HasCompactSupport f → ∀ R : ℝ, 0 < R →
      let U := atomicU J charges y s ε
      (∫ x in {x : OneParticle d | R < ‖x‖}, f x ^ 2 * Real.exp (-(V x + U x))) ≤
        C * (R ^ (-2 : ℝ) + R ^ (-(2 / (s + 1)))) *
          ((∫ x, ‖EuclideanGradient f x‖ ^ 2 * Real.exp (-(V x + U x))) +
            ∫ x, f x ^ 2 * Real.exp (-(V x + U x))) := by
  obtain ⟨C₀, hC₀, hcoerce⟩ := AtomicCompactCoercivity d hd s A hs hsd hA0 Ca
  obtain ⟨K, hK⟩ := AtomicForceForm d hd s hs hsd
  let θ := 2 / (s + 1)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  let H := (K : ℝ) * A ^ θ
  have hH : 0 ≤ H := mul_nonneg K.coe_nonneg (Real.rpow_nonneg hA0 _)
  let P := max 1 C₀
  have hP : 0 < P := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  let L := 32 / κ ^ 2 + 2 * H * (2 / κ) ^ θ
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨L * P, mul_pos hL hP, ?_⟩
  intro V hV hHess hmin hgrowth ι J charges y ε ha hmass hε f hf hcf R hR
  let U := atomicU J charges y s ε
  let Htot := fun x => V x + U x
  let ψ := groundState Htot f
  let E := ∫ x, ‖EuclideanGradient f x‖ ^ 2 * Real.exp (-Htot x)
  let M := ∫ x, ψ x ^ 2
  let G := ∫ x, ‖EuclideanGradient ψ x‖ ^ 2
  let S := ∫ x, -EuclideanLaplacian U x * ψ x ^ 2
  have hU : ContDiff ℝ 2 U := atomicU_contDiff J charges y s ε hε
  have hψ : ContDiff ℝ 1 ψ := groundState_contDiff Htot f (hV.add hU) hf
  have hcψ : HasCompactSupport ψ := groundState_compact Htot f hcf
  have hV1 : ContDiff ℝ 1 V := hV.of_le (by norm_num)
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by norm_num)
  have himass : Integrable (fun x => ψ x ^ 2) := by
    simpa only [one_mul] using compact_weight_integrable (fun _ => 1) ψ continuous_const hψ hcψ
  have hiT := compact_weight_integrable (fun x => ‖EuclideanGradient V x + EuclideanGradient U x‖ ^ 2) ψ
    (((continuous_gradient V hV1).add (continuous_gradient U hU1)).norm.pow 2) hψ hcψ
  have hiF : Integrable (fun x => ‖EuclideanGradient U x‖ ^ θ * ψ x ^ 2) := by
    simpa only [Function.comp_def] using compact_weight_integrable _ ψ
      ((Real.continuous_rpow_const hθ.le).comp (continuous_gradient U hU1).norm) hψ hcψ
  have hG : 0 ≤ G := integral_nonneg (fun x => sq_nonneg _)
  have hS : 0 ≤ S := integral_nonneg (fun x =>
    mul_nonneg (((AtomicInteractionSource d s ε hs hsd hε J charges y ha).2 x).2) (sq_nonneg _))
  have hE : 0 ≤ E := integral_nonneg (fun x => by positivity)
  have hM : 0 ≤ M := integral_nonneg (fun x => sq_nonneg _)
  have hdrift : ∀ x : OneParticle d, κ * ‖x‖ ≤ ‖EuclideanGradient V x‖ := by
    obtain ⟨a, ha', huniq, _, _, hdr⟩ := (HessianMinimizer V κ hκ ⟨hV, hHess⟩).2
    have hz : (0 : OneParticle d) = a := huniq 0 hmin
    subst a
    simpa only [sub_zero] using hdr
  have hform : (∫ x, ‖EuclideanGradient U x‖ ^ θ * ψ x ^ 2) ≤ H * G :=
    (hK J charges y ε A ha hmass hA0 hε ψ hψ hcψ).2
  have hcoercive : G / 2 + (∫ x, ‖EuclideanGradient V x + EuclideanGradient U x‖ ^ 2 * ψ x ^ 2) / 8 + S / 2 ≤ E + C₀ * M :=
    hcoerce V hV hgrowth J charges y ε ha hmass hε f hf hcf
  have HT := squared_test_coercive_tail (EuclideanGradient V) (EuclideanGradient U) ψ κ θ R G S (E + C₀ * M) H
    hκ hθ hR hdrift himass hiT hiF hG hS hH hform hcoercive
  have hB : E + C₀ * M ≤ P * (E + M) := by
    have h1 := mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) C₀) hE
    have h2 := mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) C₀) hM
    dsimp [P]
    nlinarith
  have hB0 : 0 ≤ E + C₀ * M := by positivity
  have hr2 : 0 ≤ R ^ (-2 : ℝ) := Real.rpow_nonneg hR.le _
  have hrθ : 0 ≤ R ^ (-θ) := Real.rpow_nonneg hR.le _
  have hα : 0 ≤ 32 / κ ^ 2 := by positivity
  have hβ : 0 ≤ 2 * H * (2 / κ) ^ θ := by positivity
  have hRate : 32 / κ ^ 2 * R ^ (-2 : ℝ) + 2 * H * (2 / κ) ^ θ * R ^ (-θ) ≤
      L * (R ^ (-2 : ℝ) + R ^ (-θ)) := by
    dsimp [L]
    nlinarith [mul_nonneg hα hrθ, mul_nonneg hβ hr2]
  have Hfinal : (∫ x in {x : OneParticle d | R < ‖x‖}, ψ x ^ 2) ≤
      (L * P) * (R ^ (-2 : ℝ) + R ^ (-θ)) * (E + M) := by
    calc
      _ ≤ _ := HT
      _ ≤ (L * (R ^ (-2 : ℝ) + R ^ (-θ))) * (E + C₀ * M) :=
        mul_le_mul_of_nonneg_right hRate hB0
      _ ≤ (L * (R ^ (-2 : ℝ) + R ^ (-θ))) * (P * (E + M)) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
      _ = _ := by ring
  simpa only [ψ, E, M, Htot, U, θ, groundState_square] using Hfinal


private theorem weighted_integral {d : ℕ} (H : OneParticle d → ℝ) (hH : Continuous H)
    (g : OneParticle d → ℝ) (μ : Measure (OneParticle d)) :
    (∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal (Real.exp (-H x)))) =
      ∫ x, g x * Real.exp (-H x) ∂μ := by
  have hr : Measurable (fun x => ENNReal.ofReal (Real.exp (-H x))) := by
    exact (Real.measurable_exp.comp hH.measurable.neg).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hr
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    dsimp only
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, mul_comm])

end AtomicSquaredTestTail
open AtomicSquaredTestTail
-- [TABLET NODE: AtomicSquaredTestTail]
theorem AtomicSquaredTestTail (d : ℕ) (hd : 3 ≤ d) (s A κ : ℝ)
    (hs : 0 < s) (hsd : s ≤ (d : ℝ) - 2) (hA : 0 ≤ A) (hκ : 0 < κ) (Ca : ℝ → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ V : OneParticle d → ℝ, PotentialBounds d κ V →
      (∀ x, V 0 ≤ V x) →
      (∀ a : ℝ, 0 < a → ∀ x, EuclideanLaplacian V x ≤
        a * ‖EuclideanGradient V x‖ ^ (2 / (s + 1)) + Ca a) →
      ∀ {ι : Type*} (J : Finset ι) (charges : ι → ℝ) (y : ι → OneParticle d) (ε : ℝ),
      (∀ j ∈ J, 0 ≤ charges j) → (∑ j ∈ J, charges j ≤ A) → 0 < ε →
      ∀ (r : ℝ), 0 ≤ r → ∀ (f : OneParticle d → ℝ), ContDiff ℝ 1 f → ∀ c : ℝ,
      HasCompactSupport (fun x => f x - c) → ∀ R : ℝ, 0 < R →
      let U := fun x => ∑ j ∈ J, charges j * RieszKernel s ε (x - y j)
      (∫ x in {x : OneParticle d | R < ‖x‖}, r * (f x^2 * Real.exp (-(V x + U x)))) ≤
        C * (R ^ (-2 : ℝ) + R ^ (-(2 / (s + 1)))) *
          ((∫ x, r * (‖EuclideanGradient f x‖^2 * Real.exp (-(V x + U x)))) +
            ∫ x, r * (f x^2 * Real.exp (-(V x + U x)))) := by
-- BODY
  obtain ⟨C, hC, hcompact⟩ := uniform_atomic_compact_squared_tail d hd s A κ
    hs hsd hA hκ Ca
  refine ⟨C, hC, ?_⟩
  intro V hV hmin hgrowth ι J charges y ε ha hmass hε r hr f hf c hcf R hR
  let U := fun x => ∑ j ∈ J, charges j * RieszKernel s ε (x - y j)
  let H := fun x => V x + U x
  let P := volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-H x)))
  have hU : ContDiff ℝ 2 U := (AtomicInteractionSource d s ε hs hsd hε J charges y ha).1
  have hH : Continuous H := hV.regularity.continuous.add hU.continuous
  have hb : BoundedMultiplier d 1 (fun _ => 1) :=
    ⟨measurable_const, 1, 1, by norm_num, le_rfl, by norm_num, fun _ => ⟨le_rfl, le_rfl⟩⟩
  have hiV : Integrable (fun x => Real.exp (-V x)) := by
    simpa only [one_mul] using (ConvexReferenceNormalization V (fun _ => 1) κ 1 hκ hV hb).1
  have hUn : ∀ x, 0 ≤ U x := by
    intro x
    apply Finset.sum_nonneg
    intro j hj
    apply mul_nonneg (ha j hj)
    dsimp [RieszKernel]
    rw [if_neg (ne_of_gt hε)]
    positivity
  have hiH : Integrable (fun x => Real.exp (-H x)) :=
    hiV.mono' ((Real.continuous_exp.comp hH.neg).aestronglyMeasurable)
      (Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (by dsimp [H]; linarith [hUn x])))
  haveI : IsFiniteMeasure P := by
    apply isFiniteMeasure_withDensity
    rw [← ofReal_integral_eq_lintegral_ofReal hiH
      (Eventually.of_forall (fun x => (Real.exp_pos _).le))]
    exact ENNReal.ofReal_ne_top
  let T := {x : OneParticle d | R < ‖x‖}
  have hT : MeasurableSet T := measurableSet_lt measurable_const continuous_norm.measurable
  obtain ⟨fn, hreg, _, _, _, _, hmasslim, henergylim, htailall⟩ :=
    WeightedSpatialApproximation P f hf c hcf
  have htail := htailall T
  have hright := (henergylim.add hmasslim).const_mul (C * (R^(-2 : ℝ)+R^(-(2/(s+1)))))
  have hbound : ∀ n, (∫ x in T, fn n x^2 ∂P) ≤
      C * (R^(-2 : ℝ)+R^(-(2/(s+1)))) *
        ((∫ x, ‖EuclideanGradient (fn n) x‖^2 ∂P) + ∫ x, fn n x^2 ∂P) := by
    intro n
    have h := hcompact V hV.regularity hV.lower hmin hgrowth J charges y ε ha hmass hε
      (fn n) (hreg n).1 (hreg n).2 R hR
    rw [show P.restrict T = (volume.restrict T).withDensity
      (fun x => ENNReal.ofReal (Real.exp (-H x))) from restrict_withDensity hT _,
      weighted_integral H hH _ (volume.restrict T), weighted_integral H hH _ volume,
      weighted_integral H hH _ volume]
    exact h
  have hraw := le_of_tendsto_of_tendsto htail hright (Eventually.of_forall hbound)
  rw [show P.restrict T = (volume.restrict T).withDensity
    (fun x => ENNReal.ofReal (Real.exp (-H x))) from restrict_withDensity hT _,
    weighted_integral H hH _ (volume.restrict T), weighted_integral H hH _ volume,
    weighted_integral H hH _ volume] at hraw
  dsimp only
  simp only [integral_const_mul]
  have hscaled := mul_le_mul_of_nonneg_left hraw hr
  nlinarith [hscaled]
