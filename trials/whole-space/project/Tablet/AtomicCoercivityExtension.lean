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
namespace AtomicCoercivityExtension
private noncomputable def groundState {d : ℕ} (H f : OneParticle d → ℝ) :=
  fun x => f x * Real.exp (-H x / 2)
private theorem groundState_contDiff {d : ℕ} (H f : OneParticle d → ℝ)
    (hH : ContDiff ℝ 2 H) (hf : ContDiff ℝ 1 f) : ContDiff ℝ 1 (groundState H f) := by
  exact hf.mul (((hH.of_le (by norm_num)).neg.div_const 2).exp)
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

private noncomputable def density {d : ℕ} (V U ψ : OneParticle d → ℝ) := fun x =>
  ‖EuclideanGradient ψ x‖^2 / 2 +
    (‖EuclideanGradient V x + EuclideanGradient U x‖^2 * ψ x^2) / 8 +
    (-EuclideanLaplacian U x * ψ x^2) / 2
private theorem density_continuous {d : ℕ} (V U ψ : OneParticle d → ℝ)
    (hV : ContDiff ℝ 2 V) (hU : ContDiff ℝ 2 U) (hψ : ContDiff ℝ 1 ψ) :
    Continuous (density V U ψ) := by
  exact (((continuous_gradient ψ hψ).norm.pow 2).div_const 2 |>.add
    ((((continuous_gradient V (hV.of_le (by norm_num))).add
      (continuous_gradient U (hU.of_le (by norm_num)))).norm.pow 2 |>.mul
      (hψ.continuous.pow 2)).div_const 8)).add
    (((continuous_laplacian U hU).neg.mul (hψ.continuous.pow 2)).div_const 2)
private theorem density_nonneg {d : ℕ} (V U ψ : OneParticle d → ℝ)
    (hS : ∀ x, 0 ≤ -EuclideanLaplacian U x) (x : OneParticle d) :
    0 ≤ density V U ψ x := by
  have hx := hS x
  dsimp [density]
  positivity
private theorem density_compact_integral {d : ℕ} (V U ψ : OneParticle d → ℝ)
    (hV : ContDiff ℝ 2 V) (hU : ContDiff ℝ 2 U)
    (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) :
    Integrable (density V U ψ) ∧
      (∫ x, density V U ψ x) = (∫ x, ‖EuclideanGradient ψ x‖ ^ 2) / 2 +
        (∫ x, ‖EuclideanGradient V x + EuclideanGradient U x‖ ^ 2 * ψ x ^ 2) / 8 +
        (∫ x, -EuclideanLaplacian U x * ψ x ^ 2) / 2 := by
  have hiG := compact_gradient_energy_integrable ψ hψ hcψ
  have hiT : Integrable (fun x => ‖EuclideanGradient V x + EuclideanGradient U x‖ ^ 2 * ψ x ^ 2) := compact_weight_integrable _ ψ
    (((continuous_gradient V (hV.of_le (by norm_num))).add
      (continuous_gradient U (hU.of_le (by norm_num)))).norm.pow 2) hψ hcψ
  have hiS : Integrable (fun x => -EuclideanLaplacian U x * ψ x ^ 2) := by
    simpa only [Pi.neg_apply] using compact_weight_integrable _ ψ
      (continuous_laplacian U hU).neg hψ hcψ
  constructor
  · exact ((hiG.div_const 2).add (hiT.div_const 8)).add (hiS.div_const 2)
  · unfold density
    have h1 := integral_add ((hiG.div_const 2).add (hiT.div_const 8)) (hiS.div_const 2)
    have h2 := integral_add (hiG.div_const 2) (hiT.div_const 8)
    dsimp only [Pi.add_apply, Pi.div_apply] at h1 h2
    rw [h1, h2, integral_div, integral_div, integral_div]
private theorem gradient_product {d : ℕ} (f g : OneParticle d → ℝ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (x : OneParticle d) :
    EuclideanGradient (fun y => f y * g y) x =
      g x • EuclideanGradient f x + f x • EuclideanGradient g x := by
  apply (InnerProductSpace.toDual ℝ (OneParticle d)).injective
  rw [map_add, map_smul, map_smul, EuclideanGradient, EuclideanGradient, EuclideanGradient,
    toDual_gradient, toDual_gradient, toDual_gradient, fderiv_fun_mul (hf x) (hg x)]
  simp only [smul_eq_mul, add_comm]
private theorem weighted_integral {d : ℕ} (H : OneParticle d → ℝ) (hH : Continuous H)
    (g : OneParticle d → ℝ) :
    (∫ x, g x ∂volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-H x)))) =
      ∫ x, g x * Real.exp (-H x) := by
  have hr : Measurable (fun x => ENNReal.ofReal (Real.exp (-H x))) := by
    exact (Real.measurable_exp.comp hH.measurable.neg).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hr
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    dsimp only
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, mul_comm])
end AtomicCoercivityExtension
open AtomicCoercivityExtension
-- [TABLET NODE: AtomicCoercivityExtension]
theorem AtomicCoercivityExtension (d : ℕ) (hd : 3 ≤ d) (s A κ : ℝ)
    (hs : 0 < s) (hsd : s ≤ (d : ℝ) - 2) (hA : 0 ≤ A) (hκ : 0 < κ) (Ca : ℝ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ V : OneParticle d → ℝ, PotentialBounds d κ V →
      (∀ a : ℝ, 0 < a → ∀ x, EuclideanLaplacian V x ≤
        a * ‖EuclideanGradient V x‖ ^ (2 / (s + 1)) + Ca a) →
      ∀ {ι : Type*} (J : Finset ι) (charges : ι → ℝ) (y : ι → OneParticle d) (ε : ℝ),
      (∀ j ∈ J, 0 ≤ charges j) → (∑ j ∈ J, charges j ≤ A) → 0 < ε →
      ∀ (f : OneParticle d → ℝ), ContDiff ℝ 1 f → ∀ c : ℝ,
      HasCompactSupport (fun x => f x - c) →
      let U := fun x => ∑ j ∈ J, charges j * RieszKernel s ε (x - y j)
      let ψ := fun x => f x * Real.exp (-(V x + U x) / 2)
      let P := volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-(V x + U x))))
      let D := fun x => ‖EuclideanGradient ψ x‖^2 / 2 +
        (‖EuclideanGradient V x + EuclideanGradient U x‖^2 * ψ x^2) / 8 +
        (-EuclideanLaplacian U x * ψ x^2) / 2
      Integrable D volume ∧ (∫ x, D x) ≤
        (∫ x, ‖EuclideanGradient f x‖^2 ∂P) + C * (∫ x, f x^2 ∂P) := by
-- BODY
  obtain ⟨C, hC, hcompact⟩ := AtomicCompactCoercivity d hd s A hs hsd hA Ca
  refine ⟨C, hC, ?_⟩
  intro V hV hgrowth ι J charges y ε ha hmass hε f hf c hcf
  let U := fun x => ∑ j ∈ J, charges j * RieszKernel s ε (x - y j)
  let H := fun x => V x + U x
  let ψ := groundState H f
  let P := volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-H x)))
  have hU : ContDiff ℝ 2 U := (AtomicInteractionSource d s ε hs hsd hε J charges y ha).1
  have hS : ∀ x, 0 ≤ -EuclideanLaplacian U x :=
    fun x => ((AtomicInteractionSource d s ε hs hsd hε J charges y ha).2 x).2
  have hH : ContDiff ℝ 2 H := hV.regularity.add hU
  have hψ : ContDiff ℝ 1 ψ := groundState_contDiff H f hH hf
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
    hiV.mono' ((Real.continuous_exp.comp hH.continuous.neg).aestronglyMeasurable)
      (Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (by dsimp [H]; linarith [hUn x])))
  haveI : IsFiniteMeasure P := by
    apply isFiniteMeasure_withDensity
    rw [← ofReal_integral_eq_lintegral_ofReal hiH
      (Eventually.of_forall (fun x => (Real.exp_pos _).le))]
    exact ENNReal.ofReal_ne_top
  obtain ⟨fn, hreg, hval, hgrad, _, _, hmasslim, henergylim, _⟩ :=
    WeightedSpatialApproximation P f hf c hcf
  let ψn := fun n => groundState H (fn n)
  have hψn : ∀ n, ContDiff ℝ 1 (ψn n) :=
    fun n => groundState_contDiff H (fn n) hH (hreg n).1
  have hcψn : ∀ n, HasCompactSupport (ψn n) := fun n => (hreg n).2.mul_right
  let e := fun x => Real.exp (-H x / 2)
  have he : ContDiff ℝ 1 e := ((hH.of_le (by norm_num)).neg.div_const 2).exp
  have hψval : ∀ x, Tendsto (fun n => ψn n x) atTop (𝓝 (ψ x)) := by
    intro x
    exact (hval x).mul_const (e x)
  have hψgrad : ∀ x, Tendsto (fun n => EuclideanGradient (ψn n) x) atTop
      (𝓝 (EuclideanGradient ψ x)) := by
    intro x
    have hprod : ∀ n, EuclideanGradient (ψn n) x =
        e x • EuclideanGradient (fn n) x + fn n x • EuclideanGradient e x :=
      fun n => gradient_product (fn n) e ((hreg n).1.differentiable (by norm_num))
        (he.differentiable (by norm_num)) x
    rw [show EuclideanGradient ψ x = e x • EuclideanGradient f x +
      f x • EuclideanGradient e x from gradient_product f e (hf.differentiable (by norm_num))
        (he.differentiable (by norm_num)) x]
    simp only [hprod]
    exact ((hgrad x).const_smul (e x)).add ((hval x).smul_const (EuclideanGradient e x))
  have hDlim : ∀ x, Tendsto (fun n => density V U (ψn n) x) atTop (𝓝 (density V U ψ x)) := by
    intro x
    exact (((hψgrad x).norm.pow 2).div_const 2 |>.add
      (((hψval x).pow 2).const_mul (‖EuclideanGradient V x + EuclideanGradient U x‖^2) |>.div_const 8)).add
      (((hψval x).pow 2).const_mul (-EuclideanLaplacian U x) |>.div_const 2)
  let Dn := fun n x => ENNReal.ofReal (density V U (ψn n) x)
  have hDm : ∀ n, Measurable (Dn n) :=
    fun n => (density_continuous V U (ψn n) hV.regularity hU (hψn n)).measurable.ennreal_ofReal
  have hDlim' : ∀ x, Tendsto (fun n => Dn n x) atTop
      (𝓝 (ENNReal.ofReal (density V U ψ x))) := fun x => ENNReal.tendsto_ofReal (hDlim x)
  have hFatou : (∫⁻ x, ENNReal.ofReal (density V U ψ x)) ≤
      liminf (fun n => ∫⁻ x, Dn n x) atTop := by
    calc
      _ = ∫⁻ x, liminf (fun n => Dn n x) atTop :=
        lintegral_congr (fun x => (hDlim' x).liminf_eq.symm)
      _ ≤ _ := lintegral_liminf_le hDm
  have hbnd : ∀ n, (∫⁻ x, Dn n x) ≤ ENNReal.ofReal
      ((∫ x, ‖EuclideanGradient (fn n) x‖^2 ∂P) + C * ∫ x, fn n x^2 ∂P) := by
    intro n
    have hc := hcompact V hV.regularity hgrowth J charges y ε ha hmass hε
      (fn n) (hreg n).1 (hreg n).2
    have hdi := density_compact_integral V U (ψn n) hV.regularity hU (hψn n) (hcψn n)
    change (∫⁻ x, ENNReal.ofReal (density V U (ψn n) x)) ≤ _
    rw [← ofReal_integral_eq_lintegral_ofReal hdi.1
      (Eventually.of_forall (density_nonneg V U (ψn n) hS)), hdi.2]
    apply ENNReal.ofReal_le_ofReal
    have hsquare : ∀ x, ψn n x^2 = fn n x^2 * Real.exp (-H x) := by
      intro x
      dsimp [ψn, groundState]
      have hexp : Real.exp (-H x / 2)^2 = Real.exp (-H x) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      rw [mul_pow, hexp]
    rw [weighted_integral H hH.continuous, weighted_integral H hH.continuous]
    simp_rw [← hsquare]
    exact hc
  have hR := hFatou.trans ((liminf_le_liminf (Eventually.of_forall hbnd)).trans_eq
    (ENNReal.tendsto_ofReal (henergylim.add (hmasslim.const_mul C))).liminf_eq)
  have hiD : Integrable (density V U ψ) :=
    (lintegral_ofReal_ne_top_iff_integrable
      (density_continuous V U ψ hV.regularity hU hψ).aestronglyMeasurable
      (Eventually.of_forall (density_nonneg V U ψ hS))).mp
      (ne_of_lt (hR.trans_lt ENNReal.ofReal_lt_top))
  refine ⟨hiD, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hiD
    (Eventually.of_forall (density_nonneg V U ψ hS))] at hR
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hR
