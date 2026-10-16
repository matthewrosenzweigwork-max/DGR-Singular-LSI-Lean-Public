import Tablet.AtomicCoercivityExtension
import Tablet.EuclideanSobolev
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Tactic
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace AtomicNormalizedSobolev
private noncomputable def groundState {d : ℕ} (H f : OneParticle d → ℝ) :=
  fun x => f x * Real.exp (-H x / 2)
private theorem groundState_contDiff {d : ℕ} (H f : OneParticle d → ℝ)
    (hH : ContDiff ℝ 2 H) (hf : ContDiff ℝ 1 f) : ContDiff ℝ 1 (groundState H f) := by
  exact hf.mul (((hH.of_le (by norm_num)).neg.div_const 2).exp)
private theorem continuous_gradient {d : ℕ} (u : OneParticle d → ℝ) (hu : ContDiff ℝ 1 u) :
    Continuous (EuclideanGradient u) :=
  (InnerProductSpace.toDual ℝ (OneParticle d)).symm.continuous.comp (hu.continuous_fderiv (by norm_num))
private noncomputable def density {d : ℕ} (V U ψ : OneParticle d → ℝ) := fun x =>
  ‖EuclideanGradient ψ x‖^2 / 2 +
    (‖EuclideanGradient V x + EuclideanGradient U x‖^2 * ψ x^2) / 8 +
    (-EuclideanLaplacian U x * ψ x^2) / 2
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

private theorem gradient_scale {d : ℕ} (g : OneParticle d → ℝ)
    (hg : ContDiff ℝ 1 g) (a : ℝ) (x : OneParticle d) :
    EuclideanGradient (fun z => a * g z) x = a • EuclideanGradient g x := by
  apply (InnerProductSpace.toDual ℝ (OneParticle d)).injective
  rw [map_smul, EuclideanGradient, EuclideanGradient, toDual_gradient, toDual_gradient,
    fderiv_const_mul (hg.differentiable (by norm_num) x)]
private theorem gradient_L2 {d : ℕ} (g : OneParticle d → ℝ)
    (hi : Integrable (fun x => ‖EuclideanGradient g x‖^2)) :
    eLpNorm (EuclideanGradient g) 2 volume =
      ENNReal.ofReal (∫ x, ‖EuclideanGradient g x‖^2) ^ (1/2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  norm_num only [ENNReal.toReal_ofNat]
  congr 1
  rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun x => sq_nonneg _))]
  apply lintegral_congr
  intro x
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  simpa only [Nat.cast_ofNat] using ENNReal.rpow_natCast ‖EuclideanGradient g x‖ₑ 2
end AtomicNormalizedSobolev
open AtomicNormalizedSobolev
-- [TABLET NODE: AtomicNormalizedSobolev]
theorem AtomicNormalizedSobolev (d : ℕ) (hd : 3 ≤ d) (s A κ : ℝ)
    (hs : 0 < s) (hsd : s ≤ (d : ℝ) - 2) (hA : 0 ≤ A) (hκ : 0 < κ) (Ca : ℝ → ℝ) :
    ∃ (G : ℝ) (T : ℝ≥0∞), 0 ≤ G ∧ T < ⊤ ∧
      ∀ V : OneParticle d → ℝ, PotentialBounds d κ V →
      (∀ a : ℝ, 0 < a → ∀ x, EuclideanLaplacian V x ≤
        a * ‖EuclideanGradient V x‖ ^ (2 / (s + 1)) + Ca a) →
      ∀ {ι : Type*} (J : Finset ι) (charges : ι → ℝ) (y : ι → OneParticle d) (ε : ℝ),
      (∀ j ∈ J, 0 ≤ charges j) → (∑ j ∈ J, charges j ≤ A) → 0 < ε →
      ∀ (r : ℝ), 0 ≤ r → ∀ (f : OneParticle d → ℝ), ContDiff ℝ 1 f → ∀ c : ℝ,
      HasCompactSupport (fun x => f x - c) →
      let U := fun x => ∑ j ∈ J, charges j * RieszKernel s ε (x - y j)
      let ψ := fun x => Real.sqrt r * (f x * Real.exp (-(V x + U x) / 2))
      (∫ x, ψ x^2) = 1 →
      r * (∫ x, ‖EuclideanGradient f x‖^2 * Real.exp (-(V x + U x))) ≤ 1 →
      ContDiff ℝ 1 ψ ∧ Integrable (fun x => ψ x^2) volume ∧
        Integrable (fun x => ‖EuclideanGradient ψ x‖^2) volume ∧
        (∫ x, ‖EuclideanGradient ψ x‖^2) ≤ G ∧
        eLpNorm ψ (SobolevExponent d hd) volume ≤ T := by
-- BODY
  obtain ⟨C, hC, hcoerc⟩ := AtomicCoercivityExtension d hd s A κ hs hsd hA hκ Ca
  obtain ⟨S, hSob⟩ := EuclideanSobolev (ι := Fin d) (by simpa using hd)
  simp only [Fintype.card_fin] at hSob
  let G := 4*(1+C)
  let T : ℝ≥0∞ := S * ENNReal.ofReal G ^ (1/2 : ℝ)
  refine ⟨G, T, by dsimp [G]; positivity, by dsimp [T]; finiteness, ?_⟩
  intro V hV hgrowth ι J charges y ε ha hmass hε r hr f hf c hcf
  let U := fun x => ∑ j ∈ J, charges j * RieszKernel s ε (x-y j)
  let H := fun x => V x+U x
  let P := volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-H x)))
  let tr := fun (g : OneParticle d → ℝ) x => Real.sqrt r * groundState H g x
  dsimp only
  intro hunit henergy
  have hU : ContDiff ℝ 2 U := (AtomicInteractionSource d s ε hs hsd hε J charges y ha).1
  have hS : ∀ x, 0 ≤ -EuclideanLaplacian U x :=
    fun x => ((AtomicInteractionSource d s ε hs hsd hε J charges y ha).2 x).2
  have hH : ContDiff ℝ 2 H := hV.regularity.add hU
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
  have htrreg : ∀ g : OneParticle d → ℝ, ContDiff ℝ 1 g → ContDiff ℝ 1 (tr g) :=
    fun g hg => contDiff_const.mul (groundState_contDiff H g hH hg)
  have hsquare : ∀ g x, tr g x^2 = r * (g x^2 * Real.exp (-H x)) := by
    intro g x
    have hexp : Real.exp (-H x/2)^2 = Real.exp (-H x) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    dsimp [tr, groundState]
    rw [mul_pow, mul_pow, Real.sq_sqrt hr, hexp]
  have hgscale : ∀ g : OneParticle d → ℝ, ContDiff ℝ 1 g → ∀ x,
      ‖EuclideanGradient (tr g) x‖^2 = r * ‖EuclideanGradient (groundState H g) x‖^2 := by
    intro g hg x
    rw [gradient_scale _ (groundState_contDiff H g hH hg), norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt hr]
  have hgb : ∀ (g : OneParticle d → ℝ), ContDiff ℝ 1 g → ∀ c' : ℝ,
      HasCompactSupport (fun x => g x-c') →
      Integrable (fun x => ‖EuclideanGradient (tr g) x‖^2) ∧
      (∫ x, ‖EuclideanGradient (tr g) x‖^2) ≤
        2*r*((∫ x, ‖EuclideanGradient g x‖^2 ∂P)+C*(∫ x, g x^2 ∂P)) := by
    intro g hg c' hcg
    have hbnd := hcoerc V hV hgrowth J charges y ε ha hmass hε g hg c' hcg
    let ψ := groundState H g
    change Integrable (density V U ψ) ∧ (∫ x, density V U ψ x) ≤
      (∫ x, ‖EuclideanGradient g x‖^2 ∂P)+C*(∫ x, g x^2 ∂P) at hbnd
    have hpt : ∀ x, ‖EuclideanGradient (tr g) x‖^2 ≤ 2*r*density V U ψ x := by
      intro x
      rw [hgscale g hg]
      have ht := mul_nonneg (sq_nonneg ‖EuclideanGradient V x + EuclideanGradient U x‖) (sq_nonneg (ψ x))
      have hs' := mul_nonneg (hS x) (sq_nonneg (ψ x))
      dsimp [density]
      nlinarith
    have hi : Integrable (fun x => ‖EuclideanGradient (tr g) x‖^2) :=
      (hbnd.1.const_mul (2*r)).mono_nonneg
        ((continuous_gradient (tr g) (htrreg g hg)).norm.pow 2).aestronglyMeasurable
        (Eventually.of_forall (fun x => sq_nonneg _)) (Eventually.of_forall hpt)
    refine ⟨hi, ?_⟩
    have hmono := integral_mono hi (hbnd.1.const_mul (2*r)) hpt
    rw [integral_const_mul] at hmono
    exact hmono.trans (mul_le_mul_of_nonneg_left hbnd.2 (by positivity))
  have hiMass : Integrable (fun x => tr f x^2) := by
    obtain ⟨B, hB⟩ := hcf.exists_bound_of_continuous (hf.continuous.sub continuous_const)
    let F := max 0 B + |c|
    have hF : 0 ≤ F := by dsimp [F]; positivity
    have hfb : ∀ x, |f x| ≤ F := by
      intro x
      have h := abs_add_le (f x-c) c
      have hb : |f x-c| ≤ B := by simpa only [Real.norm_eq_abs] using hB x
      have heq : f x-c+c = f x := by ring
      rw [heq] at h
      dsimp [F]
      linarith [le_max_right (0 : ℝ) B]
    apply (hiH.const_mul (r*F^2)).mono_nonneg
      ((htrreg f hf).continuous.pow 2).aestronglyMeasurable
      (Eventually.of_forall (fun x => sq_nonneg _))
    exact Eventually.of_forall (fun x => by
      change tr f x^2 ≤ r*F^2*Real.exp (-H x)
      rw [hsquare]
      have hb := pow_le_pow_left₀ (abs_nonneg (f x)) (hfb x) 2
      rw [sq_abs] at hb
      have he := Real.exp_pos (-H x)
      exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb he.le) hr).trans_eq (by ring))
  have hM : r*(∫ x, f x^2 ∂P) = 1 := by
    rw [weighted_integral H hH.continuous]
    have h := hunit
    change (∫ x, tr f x^2) = 1 at h
    simp_rw [hsquare] at h
    rwa [integral_const_mul] at h
  have hE : r*(∫ x, ‖EuclideanGradient f x‖^2 ∂P) ≤ 1 := by
    rw [weighted_integral H hH.continuous]
    exact henergy
  have hg := hgb f hf c hcf
  have hcap : (∫ x, ‖EuclideanGradient (tr f) x‖^2) ≤ G := by
    have h := hg.2
    dsimp [G]
    nlinarith
  obtain ⟨fn, hreg, hval, _, _, _, hmasslim, henergylim, _⟩ :=
    WeightedSpatialApproximation P f hf c hcf
  have hcaplim := ((henergylim.add (hmasslim.const_mul C)).const_mul (2*r))
  have hlt : 2*r*((∫ x, ‖EuclideanGradient f x‖^2 ∂P)+C*(∫ x, f x^2 ∂P)) < G := by
    dsimp [G]
    nlinarith
  have hevent : ∀ᶠ n : ℕ in atTop, 2*r*((∫ x, ‖EuclideanGradient (fn n) x‖^2 ∂P)+
      C*(∫ x, fn n x^2 ∂P)) ≤ G :=
    (hcaplim.eventually (eventually_lt_nhds hlt)).mono (fun _ h => h.le)
  have hnormbound : ∀ᶠ n : ℕ in atTop,
      eLpNorm (tr (fn n)) (SobolevExponent d hd) volume ≤ T := by
    filter_upwards [hevent] with n hn
    have hcomp : HasCompactSupport (tr (fn n)) := (hreg n).2.mul_right.mul_left
    have hgn := hgb (fn n) (hreg n).1 0 (by simpa only [sub_zero] using (hreg n).2)
    have hsob := hSob (tr (fn n)) (htrreg (fn n) (hreg n).1) hcomp
    rw [gradient_L2 _ hgn.1] at hsob
    apply hsob.trans
    have hpow := ENNReal.rpow_le_rpow
      (ENNReal.ofReal_le_ofReal (hgn.2.trans hn)) (by norm_num : (0 : ℝ) ≤ 1/2)
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hnorm : eLpNorm (tr f) (SobolevExponent d hd) volume ≤ T :=
    Lp.eLpNorm_le_of_ae_tendsto hnormbound
      (fun n => (htrreg (fn n) (hreg n).1).continuous.aestronglyMeasurable)
      (Eventually.of_forall (fun x => by
        exact ((hval x).mul_const (Real.exp (-H x/2))).const_mul (Real.sqrt r)))
  exact ⟨htrreg f hf, hiMass, hg.1, hcap, hnorm⟩
