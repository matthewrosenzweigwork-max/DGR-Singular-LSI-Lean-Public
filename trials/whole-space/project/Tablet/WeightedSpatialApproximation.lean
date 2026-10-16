import Tablet.SpatialCutoffApproximation
import Tablet.OneParticle
import Tablet.GradientNormIdentity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
namespace WeightedSpatialApproximation
private theorem continuous_gradient {ι : Type*} [Fintype ι] (f : EuclideanSpace ℝ ι → ℝ)
    (hf : ContDiff ℝ 1 f) : Continuous (EuclideanGradient f) :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm.continuous.comp
    (hf.continuous_fderiv (by norm_num))
private theorem gradient_product {ι : Type*} [Fintype ι] (f g : EuclideanSpace ℝ ι → ℝ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (x : EuclideanSpace ℝ ι) :
    EuclideanGradient (fun y => f y * g y) x =
      g x • EuclideanGradient f x + f x • EuclideanGradient g x := by
  apply (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).injective
  rw [map_add, map_smul, map_smul, EuclideanGradient, EuclideanGradient, EuclideanGradient,
    toDual_gradient, toDual_gradient, toDual_gradient, fderiv_fun_mul (hf x) (hg x)]
  simp only [smul_eq_mul, add_comm]
private theorem constant_off_compact_global_bounds {ι : Type*} [Fintype ι] (f : EuclideanSpace ℝ ι → ℝ) (hf : ContDiff ℝ 1 f)
    (c : ℝ) (hcf : HasCompactSupport (fun x => f x - c)) :
    ∃ F G : ℝ, 0 ≤ F ∧ 0 ≤ G ∧ (∀ x, |f x| ≤ F) ∧ (∀ x, ‖EuclideanGradient f x‖ ≤ G) := by
  obtain ⟨B, hB⟩ := hcf.exists_bound_of_continuous (hf.continuous.sub continuous_const)
  have hd : ContDiff ℝ 1 (fun x => f x - c) := hf.sub contDiff_const
  have hcder := hcf.fderiv ℝ
  obtain ⟨G, hG⟩ := hcder.exists_bound_of_continuous (hd.continuous_fderiv (by norm_num))
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
  refine ⟨max 0 B + |c|, G, by positivity, hG0, ?_, ?_⟩
  · intro x
    have hsplit : f x = (f x - c) + c := by ring
    have hh := abs_add_le (f x - c) c
    have hbx : |f x - c| ≤ B := by simpa only [Real.norm_eq_abs] using hB x
    rw [hsplit]
    exact hh.trans (by linarith [le_max_right (0 : ℝ) B])
  · intro x
    have H := hG x
    rw [fderiv_sub_const c] at H
    simpa only [(GradientNormIdentity f x).2] using H

end WeightedSpatialApproximation
open WeightedSpatialApproximation
-- [TABLET NODE: WeightedSpatialApproximation]
theorem WeightedSpatialApproximation {ι : Type*} [Fintype ι] (P : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure P]
    (f : EuclideanSpace ℝ ι → ℝ) (hf : ContDiff ℝ 1 f) (c : ℝ)
    (hc : HasCompactSupport (fun x => f x - c)) :
    ∃ fn : ℕ → EuclideanSpace ℝ ι → ℝ,
      (∀ n, ContDiff ℝ 1 (fn n) ∧ HasCompactSupport (fn n)) ∧
      (∀ x, Tendsto (fun n => fn n x) atTop (𝓝 (f x))) ∧
      (∀ x, Tendsto (fun n => EuclideanGradient (fn n) x) atTop (𝓝 (EuclideanGradient f x))) ∧
      Tendsto (fun n => ∫ x, (fn n x - f x)^2 ∂P) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ x, ‖EuclideanGradient (fn n) x - EuclideanGradient f x‖^2 ∂P)
        atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ x, (fn n x)^2 ∂P) atTop (𝓝 (∫ x, f x^2 ∂P)) ∧
      Tendsto (fun n => ∫ x, ‖EuclideanGradient (fn n) x‖^2 ∂P)
        atTop (𝓝 (∫ x, ‖EuclideanGradient f x‖^2 ∂P)) ∧
      ∀ S : Set (EuclideanSpace ℝ ι), Tendsto (fun n => ∫ x in S, (fn n x)^2 ∂P)
        atTop (𝓝 (∫ x in S, f x^2 ∂P)) := by
-- BODY
  obtain ⟨χ, C, hC, hχreg, hχbounds, hχlim, hχgrad⟩ :=
    SpatialCutoffApproximation (ι := ι)
  obtain ⟨F, G, hF, hG, hfb, hgb⟩ := constant_off_compact_global_bounds f hf c hc
  let fn := fun n x => f x * χ n x
  have hreg : ∀ n, ContDiff ℝ 1 (fn n) ∧ HasCompactSupport (fn n) := fun n =>
    ⟨hf.mul ((hχreg n).1.of_le (by simp)), (hχreg n).2.mul_left⟩
  have hglim : ∀ x, Tendsto (fun n => EuclideanGradient (χ n) x) atTop (𝓝 0) := by
    intro x
    have hi : Tendsto (fun n : ℕ => C / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) := by
      simpa only [div_eq_mul_inv, one_div, mul_zero, one_mul] using
        tendsto_one_div_add_atTop_nhds_zero_nat.const_mul C
    exact tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero (fun n => norm_nonneg _) (fun n => hχgrad n x) hi)
  have hval : ∀ x, Tendsto (fun n => fn n x) atTop (𝓝 (f x)) := by
    intro x
    simpa only [fn, mul_one] using (tendsto_const_nhds (x := f x)).mul (hχlim x)
  have hprod : ∀ n x, EuclideanGradient (fn n) x =
      χ n x • EuclideanGradient f x + f x • EuclideanGradient (χ n) x := by
    intro n x
    exact gradient_product f (χ n) (hf.differentiable (by norm_num))
      ((hχreg n).1.differentiable (by simp)) x
  have hgrad : ∀ x, Tendsto (fun n => EuclideanGradient (fn n) x)
      atTop (𝓝 (EuclideanGradient f x)) := by
    intro x
    simp only [hprod]
    convert ((hχlim x).smul_const (EuclideanGradient f x)).add
      ((tendsto_const_nhds (x := f x)).smul (hglim x)) using 1 <;> simp
  let B := G + F * C
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb : ∀ n x, |fn n x| ≤ F ∧ ‖EuclideanGradient (fn n) x‖ ≤ B := by
    intro n x
    have hχ := hχbounds n x
    have hcg : ‖EuclideanGradient (χ n) x‖ ≤ C := by
      apply (hχgrad n x).trans
      apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).2
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    constructor
    · dsimp [fn]
      rw [abs_mul, abs_of_nonneg hχ.1]
      exact (mul_le_mul (hfb x) hχ.2 hχ.1 hF).trans_eq (mul_one _)
    · rw [hprod]
      apply (norm_add_le _ _).trans
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hχ.1]
      have h1 := mul_le_mul hχ.2 (hgb x) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      have h2 := mul_le_mul (hfb x) hcg (norm_nonneg _) hF
      dsimp [B]
      nlinarith
  refine ⟨fn, hreg, hval, hgrad, ?_, ?_, ?_, ?_, ?_⟩
  · have h := tendsto_integral_filter_of_dominated_convergence
      (μ := P) (bound := fun _ => (2*F)^2)
      (F := fun n x => (fn n x - f x)^2) (f := fun _ => (0 : ℝ))
      (Eventually.of_forall (fun n => (((hreg n).1.continuous.sub hf.continuous).pow 2).aestronglyMeasurable))
      (Eventually.of_forall (fun n => Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
        apply pow_le_pow_left₀ (abs_nonneg _) _ 2
        exact (abs_sub _ _).trans (by linarith [(hb n x).1, hfb x]))))
      (integrable_const _) (Eventually.of_forall (fun x => by
        simpa using ((hval x).sub_const (f x)).pow 2))
    simpa using h
  · have h := tendsto_integral_filter_of_dominated_convergence
      (μ := P) (bound := fun _ => (B+G)^2)
      (F := fun n x => ‖EuclideanGradient (fn n) x - EuclideanGradient f x‖^2)
      (f := fun _ => (0 : ℝ))
      (Eventually.of_forall (fun n =>
        (((continuous_gradient _ (hreg n).1).sub (continuous_gradient _ hf)).norm.pow 2).aestronglyMeasurable))
      (Eventually.of_forall (fun n => Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        apply pow_le_pow_left₀ (norm_nonneg _) _ 2
        exact (norm_sub_le _ _).trans (add_le_add (hb n x).2 (hgb x)))))
      (integrable_const _) (Eventually.of_forall (fun x => by
        simpa using ((hgrad x).sub_const (EuclideanGradient f x)).norm.pow 2))
    simpa using h
  · apply tendsto_integral_filter_of_dominated_convergence (fun _ => F^2)
    · exact Eventually.of_forall (fun n => ((hreg n).1.continuous.pow 2).aestronglyMeasurable)
    · exact Eventually.of_forall (fun n => Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hb n x).1 2))
    · exact integrable_const _
    · exact Eventually.of_forall (fun x => (hval x).pow 2)
  · apply tendsto_integral_filter_of_dominated_convergence (fun _ => B^2)
    · exact Eventually.of_forall (fun n =>
        ((continuous_gradient _ (hreg n).1).norm.pow 2).aestronglyMeasurable)
    · exact Eventually.of_forall (fun n => Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hb n x).2 2))
    · exact integrable_const _
    · exact Eventually.of_forall (fun x => (hgrad x).norm.pow 2)
  · intro S
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => F^2)
    · exact Eventually.of_forall (fun n => ((hreg n).1.continuous.pow 2).aestronglyMeasurable)
    · exact Eventually.of_forall (fun n => Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hb n x).1 2))
    · exact integrable_const _
    · exact Eventually.of_forall (fun x => (hval x).pow 2)
