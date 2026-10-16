module

public import Tablet.RawL2OperatorDescent
public import Tablet.WeightedIntegralCauchySchwarz
public import Tablet.Preamble
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Tactic

@[expose] public section
open MeasureTheory Filter Set
open scoped InnerProduct
set_option autoImplicit false
set_option maxHeartbeats 1500000

universe u
-- [TABLET NODE: ReferenceKernelSchur]
theorem ReferenceKernelSchur {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (K : Ω → Ω → ℝ)
    (hKm : Measurable (fun p : Ω × Ω => K p.1 p.2))
    (C M : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hKb : ∀ x y, 0 ≤ K x y ∧ K x y ≤ C)
    (hKs : ∀ x y, K x y = K y x)
    (hrow : ∀ x, (∫ y, K x y ∂μ) ≤ M) :
    ∃! T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ,
      ‖T‖ ≤ M ∧
      (∀ v w, inner ℝ v (T w) = inner ℝ (T v) w) ∧
      (∀ (f : Ω → ℝ) (hf : MemLp f 2 μ),
        T (hf.toLp f) =ᵐ[μ] fun x => ∫ y, K x y*f y ∂μ) := by
-- BODY
  have real_L2_inner_toLp {α : Type u} [MeasurableSpace α] {μ : Measure α} (f g : α → ℝ)
      (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
      inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
    simp [hfx, hgx, mul_comm]
  have real_L2_norm_sq_toLp {α : Type u} [MeasurableSpace α] {μ : Measure α} (f : α → ℝ) (hf : MemLp f 2 μ) :
      ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, real_L2_inner_toLp]
    simp_rw [pow_two]
  have nonnegative_symmetric_kernel_schur {Ω : Type u} [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (K : Ω → Ω → ℝ)
      (hKm : Measurable (fun p : Ω × Ω => K p.1 p.2))
      (C M : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M)
      (hKb : ∀ x y, 0 ≤ K x y ∧ K x y ≤ C)
      (hKs : ∀ x y, K x y = K y x)
      (hrow : ∀ x, (∫ y, K x y ∂μ) ≤ M)
      (f : Ω → ℝ) (hf : MemLp f 2 μ) :
      MemLp (fun x => ∫ y, K x y*f y ∂μ) 2 μ ∧
        (∫ x, (∫ y, K x y*f y ∂μ)^2 ∂μ) ≤ M^2*(∫ y, (f y)^2 ∂μ) := by
    let T := fun x => ∫ y, K x y*f y ∂μ
    let D := fun x => ∫ y, K x y*(f y)^2 ∂μ
    have hKmx (x : Ω) : Measurable (K x) :=
      hKm.comp (measurable_const.prodMk measurable_id)
    have hKnorm (x y : Ω) : ‖K x y‖ ≤ C := by
      rw [Real.norm_eq_abs, abs_of_nonneg (hKb x y).1]
      exact (hKb x y).2
    have hKi (x : Ω) : Integrable (K x) μ :=
      (integrable_const C).mono' (hKmx x).aestronglyMeasurable
        (Eventually.of_forall (hKnorm x))
    have hKfi (x : Ω) : Integrable (fun y => K x y*f y) μ := by
      simpa only [mul_comm] using (hf.integrable (by norm_num)).bdd_mul
        (hKmx x).aestronglyMeasurable (Eventually.of_forall (hKnorm x))
    have hKf2i (x : Ω) : Integrable (fun y => K x y*(f y)^2) μ := by
      simpa only [mul_comm] using hf.integrable_sq.bdd_mul
        (hKmx x).aestronglyMeasurable (Eventually.of_forall (hKnorm x))
    have hJ : Integrable (fun p : Ω × Ω => K p.1 p.2*(f p.2)^2) (μ.prod μ) := by
      simpa only [mul_comm] using (hf.integrable_sq.comp_snd μ).bdd_mul
        hKm.aestronglyMeasurable (Eventually.of_forall fun p => hKnorm p.1 p.2)
    have hDi : Integrable D μ := hJ.integral_prod_left
    have hDn (x : Ω) : 0 ≤ D x :=
      integral_nonneg fun y => mul_nonneg (hKb x y).1 (sq_nonneg _)
    have hTm : AEStronglyMeasurable T μ :=
      (hKm.aestronglyMeasurable.mul hf.aestronglyMeasurable.comp_snd).integral_prod_right'
    have hpoint (x : Ω) : (T x)^2 ≤ M*D x := by
      have h := WeightedIntegralCauchySchwarz μ (K x) f
        (Eventually.of_forall fun y => (hKb x y).1) (hKi x) (hKfi x) (hKf2i x)
      exact h.trans (mul_le_mul_of_nonneg_right (hrow x) (hDn x))
    have hTi : Integrable (fun x => (T x)^2) μ :=
      (hDi.const_mul M).mono' (hTm.pow 2)
        (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (T x))] using hpoint x)
    have hmass : (∫ x, D x ∂μ) ≤ M*(∫ y, (f y)^2 ∂μ) := by
      change (∫ x, ∫ y, K x y*(f y)^2 ∂μ ∂μ) ≤ _
      rw [integral_integral_swap hJ, ← integral_const_mul]
      apply integral_mono_of_nonneg
        (Eventually.of_forall fun y => integral_nonneg fun x =>
          mul_nonneg (hKb x y).1 (sq_nonneg _)) (hf.integrable_sq.const_mul M)
      exact Eventually.of_forall fun y => by
        dsimp only
        rw [integral_mul_const]
        have hcol : (∫ x, K x y ∂μ) ≤ M := by
          have he : (∫ x, K x y ∂μ) = ∫ x, K y x ∂μ :=
            integral_congr_ae (Eventually.of_forall fun x => hKs x y)
          rw [he]
          exact hrow y
        exact mul_le_mul_of_nonneg_right hcol (sq_nonneg _)
    refine ⟨(memLp_two_iff_integrable_sq hTm).mpr hTi, ?_⟩
    calc
      (∫ x, (T x)^2 ∂μ) ≤ ∫ x, M*D x ∂μ :=
        integral_mono hTi (hDi.const_mul M) hpoint
      _ = M*(∫ x, D x ∂μ) := integral_const_mul _ _
      _ ≤ M*(M*(∫ y, (f y)^2 ∂μ)) := mul_le_mul_of_nonneg_left hmass hM
      _ = _ := by ring
  have kernel_row_integrable {Ω : Type u} [MeasurableSpace Ω]
      (μ : Measure Ω) [IsFiniteMeasure μ] (K : Ω → Ω → ℝ)
      (hKm : Measurable (fun p : Ω × Ω => K p.1 p.2))
      (C : ℝ) (hKb : ∀ x y, ‖K x y‖ ≤ C)
      (f : Ω → ℝ) (hf : Integrable f μ) (x : Ω) :
      Integrable (fun y => K x y*f y) μ := by
    have hm : Measurable (K x) := hKm.comp (measurable_const.prodMk measurable_id)
    simpa only [mul_comm] using hf.bdd_mul hm.aestronglyMeasurable (Eventually.of_forall (hKb x))
  let Tf := fun (f : Ω → ℝ) x => ∫ y, K x y*f y ∂μ
  have hKn (x y : Ω) : ‖K x y‖ ≤ C := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hKb x y).1]
    exact (hKb x y).2
  have hmem (f : Ω → ℝ) (hf : MemLp f 2 μ) : MemLp (Tf f) 2 μ :=
    (nonnegative_symmetric_kernel_schur μ K hKm C M hC hM hKb hKs hrow f hf).1
  have hbound (f : Ω → ℝ) (hf : MemLp f 2 μ) :
      ‖(hmem f hf).toLp (Tf f)‖ ≤ M*‖hf.toLp f‖ := by
    have h := (nonnegative_symmetric_kernel_schur μ K hKm C M hC hM hKb hKs hrow f hf).2
    change (∫ x, (Tf f x)^2 ∂μ) ≤ M^2*(∫ x, (f x)^2 ∂μ) at h
    rw [← real_L2_norm_sq_toLp (Tf f) (hmem f hf), ← real_L2_norm_sq_toLp f hf] at h
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).mp
    simpa only [mul_pow] using h
  have hae (f g : Ω → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
      (hfg : f =ᵐ[μ] g) : Tf f =ᵐ[μ] Tf g := by
    exact Eventually.of_forall fun x => integral_congr_ae
      (hfg.mono fun y hy => by change K x y*f y = K x y*g y; rw [hy])
  have hadd (f g : Ω → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
      Tf (f+g) =ᵐ[μ] Tf f+Tf g := by
    exact Eventually.of_forall fun x => by
      dsimp [Tf]
      simp only [Pi.add_apply, mul_add]
      exact integral_add
        (kernel_row_integrable μ K hKm C hKn f (hf.integrable (by norm_num)) x)
        (kernel_row_integrable μ K hKm C hKn g (hg.integrable (by norm_num)) x)
  have hsmul (c : ℝ) (f : Ω → ℝ) (hf : MemLp f 2 μ) :
      Tf (c • f) =ᵐ[μ] c • Tf f := by
    exact Eventually.of_forall fun x => by
      dsimp [Tf]
      have he : (fun y => K x y*(c*f y)) = fun y => c*(K x y*f y) := by funext y; ring
      rw [he, integral_const_mul]
  obtain ⟨T,hT,hunique⟩ := RawL2OperatorDescent (μ := μ) (η := μ) Tf M hM hmem
    hae hadd hsmul hbound
  have hself : ∀ v w, inner ℝ v (T w) = inner ℝ (T v) w := by
    intro v w
    have hvi := (Lp.memLp v).integrable (by norm_num)
    have hwi := (Lp.memLp w).integrable (by norm_num)
    have hprod : Integrable (fun p : Ω × Ω => K p.1 p.2*(v p.1*w p.2)) (μ.prod μ) :=
      (hvi.mul_prod hwi).bdd_mul hKm.aestronglyMeasurable
        (Eventually.of_forall fun p => hKn p.1 p.2)
    have hlhs : inner ℝ v (T w) = ∫ x, ∫ y, K x y*(v x*w y) ∂μ ∂μ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      have hr : T w =ᵐ[μ] Tf w := by simpa only [Lp.toLp_coeFn] using hT.2 w (Lp.memLp w)
      filter_upwards [hr] with x hx
      rw [hx]
      dsimp [Tf]
      simp only [starRingEnd_apply, star_trivial]
      rw [← integral_mul_const]
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by simp only [RCLike.inner_apply, conj_trivial]; ring
    have hrhs : inner ℝ (T v) w = ∫ y, ∫ x, K x y*(v x*w y) ∂μ ∂μ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      have hr : T v =ᵐ[μ] Tf v := by simpa only [Lp.toLp_coeFn] using hT.2 v (Lp.memLp v)
      filter_upwards [hr] with y hy
      rw [hy]
      dsimp [Tf]
      simp only [starRingEnd_apply, star_trivial]
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simp only [RCLike.inner_apply, conj_trivial]
        rw [hKs y x]
        ring
    rw [hlhs, hrhs]
    exact integral_integral_swap hprod
  refine ⟨T, ⟨hT.1,hself,hT.2⟩, ?_⟩
  intro U hU
  exact hunique U ⟨hU.1,hU.2.2⟩
