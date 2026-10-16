module

public import Tablet.ProductBoundedDifferences
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Probability.Independence.Integration

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
-- [TABLET NODE: CanonicalL2SumConcentration]
theorem CanonicalL2SumConcentration {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ)
    (q : Ω → Ω → ℝ) (hq : Measurable (fun p : Ω × Ω => q p.1 p.2))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hb : ∀ x y,|q x y|≤A)
    (hv : ∀ x,(∫ y,(q x y)^2 ∂μ)≤B^2) :
    ∀ t : ℝ,
    (∫ X : Fin N → Ω,Real.exp (t*(Real.sqrt (∫ y,(∑ i,q (X i) y)^2 ∂μ)-
      ∫ Y : Fin N → Ω,Real.sqrt (∫ y,(∑ i,q (Y i) y)^2 ∂μ)
        ∂Measure.pi (fun _ : Fin N => μ))) ∂Measure.pi (fun _ : Fin N => μ)) ≤
      Real.exp (2*(N : ℝ)*B^2*t^2) := by
-- BODY
  classical
  let S (X : Fin N → Ω) (y : Ω) := ∑ i,q (X i) y
  let F (X : Fin N → Ω) := Real.sqrt (∫ y,(S X y)^2 ∂μ)
  have hqm (x : Ω) : Measurable (q x) := hq.comp (measurable_const.prodMk measurable_id)
  have hqL (x : Ω) : MemLp (q x) 2 μ := MemLp.of_bound (hqm x).aestronglyMeasurable A
    (Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hb x y)
  have hSm (X : Fin N → Ω) : Measurable (S X) := Finset.measurable_fun_sum _ (fun i _ => hqm (X i))
  have hSb (X : Fin N → Ω) (y : Ω) : |S X y|≤(N : ℝ)*A := by
    calc
      _ ≤ ∑ i,|q (X i) y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin N,A := Finset.sum_le_sum (fun i _ => hb _ _)
      _ = _ := by simp
  have hSL (X : Fin N → Ω) : MemLp (S X) 2 μ := MemLp.of_bound (hSm X).aestronglyMeasurable ((N : ℝ)*A)
    (Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hSb X y)
  have norm_square (r : Ω → ℝ) (hr : MemLp r 2 μ) : ‖hr.toLp r‖^2=∫ y,(r y)^2 ∂μ := by
    rw [←real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hr.coeFn_toLp] with y hy
    simp only [hy,real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
  have norm_sqrt (r : Ω → ℝ) (hr : MemLp r 2 μ) : Real.sqrt (∫ y,(r y)^2 ∂μ)=‖hr.toLp r‖ := by
    rw [←norm_square r hr,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]
  have hFq (X : Fin N → Ω) : F X=‖(hSL X).toLp (S X)‖ := norm_sqrt _ _
  have hFm : Measurable F := by
    have hm : Measurable (fun p : (Fin N → Ω) × Ω => (S p.1 p.2)^2) := by
      apply Measurable.pow_const
      apply Finset.measurable_fun_sum
      intro i hi
      have hp : Measurable (fun p : (Fin N → Ω) × Ω => (p.1 i,p.2)) :=
        ((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd
      exact hq.comp hp
    exact Real.continuous_sqrt.measurable.comp hm.stronglyMeasurable.integral_prod_right'.measurable
  have hFn (X : Fin N → Ω) : 0≤F X := Real.sqrt_nonneg _
  have hFbound (X : Fin N → Ω) : |F X|≤(N : ℝ)*A := by
    rw [abs_of_nonneg (hFn X)]
    apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg (Nat.cast_nonneg _) hA,?_⟩
    calc
      _ ≤ ∫ _ : Ω,((N : ℝ)*A)^2 ∂μ :=
        integral_mono_ae (hSL X).integrable_sq (integrable_const _)
          (Filter.Eventually.of_forall fun y => by nlinarith [abs_le.mp (hSb X y),sq_nonneg (S X y)])
      _ = _ := by simp
  have hqn (x : Ω) : ‖(hqL x).toLp (q x)‖≤B := by
    have hh := hv x
    rw [←norm_square (q x) (hqL x)] at hh
    nlinarith [norm_nonneg ((hqL x).toLp (q x))]
  have hFd : ∀ i X Y, (∀ j,j≠i → X j=Y j) → |F X-F Y|≤2*B := by
    intro i X Y hXY
    have hSdiff : S X-S Y=q (X i)-q (Y i) := by
      funext y
      dsimp [S]
      rw [←Finset.sum_sub_distrib]
      rw [Finset.sum_eq_single i (fun j hj hji => by simp only [hXY j hji,sub_self]) (by simp)]
    have hdiff : (hSL X).toLp (S X)-(hSL Y).toLp (S Y)=
        (hqL (X i)).toLp (q (X i))-(hqL (Y i)).toLp (q (Y i)) := by
      rw [←MemLp.toLp_sub,←MemLp.toLp_sub]
      exact (MemLp.toLp_eq_toLp_iff _ _).mpr (Filter.Eventually.of_forall fun y => congrFun hSdiff y)
    rw [hFq,hFq]
    calc
      _ ≤ ‖(hSL X).toLp (S X)-(hSL Y).toLp (S Y)‖ := abs_norm_sub_norm_le _ _
      _ = ‖(hqL (X i)).toLp (q (X i))-(hqL (Y i)).toLp (q (Y i))‖ := congrArg norm hdiff
      _ ≤ ‖(hqL (X i)).toLp (q (X i))‖+‖(hqL (Y i)).toLp (q (Y i))‖ := norm_sub_le _ _
      _ ≤ _ := by linarith [hqn (X i),hqn (Y i)]
  intro t
  have hh := ProductBoundedDifferences μ N F hFm ((N : ℝ)*A) (2*B)
    (mul_nonneg (Nat.cast_nonneg _) hA) (by linarith) hFbound hFd t
  convert hh using 1
  congr 1
  ring
