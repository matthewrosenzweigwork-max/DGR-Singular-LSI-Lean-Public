import Tablet.Preamble
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.Complex.Exponential
open MeasureTheory ProbabilityTheory
-- [TABLET NODE: IndependentVarianceMGF]
theorem IndependentVarianceMGF {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ) (f : Fin N → Ω → ℝ)
    (hf : ∀ i, Measurable (f i)) (A V : ℝ) (hA : 0 ≤ A) (hV : 0 ≤ V)
    (hb : ∀ i, ∀ᵐ x ∂μ, |f i x| ≤ A) (hm : ∀ i, (∫ x, f i x ∂μ) = 0)
    (hv : ∀ i, (∫ x, (f i x)^2 ∂μ) ≤ V) :
    ∀ t : ℝ, |t| * A ≤ 1 →
      Integrable (fun X : Fin N → Ω => Real.exp (t*∑ i,f i (X i)))
        (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ X : Fin N → Ω, Real.exp (t*∑ i,f i (X i))
        ∂Measure.pi (fun _ : Fin N => μ)) ≤ Real.exp ((N : ℝ)*t^2*V) ∧
      (0 ≤ t → ∀ u : ℝ,
        (Measure.pi (fun _ : Fin N => μ)).real {X : Fin N → Ω | u ≤ ∑ i,f i (X i)} ≤
          Real.exp ((N : ℝ)*t^2*V-t*u)) := by
-- BODY
  have bounded_mgf
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (A V : ℝ) (hA : 0 ≤ A) (hV : 0 ≤ V)
    (hb : ∀ᵐ x ∂μ, |f x| ≤ A) (hmean : (∫ x, f x ∂μ) = 0)
    (hvariance : (∫ x, (f x)^2 ∂μ) ≤ V) :
    ∀ t : ℝ, |t| * A ≤ 1 →
      Integrable (fun x => Real.exp (t*f x)) μ ∧
      (∫ x, Real.exp (t*f x) ∂μ) ≤ Real.exp (t^2*V) := by
    have hfi : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable A
      (by simpa only [Real.norm_eq_abs] using hb)
    have hf2i : Integrable (fun x => (f x)^2) μ := by
      apply Integrable.of_bound (hf.pow_const 2).aestronglyMeasurable (A^2)
      filter_upwards [hb] with x hx
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (f x)) hA).mpr hx
    intro t ht
    have hexpi : Integrable (fun x => Real.exp (t*f x)) μ := by
      apply Integrable.of_bound (hf.const_mul t).exp.aestronglyMeasurable (Real.exp (|t| * A))
      filter_upwards [hb] with x hx
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ |t * f x| := le_abs_self _
        _ = |t| * |f x| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left hx (abs_nonneg t)
    have hpoint : ∀ᵐ x ∂μ, Real.exp (t*f x) ≤ 1+t*f x+t^2*(f x)^2 := by
      filter_upwards [hb] with x hx
      have hz : |t * f x| ≤ 1 := by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left hx (abs_nonneg t)).trans ht
      have hs := Real.norm_exp_sub_one_sub_id_le (show ‖t*f x‖ ≤ 1 by simpa using hz)
      have hr : Real.exp (t*f x)-1-t*f x ≤ (t*f x)^2 := by
        calc
          _ ≤ |Real.exp (t*f x)-1-t*f x| := le_abs_self _
          _ ≤ |t * f x|^2 := by simpa only [Real.norm_eq_abs] using hs
          _ = _ := sq_abs _
      nlinarith
    have hlin : Integrable (fun x => 1+t*f x) μ :=
      (integrable_const (1:ℝ)).add (hfi.const_mul t)
    have hmajor : Integrable (fun x => 1+t*f x+t^2*(f x)^2) μ :=
      hlin.add (hf2i.const_mul (t^2))
    refine ⟨hexpi,?_⟩
    calc
      _ ≤ ∫ x, 1+t*f x+t^2*(f x)^2 ∂μ := integral_mono_ae hexpi hmajor hpoint
      _ = 1+t^2*(∫ x, (f x)^2 ∂μ) := by
        rw [integral_add hlin (hf2i.const_mul _),
          integral_add (integrable_const _) (hfi.const_mul t),
          integral_const_mul,integral_const_mul,hmean]
        simp
      _ ≤ 1+t^2*V := by
        simpa only [add_comm] using add_le_add_left (mul_le_mul_of_nonneg_left hvariance (sq_nonneg t)) (1:ℝ)
      _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (t^2*V)

  classical
  intro t ht
  have hsingle (i : Fin N) := bounded_mgf μ (f i) (hf i) A V hA hV
    (hb i) (hm i) (hv i) t ht
  have hint : Integrable (fun X : Fin N → Ω => Real.exp (t*∑ i,f i (X i)))
      (Measure.pi (fun _ : Fin N => μ)) := by
    simp_rw [Finset.mul_sum,Real.exp_sum]
    exact Integrable.fintype_prod (fun i => (hsingle i).1)
  have hbound : (∫ X : Fin N → Ω, Real.exp (t*∑ i,f i (X i))
      ∂Measure.pi (fun _ : Fin N => μ)) ≤ Real.exp ((N : ℝ)*t^2*V) := by
    calc
      _ = ∏ i,∫ x,Real.exp (t*f i x) ∂μ := by
        simp_rw [Finset.mul_sum,Real.exp_sum]
        exact integral_fintype_prod_eq_prod (fun i x => Real.exp (t*f i x))
      _ ≤ ∏ i : Fin N,Real.exp (t^2*V) :=
        Finset.prod_le_prod (fun i _ => integral_nonneg (fun x => Real.exp_nonneg _))
          (fun i _ => (hsingle i).2)
      _ = _ := by
        rw [←Real.exp_sum]
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        congr 1
        ring
  refine ⟨hint,hbound,?_⟩
  intro ht0 u
  calc
    _ ≤ Real.exp (-t*u)*(∫ X : Fin N → Ω,Real.exp (t*∑ i,f i (X i))
        ∂Measure.pi (fun _ : Fin N => μ)) :=
      measure_ge_le_exp_mul_mgf u ht0 hint
    _ ≤ Real.exp (-t*u)*Real.exp ((N : ℝ)*t^2*V) :=
      mul_le_mul_of_nonneg_left hbound (Real.exp_nonneg _)
    _ = _ := by rw [←Real.exp_add];congr 1;ring
