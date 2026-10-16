module

public import Tablet.IndependentVarianceMGF
public import Tablet.MomentFromExponential
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section
open MeasureTheory
-- [TABLET NODE: IndependentBernsteinMoments]
theorem IndependentBernsteinMoments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ) (f : Fin N → Ω → ℝ)
    (hf : ∀ i, Measurable (f i)) (A V : ℝ) (hA : 0 < A) (hV : 0 ≤ V)
    (hb : ∀ i x, |f i x| ≤ A) (hm : ∀ i, (∫x,f i x ∂μ)=0)
    (hv : ∀i,(∫x,(f i x)^2 ∂μ)≤V) (n : ℕ) (hn : 1≤n) :
    (∫X : Fin N → Ω,|∑i,f i (X i)|^n ∂Measure.pi (fun _ : Fin N => μ)) ≤
      (6*((n:ℝ)*A+Real.sqrt ((n:ℝ)*(N:ℝ)*V)))^n := by
-- BODY
  classical
  let ν := Measure.pi (fun _ : Fin N => μ)
  let F (X : Fin N → Ω) := ∑i,f i (X i)
  let r := Real.sqrt ((N:ℝ)*V/(n:ℝ))
  let D := A+r
  let ℓ := D⁻¹
  have hnR : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hrn : 0≤r := Real.sqrt_nonneg _
  have hDp : 0<D := by dsimp [D]; linarith
  have hℓp : 0<ℓ := inv_pos.mpr hDp
  have hrestr : |ℓ| * A≤1 := by
    rw [abs_of_pos hℓp]
    change D⁻¹*A≤1
    rw [inv_mul_eq_div,div_le_one hDp]
    dsimp [D]; linarith
  have hrestrn : |-ℓ| * A≤1 := by simpa only [abs_neg] using hrestr
  have hMGFp := IndependentVarianceMGF μ N f hf A V hA.le hV
    (fun i => Filter.Eventually.of_forall (hb i)) hm hv ℓ hrestr
  have hMGFn := IndependentVarianceMGF μ N f hf A V hA.le hV
    (fun i => Filter.Eventually.of_forall (hb i)) hm hv (-ℓ) hrestrn
  have hFm : Measurable F := Finset.measurable_fun_sum _ fun i _ => (hf i).comp (measurable_pi_apply i)
  have hmoment := (MomentFromExponential ν F hFm ℓ hℓp n hMGFp.1 hMGFn.1).2
  have hrsq : r^2=(N:ℝ)*V/(n:ℝ) := Real.sq_sqrt (by positivity)
  have hNr : (N:ℝ)*V=(n:ℝ)*r^2 := by rw [hrsq]; field_simp
  have hevar : (N:ℝ)*ℓ^2*V≤(n:ℝ) := by
    have hDsq : r^2≤D^2 := by dsimp [D]; nlinarith
    change (N:ℝ)*(D⁻¹)^2*V≤(n:ℝ)
    rw [inv_pow]
    rw [show (N:ℝ)*(D^2)⁻¹*V=((N:ℝ)*V)/(D^2) by ring]
    rw [div_le_iff₀ (sq_pos_of_pos hDp),hNr]
    exact mul_le_mul_of_nonneg_left hDsq hnR.le
  have heexp : Real.exp ((N:ℝ)*ℓ^2*V)≤(3:ℝ)^n := by
    calc
      _ ≤ Real.exp (n:ℝ) := Real.exp_le_exp.mpr hevar
      _ = (Real.exp 1)^n := by simpa only [mul_one] using Real.exp_nat_mul (1:ℝ) n
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le _
  have hfac : (n.factorial:ℝ)≤(n:ℝ)^n := by exact_mod_cast Nat.factorial_le_pow n
  have h2 : (2:ℝ)≤(2:ℝ)^n := by simpa using pow_le_pow_right₀ (a:=(2:ℝ)) (by norm_num) hn
  have hDroot : (n:ℝ)*r=Real.sqrt ((n:ℝ)*(N:ℝ)*V) := by
    symm
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (mul_nonneg hnR.le hrn)).mpr
    rw [mul_pow]
    calc
      (n:ℝ)*(N:ℝ)*V=(n:ℝ)*((N:ℝ)*V) := by ring
      _=(n:ℝ)*((n:ℝ)*r^2) := by rw [hNr]
      _=_ := by ring
  calc
    _ ≤ (n.factorial:ℝ)/ℓ^n*(2*Real.exp ((N:ℝ)*ℓ^2*V)) := hmoment.trans (by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hnexp : Real.exp ((N:ℝ)*(-ℓ)^2*V)=Real.exp ((N:ℝ)*ℓ^2*V) := by rw [neg_sq]
      exact (add_le_add hMGFp.2.1 (hMGFn.2.1.trans_eq hnexp)).trans_eq (by ring))
    _ ≤ (n:ℝ)^n/ℓ^n*(2*(3:ℝ)^n) := mul_le_mul
      (div_le_div_of_nonneg_right hfac (by positivity))
      (mul_le_mul_of_nonneg_left heexp (by norm_num)) (by positivity) (by positivity)
    _ ≤ (n:ℝ)^n/ℓ^n*((2:ℝ)^n*(3:ℝ)^n) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right h2 (by positivity)) (by positivity)
    _ = (6*((n:ℝ)*A+Real.sqrt ((n:ℝ)*(N:ℝ)*V)))^n := by
      rw [←div_pow,←mul_pow,←mul_pow]
      congr 1
      change ((n:ℝ)/(D⁻¹))*(2*3)=6*((n:ℝ)*A+Real.sqrt ((n:ℝ)*(N:ℝ)*V))
      rw [div_inv_eq_mul,←hDroot]
      dsimp [D]; ring
