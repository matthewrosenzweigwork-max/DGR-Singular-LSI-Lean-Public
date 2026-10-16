import Tablet.Preamble
open MeasureTheory
-- [TABLET NODE: GLZBoundedMomentCorrection]
theorem GLZBoundedMomentCorrection {Ω Λ : Type*} [MeasurableSpace Ω] [Fintype Λ]
    (μ : Measure Ω) (f : Λ → Ω → ℝ) (a b : ℝ) (ha : 0≤a) (hb : 0≤b)
    (hfi : ∀i,Integrable (f i) μ) (hfn : ∀i,∀ᵐ x ∂μ,0≤f i x)
    (hfb : ∀i,∀ᵐ x ∂μ,f i x≤a)
    (hmean : (∑i,∫x,f i x ∂μ)≤b) (m : ℕ) (hm : 1≤m) (k : ℕ) :
    (∀i,Integrable (fun x=>(f i x)^m) μ) ∧
    (m:ℝ)^((k+1)*m)*(∑i,∫x,(f i x)^m ∂μ)≤
      (2^k:ℝ)^m*(((m:ℝ)*b)^m+((m:ℝ)^(k+1)*a)^m) := by
-- BODY
  have bounded_moment_interpolation (x a b : ℝ) (hx : 0≤x) (ha : 0≤a) (hb : 0≤b)
      (k n : ℕ) :
      x^((k+1)*(n+1))*a^n*b≤
        x^k*((x*b)^(n+1)+(x^(k+1)*a)^(n+1)) := by
    by_cases hlo : b≤x^k*a
    · calc
        _≤x^((k+1)*(n+1))*a^n*(x^k*a) := mul_le_mul_of_nonneg_left hlo (by positivity)
        _=x^k*(x^(k+1)*a)^(n+1) := by
          rw[mul_pow,←pow_mul,pow_succ a n]
          ring
        _≤_ := by
          have hp : 0≤(x*b)^(n+1) := by positivity
          exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hp) (pow_nonneg hx k)
    · have hhi : x^k*a≤b := (lt_of_not_ge hlo).le
      have hp:=pow_le_pow_left₀ (by positivity : 0≤x^k*a) hhi n
      calc
        _=x^(k+n+1)*(x^k*a)^n*b := by
          rw[mul_pow,←pow_mul]
          have he:x^((k+1)*(n+1))=x^(k+n+1)*x^(k*n) := by
            rw[←pow_add]
            congr 1
            ring
          rw[he]
          ring
        _≤x^(k+n+1)*b^n*b := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp (pow_nonneg hx _)) hb
        _=x^k*(x*b)^(n+1) := by
          rw[mul_pow,pow_succ b n]
          have he:x^(k+n+1)=x^k*x^(n+1) := by
            rw[←pow_add]
            congr 1
          rw[he]
          ring
        _≤_ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (pow_nonneg hx k)
  have bounded_glz_correction (m : ℕ) (hm : 1≤m) (a b : ℝ) (ha : 0≤a) (hb : 0≤b) (k : ℕ) :
      (m:ℝ)^((k+1)*m)*a^(m-1)*b≤
        (2^k:ℝ)^m*(((m:ℝ)*b)^m+((m:ℝ)^(k+1)*a)^m) := by
    have hpred : (m-1)+1=m := by omega
    have hi:=bounded_moment_interpolation (m:ℝ) a b (Nat.cast_nonneg _) ha hb k (m-1)
    rw[hpred] at hi
    have hm2 : (m:ℝ)≤(2:ℝ)^m := by exact_mod_cast (Nat.lt_two_pow_self (n:=m)).le
    have hk : (m:ℝ)^k≤(2^k:ℝ)^m := by
      have hh:=pow_le_pow_left₀ (Nat.cast_nonneg m) hm2 k
      simpa only[←pow_mul,Nat.mul_comm] using hh
    exact hi.trans (mul_le_mul_of_nonneg_right hk (by positivity))
  classical
  have hp (i:Λ) : ∀ᵐ x ∂μ,0≤(f i x)^m ∧ (f i x)^m≤a^(m-1)*f i x := by
    filter_upwards[hfn i,hfb i] with x hn hx
    refine ⟨pow_nonneg hn _,?_⟩
    have hh:=mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hn hx (m-1)) hn
    have hpred : (m-1)+1=m := by omega
    rwa[←pow_succ,hpred] at hh
  have hi (i:Λ) : Integrable (fun x=>(f i x)^m) μ :=
    ((hfi i).const_mul (a^(m-1))).mono' ((hfi i).aestronglyMeasurable.pow m) (by
      filter_upwards[hp i] with x hx
      rw[Real.norm_eq_abs,abs_of_nonneg hx.1]
      exact hx.2)
  have hh : (∑i,∫x,(f i x)^m ∂μ)≤a^(m-1)*b := by
    calc
      _≤∑i,a^(m-1)*(∫x,f i x ∂μ) := Finset.sum_le_sum fun i _=>by
        have he:=integral_mono_ae (hi i) ((hfi i).const_mul (a^(m-1))) ((hp i).mono fun x hx=>hx.2)
        rwa[integral_const_mul] at he
      _=a^(m-1)*(∑i,∫x,f i x ∂μ) := (Finset.mul_sum _ _ _).symm
      _≤_ := mul_le_mul_of_nonneg_left hmean (pow_nonneg ha _)
  refine ⟨hi,?_⟩
  calc
    _≤(m:ℝ)^((k+1)*m)*(a^(m-1)*b) := mul_le_mul_of_nonneg_left hh (by positivity)
    _≤_ := by simpa only[mul_assoc] using bounded_glz_correction m hm a b ha hb k
