module

public import Tablet.IndependentNonnegativeMomentBound
public import Tablet.IndependentCenteredEvenMoment

@[expose] public section
open MeasureTheory
universe u
-- [TABLET NODE: IndependentRosenthalEvenMoment]
theorem IndependentRosenthalEvenMoment {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ) (Z : Fin N → Ω → ℝ)
    (hZ : ∀ i, Measurable (Z i)) (A : ℝ) (hA : 0 ≤ A)
    (hb : ∀ i x, |Z i x| ≤ A) (hc : ∀ i, ∫ x, Z i x ∂μ = 0)
    (m : ℕ) (hm : 1 ≤ m) (V T : ℝ) (hV : 0 ≤ V) (hT : 0 ≤ T)
    (hv : (∑ i, ∫ x, (Z i x)^2 ∂μ) ≤ V)
    (ht : (∑ i, ∫ x, (Z i x)^(2*m) ∂μ) ≤ T^(2*m)) :
    (∫ X : Fin N → Ω, (∑ i, Z i (X i))^(2*m) ∂Measure.pi (fun _ : Fin N => μ)) ≤
      (24 * Real.exp 1 * (m : ℝ) * V + 192 * (m : ℝ)^2 * T^2)^m := by
-- BODY
  classical
  have bi {Λ : Type u} [MeasurableSpace Λ] (ξ : Measure Λ) [IsProbabilityMeasure ξ]
      (f : Λ → ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀ x, |f x| ≤ C) : Integrable f ξ := by
    apply Integrable.of_bound hf.aestronglyMeasurable C
    exact Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x
  let ξ := μ.prod μ
  let W (i : Fin N) (v : Ω × Ω) := (Z i v.1-Z i v.2)^2
  have hZm (i : Fin N) (k : ℕ) : Measurable (fun x => (Z i x)^k) := (hZ i).pow_const _
  have hZi (i : Fin N) (k : ℕ) : Integrable (fun x => (Z i x)^k) μ :=
    bi μ _ (hZm i k) (A^k) (fun x => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hb i x) _)
  have hWm (i : Fin N) : Measurable (W i) :=
    (((hZ i).comp measurable_fst).sub ((hZ i).comp measurable_snd)).pow_const 2
  have hWn (i : Fin N) (v : Ω × Ω) : 0 ≤ W i v := sq_nonneg _
  have hWb (i : Fin N) (v : Ω × Ω) : W i v ≤ 4*A^2 := by
    have h := (abs_sub (Z i v.1) (Z i v.2)).trans (add_le_add (hb i _) (hb i _))
    have hs := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs] at hs
    dsimp [W]; nlinarith
  have hWi (i : Fin N) (k : ℕ) : Integrable (fun v => (W i v)^k) ξ :=
    bi ξ _ ((hWm i).pow_const k) ((4*A^2)^k) (fun v => by
      rw [abs_pow, abs_of_nonneg (hWn i v)]; exact pow_le_pow_left₀ (hWn i v) (hWb i v) k)
  have hfsti (i : Fin N) (k : ℕ) : Integrable (fun v : Ω × Ω => (Z i v.1)^k) ξ :=
    (hZi i k).comp_fst μ
  have hsndi (i : Fin N) (k : ℕ) : Integrable (fun v : Ω × Ω => (Z i v.2)^k) ξ :=
    (hZi i k).comp_snd μ
  have hvar (i : Fin N) : (∫v,W i v ∂ξ)=2*(∫x,(Z i x)^2 ∂μ) := by
    have hmul : Integrable (fun v : Ω × Ω => Z i v.1 * Z i v.2) ξ :=
      by simpa only [pow_one] using (hZi i 1).mul_prod (hZi i 1)
    have he : W i = fun v => (Z i v.1)^2+(Z i v.2)^2-2*(Z i v.1*Z i v.2) := by
      funext v; dsimp [W]; ring
    rw [he]
    have hiEq := integral_sub ((hfsti i 2).add (hsndi i 2)) (hmul.const_mul 2)
    simp only [Pi.add_apply] at hiEq
    rw [hiEq, integral_add (hfsti i 2) (hsndi i 2), integral_const_mul]
    change _ - 2*(∫v,Z i v.1*Z i v.2 ∂μ.prod μ) = _
    rw [integral_prod_mul, hc]
    simp only [mul_zero, zero_mul, sub_zero]
    have hfst : (∫v : Ω × Ω,(Z i v.1)^2 ∂ξ)=∫x,(Z i x)^2 ∂μ := by
      change (∫v : Ω × Ω,(Z i v.1)^2 ∂μ.prod μ)=_
      rw [integral_prod _ (hfsti i 2)]; simp
    have hsnd : (∫v : Ω × Ω,(Z i v.2)^2 ∂ξ)=∫x,(Z i x)^2 ∂μ := by
      change (∫v : Ω × Ω,(Z i v.2)^2 ∂μ.prod μ)=_
      rw [integral_prod _ (hsndi i 2)]; simp
    rw [hfst,hsnd]; ring
  have heven : Even (2*m) := ⟨m, by omega⟩
  have hpoint (i : Fin N) (v : Ω × Ω) : (W i v)^m ≤ (4:ℝ)^m*((Z i v.1)^(2*m)+(Z i v.2)^(2*m)) := by
    have h := heven.add_pow_le (a:=Z i v.1) (b:=-(Z i v.2))
    have hp : (2:ℝ)^(2*m-1) ≤ (2:ℝ)^(2*m) := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
    have hpn : 0 ≤ (Z i v.1)^(2*m)+(Z i v.2)^(2*m) :=
      add_nonneg (heven.pow_nonneg _) (heven.pow_nonneg _)
    have hq := h.trans (mul_le_mul_of_nonneg_right hp (by simpa only [heven.neg_pow] using hpn))
    have hfour : (2:ℝ)^(2*m)=(4:ℝ)^m := by rw [pow_mul]; norm_num
    simpa only [W,sub_eq_add_neg,←pow_mul,heven.neg_pow,hfour] using hq
  have hwmean (i : Fin N) : (∫v,(W i v)^m ∂ξ) ≤ 2*(4:ℝ)^m*(∫x,(Z i x)^(2*m) ∂μ) := by
    have hi := ((hfsti i (2*m)).add (hsndi i (2*m))).const_mul ((4:ℝ)^m)
    calc
      _ ≤ ∫v,(4:ℝ)^m*((Z i v.1)^(2*m)+(Z i v.2)^(2*m)) ∂ξ :=
        integral_mono (hWi i m) hi (hpoint i)
      _ = _ := by
        rw [integral_const_mul,integral_add (hfsti i (2*m)) (hsndi i (2*m))]
        have hfst : (∫v : Ω × Ω,(Z i v.1)^(2*m) ∂ξ)=∫x,(Z i x)^(2*m) ∂μ := by
          change (∫v : Ω × Ω,(Z i v.1)^(2*m) ∂μ.prod μ)=_
          rw [integral_prod _ (hfsti i (2*m))]; simp
        have hsnd : (∫v : Ω × Ω,(Z i v.2)^(2*m) ∂ξ)=∫x,(Z i x)^(2*m) ∂μ := by
          change (∫v : Ω × Ω,(Z i v.2)^(2*m) ∂μ.prod μ)=_
          rw [integral_prod _ (hsndi i (2*m))]; simp
        rw [hfst,hsnd]; ring
  have hms : (∑i,∫v,(W i v)^m ∂ξ) ≤ (8*T^2)^m := by
    calc
      _ ≤ ∑i,2*(4:ℝ)^m*(∫x,(Z i x)^(2*m) ∂μ) := Finset.sum_le_sum fun i _ => hwmean i
      _ = 2*(4:ℝ)^m*(∑i,∫x,(Z i x)^(2*m) ∂μ) := by rw [Finset.mul_sum]
      _ ≤ 2*(4:ℝ)^m*T^(2*m) := mul_le_mul_of_nonneg_left ht (by positivity)
      _ ≤ (8*T^2)^m := by
        have h2 : (2:ℝ) ≤ (2:ℝ)^m := by
          simpa using pow_le_pow_right₀ (a:=(2:ℝ)) (by norm_num) hm
        calc
          _ ≤ (2:ℝ)^m*(4:ℝ)^m*T^(2*m) := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h2 (by positivity)) (by positivity)
          _ = _ := by rw [pow_mul,←mul_pow]; norm_num; rw [mul_pow]
  let ν := Measure.pi (fun _ : Fin N => ξ)
  let F (X : Fin N → Ω × Ω) := ∑i,W i (X i)
  let K := ∫X,(F X)^m ∂ν
  let L := K^((m:ℝ)⁻¹)
  have hK : 0≤K := integral_nonneg fun X => pow_nonneg (Finset.sum_nonneg fun i _ => hWn i _) _
  have hL : 0≤L := Real.rpow_nonneg hK _
  have hroot : K=L^m := (Real.rpow_inv_natCast_pow hK (by omega : m≠0)).symm
  have hpos := IndependentNonnegativeMomentBound ξ N W hWm (4*A^2) (by positivity)
    hWn hWb m (by omega) L (8*T^2) hL (by positivity) hroot hms
  have hsum : (∑i,∫v,W i v ∂ξ) ≤ 2*V := by
    simp_rw [hvar]; rw [←Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hv (by norm_num)
  have hLs : L ≤ 4*Real.exp 1*V+32*(m:ℝ)*T^2 := by
    have hmR : 1≤(m:ℝ) := by exact_mod_cast hm
    have hh := hpos.trans (add_le_add (mul_le_mul_of_nonneg_left hsum (by positivity : 0≤2*Real.exp 1)) (le_refl (2*((m:ℝ)+1)*(8*T^2))))
    nlinarith [sq_nonneg T,Real.exp_pos 1]
  have hsym := IndependentCenteredEvenMoment N (fun _ : Fin N => μ) Z hZ ⟨A,hb⟩ hc m hm
  calc
    _ ≤ (6*(m:ℝ))^m*K := hsym
    _ = (6*(m:ℝ))^m*L^m := by rw [hroot]
    _ ≤ (6*(m:ℝ))^m*(4*Real.exp 1*V+32*(m:ℝ)*T^2)^m :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL hLs _) (by positivity)
    _ = _ := by rw [←mul_pow]; congr 1; ring
