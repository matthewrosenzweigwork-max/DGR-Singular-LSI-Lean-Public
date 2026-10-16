module

public import Tablet.HeatSemigroup
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section
open MeasureTheory Filter Set UnitAddTorus
open scoped Topology ComplexConjugate
set_option maxHeartbeats 1500000
-- [TABLET NODE: HeatFourierCoefficients]
theorem HeatFourierCoefficients (d : ℕ) (t : ℝ) (ht : 0<t) (k : Fin d→ℤ) :
    (∫x,HeatKernel d t x*(UnitAddTorus.mFourier k x).re) =
      Real.exp (-4*Real.pi^2*t*∑j,(k j:ℝ)^2) ∧
    (∫x,(HeatKernel d t x:ℂ)*UnitAddTorus.mFourier k x) =
      (Real.exp (-4*Real.pi^2*t*∑j,(k j:ℝ)^2):ℂ) := by
-- BODY
  have gaussian_int_summable (c : ℝ) (hc : 0 < c) :
      Summable (fun n : ℤ => Real.exp (-c * (n : ℝ)^2)) := by
    have hn : Summable (fun n : ℕ => Real.exp (-c * (n : ℝ)^2)) := by
      apply Real.summable_exp_nat_mul_of_ge (neg_lt_zero.mpr hc)
      intro n
      exact_mod_cast (show n ≤ n^2 by nlinarith)
    apply summable_int_iff_summable_nat_and_neg.mpr
    constructor
    · simpa using hn
    · simpa using hn

  have gaussian_lattice_summable (d : ℕ) (c : ℝ) (hc : 0 < c) :
      Summable (fun k : Fin d → ℤ => Real.exp (-c * ∑ j, (k j : ℝ)^2)) := by
    induction d with
    | zero => exact (hasSum_fintype _).summable
    | succ d ih =>
      have hs := (gaussian_int_summable c hc).mul_of_nonneg ih
        (fun _ => Real.exp_nonneg _) (fun _ => Real.exp_nonneg _)
      apply (Fin.consEquiv (fun _ : Fin (d+1) => ℤ)).summable_iff.mp
      convert hs using 1
      ext k
      simp only [Function.comp_apply, Fin.consEquiv_apply, Fin.sum_univ_succ,
        Fin.cons_zero, Fin.cons_succ]
      rw [mul_add, Real.exp_add]

  have character_exp (d : ℕ) (k : Fin d → ℤ) (x : UnitAddTorus (Fin d)) :
      UnitAddTorus.mFourier k x = Complex.exp
        ((2 * Real.pi * ∑ j, (k j : ℝ) *
          (AddCircle.equivIco (1 : ℝ) 0 (x j) : ℝ) : ℝ) * Complex.I) := by
    classical
    have hx : x = fun j =>
        ((AddCircle.equivIco (1 : ℝ) 0 (x j) : ℝ) : AddCircle (1 : ℝ)) := by
      ext j
      exact AddCircle.coe_equivIco.symm
    conv_lhs => rw [hx]
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_coe_apply,
      div_one]
    rw [← Complex.exp_sum]
    congr 1
    simp only [Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring

  have cos_eq_character_re (d : ℕ) (k : Fin d → ℤ) (x : UnitAddTorus (Fin d)) :
      Real.cos (2 * Real.pi * ∑ j, (k j : ℝ) *
        (AddCircle.equivIco (1 : ℝ) 0 (x j) : ℝ)) =
          (UnitAddTorus.mFourier k x).re := by
    rw [character_exp, Complex.exp_re]
    simp

  have heat_continuous (d : ℕ) (t : ℝ) (ht : 0 < t) :
      Continuous (HeatKernel d t) := by
    have hc : 0 < 4 * Real.pi^2 * t := by positivity
    have hs := gaussian_lattice_summable d (4 * Real.pi^2 * t) hc
    have he : HeatKernel d t = fun x => ∑' k : Fin d → ℤ,
        Real.exp (-4 * Real.pi^2 * t * ∑ j, (k j : ℝ)^2) *
          (UnitAddTorus.mFourier k x).re := by
      ext x
      simp only [HeatKernel, cos_eq_character_re]
    rw [he]
    apply continuous_tsum (u := fun k : Fin d → ℤ =>
      Real.exp (-4 * Real.pi^2 * t * ∑ j, (k j : ℝ)^2))
    · intro k
      exact continuous_const.mul (Complex.continuous_re.comp (UnitAddTorus.mFourier k).continuous)
    · convert hs using 1 <;> ring_nf
    · intro k x
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      apply mul_le_of_le_one_right (Real.exp_nonneg _)
      exact (Complex.abs_re_le_norm _).trans
        (by simpa only [UnitAddTorus.mFourier_norm] using
          (UnitAddTorus.mFourier k).norm_coe_le_norm x)

  have heat_even (d : ℕ) (t : ℝ) (x : UnitAddTorus (Fin d)) :
      HeatKernel d t (-x) = HeatKernel d t x := by
    classical
    have hneg (k : Fin d → ℤ) :
        UnitAddTorus.mFourier k (-x) = star (UnitAddTorus.mFourier k x) := by
      change (∏ j, fourier (k j) (-x j)) =
        star (∏ j, fourier (k j) (x j))
      rw [star_prod]
      apply Finset.prod_congr rfl
      intro j _
      rw [fourier_apply, smul_neg, fourier_neg']
      rfl
    unfold HeatKernel
    apply tsum_congr
    intro k
    rw [cos_eq_character_re, cos_eq_character_re, hneg]
    rfl

  have volume_eq_haar (d : ℕ) :
      (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d))) =
        MeasureTheory.Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle (T := (1 : ℝ))) := by
    change MeasureTheory.Measure.pi (fun _ : Fin d =>
      (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ)))) = _
    congr 1
    funext j
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp

  have character_mean (d : ℕ) (k : Fin d → ℤ) :
      (∫ x, UnitAddTorus.mFourier k x
        ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d)))) =
          if k = 0 then (1 : ℂ) else 0 := by
    classical
    have h := (orthonormal_iff_ite.mp (UnitAddTorus.orthonormal_mFourier (d := Fin d))) (-k) 0
    simp only [ContinuousMap.inner_toLp, ← UnitAddTorus.mFourier_neg,
      ← UnitAddTorus.mFourier_add, neg_neg, zero_add, neg_eq_zero] at h
    rw [volume_eq_haar]
    exact h

  have re_mean (d : ℕ) (k : Fin d→ℤ) : (∫x,(mFourier k x).re) = if k=0 then 1 else 0 := by
    have hi : Integrable (mFourier k) (volume : Measure (UnitAddTorus (Fin d))) :=
      (mFourier k).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hh := integral_re hi
    rw [character_mean] at hh
    split_ifs at hh ⊢ <;>simpa using hh

  have re_product_mean (d : ℕ) (j k : Fin d→ℤ) :
      (∫x,(mFourier j x).re*(mFourier k x).re) =
        ((if j=k then (1:ℝ) else 0)+(if j=-k then (1:ℝ) else 0))/2 := by
    have hpoint x : (mFourier j x).re*(mFourier k x).re =
        ((mFourier (j+k) x).re+(mFourier (j-k) x).re)/2 := by
      rw [sub_eq_add_neg]
      simp only [mFourier_add,mFourier_neg,ContinuousMap.mul_apply,ContinuousMap.star_apply,
        Complex.mul_re,Complex.conj_re,Complex.conj_im]
      ring
    have hj : Integrable (fun x=>(mFourier (j+k) x).re) volume :=
      (Complex.continuous_re.comp (mFourier (j+k)).continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hk : Integrable (fun x=>(mFourier (j-k) x).re) volume :=
      (Complex.continuous_re.comp (mFourier (j-k)).continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    simp_rw [hpoint]
    rw [integral_div,integral_add hj hk,re_mean,re_mean]
    simp only [sub_eq_zero,add_eq_zero_iff_eq_neg]
    ring

  have heat_coefficient (d : ℕ) (t : ℝ) (ht : 0<t) (k : Fin d→ℤ) :
      (∫x,HeatKernel d t x*(mFourier k x).re) =
        Real.exp (-4*Real.pi^2*t*∑j,(k j:ℝ)^2) := by
    classical
    haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1:ℝ))) := by
      rw [AddCircle.volume_eq_smul_haarAddCircle];simp;infer_instance
    let b := fun j:Fin d→ℤ=>Real.exp (-4*Real.pi^2*t*∑i,(j i:ℝ)^2)
    let F := fun (j:Fin d→ℤ) (x:UnitAddTorus (Fin d))=>b j*(mFourier j x).re*(mFourier k x).re
    have hs : Summable b := by
      convert gaussian_lattice_summable d (4*Real.pi^2*t) (by positivity) using 1
      dsimp [b];ring_nf
    have hchar (j : Fin d→ℤ) (x : UnitAddTorus (Fin d)) : |(mFourier j x).re|≤1 :=
      (Complex.abs_re_le_norm _).trans (by simpa only [mFourier_norm] using (mFourier j).norm_coe_le_norm x)
    have hi j : Integrable (F j) volume :=
      ((continuous_const.mul (Complex.continuous_re.comp (mFourier j).continuous)).mul
        (Complex.continuous_re.comp (mFourier k).continuous)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hb j x : ‖F j x‖≤b j := by
      dsimp [F]
      rw [abs_mul,abs_mul,abs_of_pos (show 0<b j from Real.exp_pos _)]
      exact (mul_le_of_le_one_right (mul_nonneg (Real.exp_pos _).le (abs_nonneg _)) (hchar k x)).trans
        (mul_le_of_le_one_right (Real.exp_pos _).le (hchar j x))
    have hsi : Summable (fun j=>∫x,‖F j x‖) := by
      apply hs.of_nonneg_of_le
      · intro j;exact integral_nonneg fun _=>norm_nonneg _
      · intro j
        exact (integral_mono (hi j).norm (integrable_const _) (hb j)).trans_eq (by simp [b,neg_mul])
    have he : (fun x=>HeatKernel d t x*(mFourier k x).re)=fun x=>∑'j:Fin d→ℤ,F j x := by
      funext x
      unfold HeatKernel
      simp_rw [cos_eq_character_re]
      exact (tsum_mul_right).symm
    rw [he,←integral_tsum_of_summable_integral_norm hi hsi]
    have hterm j : (∫x,F j x) = ((if j=k then b k else 0)+(if j=-k then b (-k) else 0))/2 := by
      dsimp [F]
      simp_rw [mul_assoc]
      rw [integral_const_mul,re_product_mean]
      have h1 : b j*(if j=k then (1:ℝ) else 0)=if j=k then b k else 0 := by
        split_ifs with h
        · subst j; simp
        · simp
      have h2 : b j*(if j=-k then (1:ℝ) else 0)=if j=-k then b (-k) else 0 := by
        split_ifs with h
        · subst j; simp
        · simp
      rw [mul_div,mul_add,h1,h2]
    simp_rw [hterm]
    have hleft : Summable (fun j:Fin d→ℤ=>if j=k then b k else 0) := (hasSum_ite_eq _ _).summable
    have hright : Summable (fun j:Fin d→ℤ=>if j=-k then b (-k) else 0) := (hasSum_ite_eq _ _).summable
    rw [tsum_div_const,hleft.tsum_add hright]
    simp only [tsum_ite_eq]
    have heven : b (-k)=b k := by simp [b]
    rw [heven]
    dsimp [b]
    ring

  have char_inv {d : ℕ} (k : Fin d → ℤ) (x : UnitAddTorus (Fin d)) :
      mFourier k (-x) = conj (mFourier k x) := by
    simp only [mFourier, ContinuousMap.coe_mk, Pi.neg_apply, fourier_apply, smul_neg,
      fourier_neg', map_prod]

  have char_norm {d : ℕ} (k : Fin d → ℤ) (x : UnitAddTorus (Fin d)) : ‖mFourier k x‖ = 1 := by
    simp only [mFourier, ContinuousMap.coe_mk, norm_prod, fourier_apply, Circle.norm_coe,
      Finset.prod_const_one]

  let coef {d : ℕ} (f : UnitAddTorus (Fin d) → ℂ) (k : Fin d → ℤ) :=
    ∫ x, mFourier k x * f x

  have coef_integrable {d : ℕ} (f : UnitAddTorus (Fin d) → ℂ) (hi : Integrable f volume) (k : Fin d → ℤ) :
      Integrable (fun x => mFourier k x * f x) volume := by
    exact hi.bdd_mul (mFourier k).continuous.measurable.aestronglyMeasurable
      (Eventually.of_forall fun x => (char_norm k x).le)

  have coef_real {d : ℕ} (K : UnitAddTorus (Fin d) → ℝ) (hi : Integrable K volume)
      (he : ∀ x, K (-x) = K x) (k : Fin d → ℤ) :
      coef (fun x => (K x : ℂ)) k = (∫ x, K x * (mFourier k x).re : ℝ) := by
    have hic : Integrable (fun x => (K x : ℂ)) volume := Complex.ofRealCLM.integrable_comp hi
    have hreal : conj (coef (fun x => (K x : ℂ)) k) = coef (fun x => (K x : ℂ)) k := by
      unfold coef
      rw [← integral_conj]
      calc
        _ = ∫ x, mFourier k (-x) * (K (-x) : ℂ) := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by dsimp; simp only [map_mul, char_inv, he, Complex.conj_ofReal]
        _ = _ := integral_neg_eq_self (fun x => mFourier k x * (K x : ℂ)) volume
    have hre : (coef (fun x => (K x : ℂ)) k).re = ∫ x, K x * (mFourier k x).re := by
      unfold coef
      change RCLike.re (∫ x, mFourier k x * (K x : ℂ)) = _
      rw [← integral_re (coef_integrable _ hic k)]
      congr 1
      funext x
      change (mFourier k x * (K x : ℂ)).re = K x * (mFourier k x).re
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      ring
    apply Complex.ext
    · simpa using hre
    · simpa using Complex.conj_eq_iff_im.mp hreal
  refine ⟨heat_coefficient d t ht k,?_⟩
  have hi : Integrable (HeatKernel d t) volume :=
    (heat_continuous d t ht).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hh := coef_real (HeatKernel d t) hi (heat_even d t) k
  rw [heat_coefficient d t ht k] at hh
  simpa [coef,mul_comm] using hh
