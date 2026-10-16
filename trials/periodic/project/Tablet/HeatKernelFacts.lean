import Tablet.HeatSemigroup
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Tablet.Preamble
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
open scoped Topology
open MeasureTheory
-- [TABLET NODE: HeatKernelFacts]
theorem HeatKernelFacts (d : ℕ) (t : ℝ) (ht : 0 < t) :
    Continuous (HeatKernel d t) ∧
    (∀ x, 0 ≤ HeatKernel d t x) ∧
    (∀ x, HeatKernel d t (-x) = HeatKernel d t x) ∧
    (∫ x, HeatKernel d t x ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d)))) = 1 ∧
    (∀ x, HeatKernel d t x =
      Real.rpow (4 * Real.pi * t) (-(d : ℝ) / 2) *
        ∑' n : Fin d → ℤ, Real.exp (-(∑ j,
          ((AddCircle.equivIco (1 : ℝ) 0 (x j) : ℝ) + (n j : ℝ)) ^ 2) / (4 * t))) ∧
    (∀ (u : ℝ), 0 < u → ∀ x,
      HeatSemigroup d t (HeatKernel d u) x = HeatKernel d (t + u) x) := by
-- BODY
  classical
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

  have heat_mass (d : ℕ) (t : ℝ) (ht : 0 < t) :
      (∫ x, HeatKernel d t x
        ∂(volume : Measure (UnitAddTorus (Fin d)))) = 1 := by
    classical
    haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
      rw [AddCircle.volume_eq_smul_haarAddCircle]
      simp
      infer_instance
    haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) :=
      inferInstance
    let b := fun k : Fin d → ℤ => Real.exp (-4 * Real.pi^2 * t * ∑ j, (k j : ℝ)^2)
    let F := fun (k : Fin d → ℤ) (x : UnitAddTorus (Fin d)) =>
      b k * (UnitAddTorus.mFourier k x).re
    have hs : Summable b := by
      convert gaussian_lattice_summable d (4 * Real.pi^2 * t) (by positivity) using 1
      dsimp [b]
      ring_nf
    have hc (k : Fin d → ℤ) : Continuous (F k) :=
      continuous_const.mul (Complex.continuous_re.comp (UnitAddTorus.mFourier k).continuous)
    have hi (k : Fin d → ℤ) : Integrable (F k) volume :=
      (hc k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hb (k : Fin d → ℤ) (x : UnitAddTorus (Fin d)) : ‖F k x‖ ≤ b k := by
      change |b k * (UnitAddTorus.mFourier k x).re| ≤ b k
      rw [abs_mul, abs_of_pos (show 0 < b k from Real.exp_pos _)]
      apply mul_le_of_le_one_right (Real.exp_nonneg _)
      exact (Complex.abs_re_le_norm _).trans
        (by simpa only [UnitAddTorus.mFourier_norm] using
          (UnitAddTorus.mFourier k).norm_coe_le_norm x)
    have hsi : Summable (fun k => ∫ x, ‖F k x‖ ∂volume) := by
      apply hs.of_nonneg_of_le
      · intro k
        exact integral_nonneg (fun _ => norm_nonneg _)
      · intro k
        calc
          _ ≤ ∫ _ : UnitAddTorus (Fin d), b k ∂volume :=
            integral_mono (hi k).norm (integrable_const _) (hb k)
          _ = b k := by simp
    have he : HeatKernel d t = fun x => ∑' k : Fin d → ℤ, F k x := by
      ext x
      simp only [HeatKernel, cos_eq_character_re, F, b]
    rw [he, ← integral_tsum_of_summable_integral_norm hi hsi]
    have hm (k : Fin d → ℤ) :
        (∫ x, F k x ∂volume) = if k = 0 then 1 else 0 := by
      have hci : Integrable (fun x => UnitAddTorus.mFourier k x) volume :=
        (UnitAddTorus.mFourier k).continuous.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      dsimp [F]
      rw [integral_const_mul]
      have hri : (∫ x, (UnitAddTorus.mFourier k x).re ∂volume) =
          (∫ x, UnitAddTorus.mFourier k x ∂volume).re := by
        simpa using integral_re hci
      rw [hri, character_mean]
      by_cases hk : k = 0
      · subst k
        simp [b]
      · simp [hk]
    simp_rw [hm]
    simp

  have scalar_complex_poisson (t x : ℝ) (ht : 0 < t) :
      (∑' n : ℤ, (Real.exp (-4*Real.pi^2*t*(n:ℝ)^2):ℂ)*
        Complex.exp ((2*Real.pi*x*(n:ℝ):ℝ)*Complex.I)) =
      (((4*Real.pi*t)^(-(1:ℝ)/2):ℝ):ℂ) *
        (∑' n : ℤ, (Real.exp (-((n:ℝ)-x)^2/(4*t)):ℂ)) := by
    let A := 4*Real.pi*t
    have hA : 0 < A := by dsimp [A]; positivity
    let f : ℤ → ℂ := fun n => Complex.exp
      (-Real.pi*(A:ℂ)*(n:ℂ)^2+2*Real.pi*((x:ℂ)*Complex.I)*(n:ℂ))
    have he (n : ℤ) :
        -Real.pi*(A:ℂ)*(n:ℂ)^2+2*Real.pi*((x:ℂ)*Complex.I)*(n:ℂ) =
        ((-4*Real.pi^2*t*(n:ℝ)^2 : ℝ):ℂ)+((2*Real.pi*x*(n:ℝ):ℝ):ℂ)*Complex.I := by
      dsimp [A]
      push_cast
      ring
    have hf : Summable f := by
      apply Summable.of_norm
      have hs := gaussian_int_summable (4*Real.pi^2*t) (by positivity)
      convert hs using 1
      ext n
      rw [Complex.norm_exp, he]
      simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
        Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
      congr 1
      ring
    have hr (n : ℤ) :
        -Real.pi/(A:ℂ)*((n:ℂ)+Complex.I*((x:ℂ)*Complex.I))^2 =
        ((-((n:ℝ)-x)^2/(4*t):ℝ):ℂ) := by
      dsimp [A]
      push_cast
      field_simp
      simp only [Complex.I_sq]
      ring
    have h := Complex.tsum_exp_neg_quadratic
      (a := (A:ℂ)) (by simpa using hA) ((x:ℂ)*Complex.I)
    have hpow : (A:ℂ)^(1/2:ℂ) = ((A^(1/2:ℝ):ℝ):ℂ) := by
      convert (Complex.ofReal_cpow hA.le (1/2:ℝ)).symm using 1 <;> norm_num
    simp_rw [hr, ← Complex.ofReal_exp] at h
    rw [hpow, ← Complex.ofReal_tsum] at h
    have hcoeff : 1 / ((A^(1/2:ℝ):ℝ):ℂ) = ((1/A^(1/2:ℝ):ℝ):ℂ) :=
      (Complex.ofReal_div 1 _).symm
    rw [hcoeff] at h
    have hc : (4*Real.pi*t)^(-(1:ℝ)/2) = 1/A^(1/2:ℝ) := by
      change A^(-(1:ℝ)/2) = _
      rw [show -(1:ℝ)/2 = -(1/2:ℝ) by ring,Real.rpow_neg hA.le]
      simp
    rw [hc]
    simp_rw [he,Complex.exp_add,← Complex.ofReal_exp] at h
    rw [Complex.ofReal_tsum] at h
    exact h

  have fin_product_tsum (d : ℕ) (f : Fin d → ℤ → ℂ)
      (hf : ∀ j, Summable (fun n => ‖f j n‖)) :
      Summable (fun k : Fin d → ℤ => ‖∏ j, f j (k j)‖) ∧
        (∑' k : Fin d → ℤ, ∏ j, f j (k j)) = ∏ j, ∑' n, f j n := by
    induction d with
    | zero => simp; exact (hasSum_fintype _).summable
    | succ d ih =>
      obtain ⟨hs,he⟩ := ih (fun j => f j.succ) (fun j => hf j.succ)
      let e := Fin.consEquiv (fun _ : Fin (d+1) => ℤ)
      have hn := (hf 0).mul_norm hs
      have hform (k : ℤ × (Fin d → ℤ)) :
          (∏ j, f j (e k j)) = f 0 k.1*(∏ j, f j.succ (k.2 j)) := by
        simp [e,Fin.prod_univ_succ]
      constructor
      · apply e.summable_iff.mp
        change Summable (fun k : ℤ × (Fin d → ℤ) => ‖∏ j, f j (e k j)‖)
        simp_rw [hform]
        exact hn
      · rw [← e.tsum_eq (fun k => ∏ j, f j (k j))]
        simp_rw [hform]
        rw [← tsum_mul_tsum_of_summable_norm (hf 0) hs,he,Fin.prod_univ_succ]

  have shifted_gaussian_summable (t x : ℝ) (ht : 0 < t) :
      Summable (fun n : ℤ => Real.exp (-((n:ℝ)-x)^2/(4*t))) := by
    have hs := (gaussian_int_summable (1/(8*t)) (by positivity)).mul_left
      (Real.exp (x^2/(4*t)))
    apply Summable.of_nonneg_of_le (fun n => Real.exp_nonneg _) (fun n => ?_) hs
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hsq := sq_nonneg ((n:ℝ)-2*x)
    have ht8 : 0 < 8*t := by positivity
    field_simp
    nlinarith

  have spectral_scalar_norm_summable (t x : ℝ) (ht : 0 < t) :
      Summable (fun n : ℤ => ‖(Real.exp (-4*Real.pi^2*t*(n:ℝ)^2):ℂ)*
        Complex.exp ((2*Real.pi*x*(n:ℝ):ℝ)*Complex.I)‖) := by
    have hs := gaussian_int_summable (4*Real.pi^2*t) (by positivity)
    convert hs using 1
    ext n
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Complex.norm_exp]
    simp

  have heat_poisson_minus (d : ℕ) (t : ℝ) (ht : 0 < t) (x : UnitAddTorus (Fin d)) :
      HeatKernel d t x = (4*Real.pi*t)^(-(d:ℝ)/2)*
        ∑' n : Fin d → ℤ, Real.exp (-(∑ j,
          ((n j:ℝ)-(AddCircle.equivIco (1:ℝ) 0 (x j):ℝ))^2)/(4*t)) := by
    classical
    let y := fun j => (AddCircle.equivIco (1:ℝ) 0 (x j):ℝ)
    let f := fun j (n:ℤ) => (Real.exp (-4*Real.pi^2*t*(n:ℝ)^2):ℂ)*
      Complex.exp ((2*Real.pi*y j*(n:ℝ):ℝ)*Complex.I)
    let g := fun j (n:ℤ) => (Real.exp (-((n:ℝ)-y j)^2/(4*t)):ℂ)
    have hf := fin_product_tsum d f (fun j => spectral_scalar_norm_summable t (y j) ht)
    have hg := fin_product_tsum d g (fun j => by
      simpa only [g,Complex.norm_real,Real.norm_eq_abs,Real.abs_exp] using
        shifted_gaussian_summable t (y j) ht)
    have he (k:Fin d→ℤ) : (∏ j, f j (k j)) =
        (Real.exp (-4*Real.pi^2*t*∑ j,(k j:ℝ)^2):ℂ)*
          Complex.exp ((2*Real.pi*∑ j,y j*(k j:ℝ):ℝ)*Complex.I) := by
      simp only [f,Finset.prod_mul_distrib]
      rw [← Complex.ofReal_prod,← Real.exp_sum,← Complex.exp_sum]
      congr 2
      · congr 1
        rw [Finset.mul_sum]
      · simp only [Complex.ofReal_mul,Complex.ofReal_sum,Finset.sum_mul,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
    have hge (k:Fin d→ℤ) : (∏ j, g j (k j)) =
        (Real.exp (-(∑ j,((k j:ℝ)-y j)^2)/(4*t)):ℂ) := by
      simp only [g]
      rw [← Complex.ofReal_prod,← Real.exp_sum]
      congr 2
      rw [← Finset.sum_div,← Finset.sum_neg_distrib]
    have hc : (∏ _j : Fin d, (((4*Real.pi*t)^(-(1:ℝ)/2):ℝ):ℂ)) =
        (((4*Real.pi*t)^(-(d:ℝ)/2):ℝ):ℂ) := by
      rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← Complex.ofReal_pow]
      congr 1
      rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity : 0 ≤ 4*Real.pi*t)]
      congr 1
      ring
    have hsum : (∑' k : Fin d → ℤ, ∏ j, f j (k j)) =
        (((4*Real.pi*t)^(-(d:ℝ)/2):ℝ):ℂ)*(∑' k : Fin d → ℤ, ∏ j,g j (k j)) := by
      rw [hf.2]
      have hsc (j : Fin d) : (∑' n,f j n)=
          (((4*Real.pi*t)^(-(1:ℝ)/2):ℝ):ℂ)*(∑' n,g j n) :=
        scalar_complex_poisson t (y j) ht
      simp_rw [hsc]
      rw [Finset.prod_mul_distrib,hc,← hg.2]
    have hr := congrArg Complex.re hsum
    rw [Complex.re_tsum hf.1.of_norm] at hr
    simp_rw [he,hge] at hr
    rw [← Complex.ofReal_tsum] at hr
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,
      Complex.exp_re,Complex.exp_im,Complex.mul_im,Complex.mul_re,Complex.I_re,
      Complex.I_im,zero_mul,add_zero,zero_add,mul_one,Real.exp_zero,one_mul] at hr
    change HeatKernel d t x = _
    simpa only [HeatKernel,y,mul_comm] using hr

  have heat_poisson (d : ℕ) (t : ℝ) (ht : 0 < t) (x : UnitAddTorus (Fin d)) :
      HeatKernel d t x = (4*Real.pi*t)^(-(d:ℝ)/2)*
        ∑' n : Fin d → ℤ, Real.exp (-(∑ j,
          ((AddCircle.equivIco (1:ℝ) 0 (x j):ℝ)+(n j:ℝ))^2)/(4*t)) := by
    rw [heat_poisson_minus d t ht x]
    congr 1
    rw [← (Equiv.neg (Fin d → ℤ)).tsum_eq
      (fun n : Fin d → ℤ => Real.exp (-(∑ j,
        ((AddCircle.equivIco (1:ℝ) 0 (x j):ℝ)+(n j:ℝ))^2)/(4*t)))]
    apply tsum_congr
    intro n
    simp only [Equiv.neg_apply,Pi.neg_apply,Int.cast_neg]
    congr 3
    apply Finset.sum_congr rfl
    intro j _
    ring

  have heat_nonnegative (d : ℕ) (t : ℝ) (ht : 0 < t) (x : UnitAddTorus (Fin d)) :
      0 ≤ HeatKernel d t x := by
    rw [heat_poisson d t ht x]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (tsum_nonneg (fun _ => Real.exp_nonneg _))

  let coeff (d : ℕ) (t : ℝ) (k : Fin d → ℤ) : ℝ :=
    Real.exp (-4*Real.pi^2*t*∑ j,(k j:ℝ)^2)

  have coeff_summable (d : ℕ) (t : ℝ) (ht : 0<t) : Summable (coeff d t) := by
    convert gaussian_lattice_summable d (4*Real.pi^2*t) (by positivity) using 1
    funext k
    dsimp only [coeff]
    ring_nf

  have coeff_neg (d : ℕ) (t : ℝ) (k : Fin d → ℤ) : coeff d t (-k)=coeff d t k := by
    simp [coeff]

  have character_norm (d : ℕ) (k : Fin d → ℤ) (x : UnitAddTorus (Fin d)) :
      ‖UnitAddTorus.mFourier k x‖=1 := by
    simp [UnitAddTorus.mFourier,fourier_apply,norm_prod,Circle.norm_coe]

  have complex_series_summable (d : ℕ) (t : ℝ) (ht : 0<t) (x : UnitAddTorus (Fin d)) :
      Summable (fun k : Fin d → ℤ=>(coeff d t k:ℂ)*UnitAddTorus.mFourier k x) := by
    apply Summable.of_norm_bounded (coeff_summable d t ht)
    intro k
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,character_norm,mul_one]
    exact le_of_eq (abs_of_pos (Real.exp_pos _))

  have heat_complex_series (d : ℕ) (t : ℝ) (ht : 0<t) (x : UnitAddTorus (Fin d)) :
      (HeatKernel d t x:ℂ)=∑' k : Fin d → ℤ,(coeff d t k:ℂ)*UnitAddTorus.mFourier k x := by
    let C : ℂ := ∑' k : Fin d → ℤ,(coeff d t k:ℂ)*UnitAddTorus.mFourier k x
    have hr : C.re=HeatKernel d t x := by
      have hh := Complex.hasSum_re (complex_series_summable d t ht x).hasSum
      rw [← hh.tsum_eq]
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
      simp only [HeatKernel,cos_eq_character_re,coeff,C]
    have hc : (starRingEnd ℂ) C=C := by
      dsimp [C]
      rw [Complex.conj_tsum]
      have he : (fun k : Fin d→ℤ=>(starRingEnd ℂ) ((coeff d t k:ℂ)*UnitAddTorus.mFourier k x))=
          (fun k : Fin d→ℤ=>(coeff d t (-k):ℂ)*UnitAddTorus.mFourier (-k) x) := by
        funext k
        rw [map_mul,Complex.conj_ofReal,coeff_neg,UnitAddTorus.mFourier_neg]
      rw [he]
      exact (Equiv.neg (Fin d→ℤ)).tsum_eq (fun k=>(coeff d t k:ℂ)*UnitAddTorus.mFourier k x)
    have him : C.im=0 := by
      have hh := congrArg Complex.im hc
      simp only [Complex.conj_im] at hh
      linarith
    apply Complex.ext
    · simpa only [Complex.ofReal_re] using hr.symm
    · simpa only [Complex.ofReal_im] using him.symm

  have character_sub (d : ℕ) (k : Fin d→ℤ) (x y : UnitAddTorus (Fin d)) :
      UnitAddTorus.mFourier k (x-y)=UnitAddTorus.mFourier k x*UnitAddTorus.mFourier (-k) y := by
    change (∏ j, fourier (k j) (x j-y j))=(∏ j,fourier (k j) (x j))*(∏ j,fourier (-k j) (y j))
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    simp only [fourier_apply]
    rw [zsmul_sub,sub_eq_add_neg,AddCircle.toCircle_add,Circle.coe_mul,neg_zsmul]

  have heat_character_coeff (d : ℕ) (t : ℝ) (ht : 0<t) (l : Fin d→ℤ) :
      (∫ y,(HeatKernel d t y:ℂ)*UnitAddTorus.mFourier (-l) y)= (coeff d t l:ℂ) := by
    classical
    haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1:ℝ))) := by
      rw [AddCircle.volume_eq_smul_haarAddCircle];simp;infer_instance
    haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := inferInstance
    let F := fun (k : Fin d→ℤ) (y : UnitAddTorus (Fin d))=>
      (coeff d t k:ℂ)*UnitAddTorus.mFourier k y*UnitAddTorus.mFourier (-l) y
    have hi k : Integrable (F k) volume :=
      ((continuous_const.mul (UnitAddTorus.mFourier k).continuous).mul
        (UnitAddTorus.mFourier (-l)).continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hsum : Summable (fun k=>∫ y,‖F k y‖) := by
      apply (coeff_summable d t ht).of_nonneg_of_le
      · intro k;exact integral_nonneg fun _=>norm_nonneg _
      · intro k
        calc
          (∫ y,‖F k y‖) ≤ ∫ _ : UnitAddTorus (Fin d),coeff d t k := by
            apply integral_mono (hi k).norm (integrable_const _)
            intro y
            simp only [F,norm_mul,character_norm,Complex.norm_real,Real.norm_eq_abs,mul_one]
            exact le_of_eq (abs_of_pos (Real.exp_pos _))
          _ = coeff d t k := by simp
    have hm k : (∫ y,F k y)=if k=l then (coeff d t k:ℂ) else 0 := by
      have he : F k=(fun y=>(coeff d t k:ℂ)*UnitAddTorus.mFourier (k-l) y) := by
        funext y
        dsimp [F]
        rw [sub_eq_add_neg,UnitAddTorus.mFourier_add]
        ring
      rw [he,integral_const_mul,character_mean]
      simp [sub_eq_zero]
    simp_rw [heat_complex_series d t ht]
    simp_rw [← tsum_mul_right]
    change (∫ y,∑' k,F k y)=(coeff d t l:ℂ)
    rw [← integral_tsum_of_summable_integral_norm hi hsum]
    simp_rw [hm]
    simp

  have heat_semigroup (d : ℕ) (t u : ℝ) (ht : 0<t) (hu : 0<u)
      (x : UnitAddTorus (Fin d)) :
      HeatSemigroup d t (HeatKernel d u) x=HeatKernel d (t+u) x := by
    classical
    haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1:ℝ))) := by
      rw [AddCircle.volume_eq_smul_haarAddCircle];simp;infer_instance
    haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := inferInstance
    have cH := heat_continuous d t ht
    obtain ⟨C,hC⟩ := isCompact_univ.bddAbove_image cH.norm.continuousOn
    have hb y : |HeatKernel d t y| ≤ C := by simpa using hC ⟨y,Set.mem_univ _,rfl⟩
    have hC0 : 0≤C := (abs_nonneg (HeatKernel d t 0)).trans (hb 0)
    let F := fun (k : Fin d→ℤ) (y : UnitAddTorus (Fin d))=>
      (HeatKernel d t y:ℂ)*(coeff d u k:ℂ)*UnitAddTorus.mFourier k (x-y)
    have hi k : Integrable (F k) volume :=
      (((Complex.continuous_ofReal.comp cH).mul continuous_const).mul
        ((UnitAddTorus.mFourier k).continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
    have hsum : Summable (fun k=>∫ y,‖F k y‖) := by
      apply ((coeff_summable d u hu).mul_left C).of_nonneg_of_le
      · intro k;exact integral_nonneg fun _=>norm_nonneg _
      · intro k
        calc
          (∫ y,‖F k y‖) ≤ ∫ _ : UnitAddTorus (Fin d),C*coeff d u k := by
            apply integral_mono (hi k).norm (integrable_const _)
            intro y
            simp only [F,norm_mul,character_norm,mul_one,Complex.norm_real,Real.norm_eq_abs]
            rw [abs_of_pos (show 0<coeff d u k from Real.exp_pos _)]
            exact mul_le_mul_of_nonneg_right (hb y) (Real.exp_pos _).le
          _ = C*coeff d u k := by simp
    have hm k : (∫ y,F k y)=(coeff d t k:ℂ)*(coeff d u k:ℂ)*UnitAddTorus.mFourier k x := by
      have he : F k=(fun y=>((coeff d u k:ℂ)*UnitAddTorus.mFourier k x)*
        ((HeatKernel d t y:ℂ)*UnitAddTorus.mFourier (-k) y)) := by
        funext y
        dsimp [F]
        rw [character_sub]
        ring
      rw [he,integral_const_mul,heat_character_coeff d t ht]
      ring
    have hc : (∫ y,(HeatKernel d t y:ℂ)*(HeatKernel d u (x-y):ℂ))=(HeatKernel d (t+u) x:ℂ) := by
      simp_rw [heat_complex_series d u hu]
      simp_rw [← tsum_mul_left,←mul_assoc]
      change (∫ y,∑' k,F k y)=(HeatKernel d (t+u) x:ℂ)
      rw [← integral_tsum_of_summable_integral_norm hi hsum,heat_complex_series d (t+u) (by positivity)]
      simp_rw [hm]
      apply tsum_congr
      intro k
      have he : coeff d t k*coeff d u k=coeff d (t+u) k := by
        dsimp [coeff]
        rw [← Real.exp_add]
        congr 1
        ring
      rw [← Complex.ofReal_mul,he]
    apply Complex.ofReal_injective
    change (((∫ y,HeatKernel d t y*HeatKernel d u (x-y)):ℝ):ℂ)=(HeatKernel d (t+u) x:ℂ)
    rw [← integral_complex_ofReal]
    simpa only [Complex.ofReal_mul] using hc
  exact ⟨heat_continuous d t ht, heat_nonnegative d t ht,
    heat_even d t, heat_mass d t ht, heat_poisson d t ht,
    fun u hu x => heat_semigroup d t u ht hu x⟩
