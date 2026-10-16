import Tablet.RieszZeroCutoffSmooth
import Tablet.RieszZeroCutoffAsymptotic
import Tablet.RieszL1Foundation
import Tablet.TorusSmooth
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
open MeasureTheory UnitAddTorus
open scoped ContDiff
-- [TABLET NODE: RieszLocalStructure]
theorem RieszLocalStructure (d : ℕ) (hd : 2 ≤ d) (s a : ℝ)
    (hs : 0 ≤ s) (hsd : s < (d : ℝ)) (ha : 0 < a) :
    ContDiffOn ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin d) => RieszKernel d s a 0 (TorusLift d y))
      {y | TorusLift d y ≠ 0} ∧
    (∀ ε : ℝ, 0 < ε → TorusSmooth (RieszKernel d s a ε)) ∧
    ∃ b C : ℝ, 0 < b ∧ 0 ≤ C ∧
      ∀ y : EuclideanSpace ℝ (Fin d), 0 < ‖y‖ → ‖y‖ < 1 / 4 →
        |RieszKernel d s a 0 (TorusLift d y) -
          (if s = 0 then b * Real.log (1 / ‖y‖)
           else b * Real.rpow ‖y‖ (-s))| ≤ C := by
-- BODY
  classical

  have pos_gaussian_int_summable (c : ℝ) (hc : 0 < c) :
      Summable (fun n : ℤ => Real.exp (-c * (n : ℝ)^2)) := by
    have hn : Summable (fun n : ℕ => Real.exp (-c * (n : ℝ)^2)) := by
      apply Real.summable_exp_nat_mul_of_ge (neg_lt_zero.mpr hc)
      intro n
      exact_mod_cast (show n ≤ n^2 by nlinarith)
    apply summable_int_iff_summable_nat_and_neg.mpr
    constructor
    · simpa using hn
    · simpa using hn

  have pos_gaussian_lattice_summable (d : ℕ) (c : ℝ) (hc : 0 < c) :
      Summable (fun k : Fin d → ℤ => Real.exp (-c * ∑ j, (k j : ℝ)^2)) := by
    induction d with
    | zero => exact (hasSum_fintype _).summable
    | succ d ih =>
      have hs := (pos_gaussian_int_summable c hc).mul_of_nonneg ih
        (fun _ => Real.exp_nonneg _) (fun _ => Real.exp_nonneg _)
      apply (Fin.consEquiv (fun _ : Fin (d+1) => ℤ)).summable_iff.mp
      convert hs using 1
      ext k
      simp only [Function.comp_apply, Fin.consEquiv_apply, Fin.sum_univ_succ,
        Fin.cons_zero, Fin.cons_succ]
      rw [mul_add, Real.exp_add]

  have pos_character_exp (d : ℕ) (k : Fin d → ℤ) (x : UnitAddTorus (Fin d)) :
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

  have pos_cos_eq_character_re (d : ℕ) (k : Fin d → ℤ) (x : UnitAddTorus (Fin d)) :
      Real.cos (2 * Real.pi * ∑ j, (k j : ℝ) *
        (AddCircle.equivIco (1 : ℝ) 0 (x j) : ℝ)) =
          (UnitAddTorus.mFourier k x).re := by
    rw [pos_character_exp, Complex.exp_re]
    simp

  have pos_polynomial_gaussian_bound (c:ℝ) (hc:0<c) (n:ℕ) :
      ∃C:ℝ,0≤C ∧ ∀q:ℝ,0≤q→Real.exp (-c*q)*(q+1)^n≤C*Real.exp (-(c/2)*q) := by
    let C:=((c/2)^n)⁻¹*(n.factorial:ℝ)*Real.exp (c/2)
    have hc2 : 0<c/2 := half_pos hc
    have hpow : 0<(c/2)^n := pow_pos hc2 n
    have hf : 0<(n.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos n
    refine ⟨C,by dsimp [C];positivity,?_⟩
    intro q hq
    have hp := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp ((c/2)*(q+1)) (by positivity) n)
    rw [mul_pow] at hp
    have hscale : (q+1)^n≤(n.factorial:ℝ)*Real.exp ((c/2)*(q+1))/(c/2)^n :=
      (le_div_iff₀ hpow).mpr (by simpa only [mul_comm] using hp)
    calc
      _ ≤ Real.exp (-c*q)*((n.factorial:ℝ)*Real.exp ((c/2)*(q+1))/(c/2)^n) :=
        mul_le_mul_of_nonneg_left hscale (Real.exp_nonneg _)
      _ = C*Real.exp (-(c/2)*q) := by
        dsimp [C]
        have he : -c*q+(c/2)*(q+1)=c/2+(-(c/2)*q) := by ring
        calc
          _ = ((c/2)^n)⁻¹*(n.factorial:ℝ)*(Real.exp (-c*q)*Real.exp ((c/2)*(q+1))) := by ring
          _ = ((c/2)^n)⁻¹*(n.factorial:ℝ)*(Real.exp (c/2)*Real.exp (-(c/2)*q)) := by
            rw [←Real.exp_add,he,Real.exp_add]
          _ = _ := by ring

  have pos_polynomial_gaussian_summable (d:ℕ) (c:ℝ) (hc:0<c) (n:ℕ) :
      Summable (fun k:Fin d→ℤ=>Real.exp (-c*∑j,(k j:ℝ)^2)*(1+∑j,(k j:ℝ)^2)^n) := by
    obtain ⟨C,hC,hb⟩ := pos_polynomial_gaussian_bound c hc n
    have hg := (pos_gaussian_lattice_summable d (c/2) (half_pos hc)).mul_left C
    apply Summable.of_nonneg_of_le
      (fun k=>by positivity)
      (fun k=>by simpa only [add_comm] using hb (∑j,(k j:ℝ)^2) (Finset.sum_nonneg (fun _ _=>sq_nonneg _))) hg

  have pos_iterated_trig_bound (n:ℕ) (x:ℝ) :
      ‖iteratedFDeriv ℝ n Real.cos x‖≤1 ∧ ‖iteratedFDeriv ℝ n Real.sin x‖≤1 := by
    simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv,Real.norm_eq_abs]
    induction n generalizing x with
    | zero => simpa only [iteratedDeriv_zero] using And.intro (Real.abs_cos_le_one x) (Real.abs_sin_le_one x)
    | succ n ih =>
      rw [Real.iteratedDeriv_add_one_cos,Real.iteratedDeriv_add_one_sin]
      simpa only [Pi.neg_apply,abs_neg] using And.intro (ih x).2 (ih x).1

  have pos_linear_trig_bound {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      (L:E→L[ℝ]ℝ) (n:ℕ) (x:E) :
      ‖iteratedFDeriv ℝ n (Real.cos ∘ L) x‖≤‖L‖^n ∧
        ‖iteratedFDeriv ℝ n (Real.sin ∘ L) x‖≤‖L‖^n := by
    constructor
    · rw [L.iteratedFDeriv_comp_right (n:=∞) (i:=n) Real.contDiff_cos x (by exact_mod_cast (show (n:ℕ∞)≤⊤ from le_top))]
      calc
        _ ≤ ‖iteratedFDeriv ℝ n Real.cos (L x)‖*∏_:Fin n,‖L‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
        _ ≤ 1*‖L‖^n := by
          simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
          exact mul_le_mul_of_nonneg_right (pos_iterated_trig_bound n (L x)).1 (by positivity)
        _ = _ := one_mul _
    · rw [L.iteratedFDeriv_comp_right (n:=∞) (i:=n) Real.contDiff_sin x (by exact_mod_cast (show (n:ℕ∞)≤⊤ from le_top))]
      calc
        _ ≤ ‖iteratedFDeriv ℝ n Real.sin (L x)‖*∏_:Fin n,‖L‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
        _ ≤ 1*‖L‖^n := by
          simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
          exact mul_le_mul_of_nonneg_right (pos_iterated_trig_bound n (L x)).2 (by positivity)
        _ = _ := one_mul _

  have pos_contDiff_trig_series {ι E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      (L:ι→E→L[ℝ]ℝ) (a b:ι→ℝ)
      (ha:∀n:ℕ,Summable (fun k=>‖a k‖*‖L k‖^n))
      (hb:∀n:ℕ,Summable (fun k=>‖b k‖*‖L k‖^n)) :
      ContDiff ℝ ∞ (fun x:E=>∑' k:ι, (a k*Real.cos (L k x)+b k*Real.sin (L k x))) := by
    have hca (k:ι) : ContDiff ℝ ∞ (fun x:E=>a k*Real.cos (L k x)) :=
      contDiff_const.mul (Real.contDiff_cos.comp (L k).contDiff)
    have hcb (k:ι) : ContDiff ℝ ∞ (fun x:E=>b k*Real.sin (L k x)) :=
      contDiff_const.mul (Real.contDiff_sin.comp (L k).contDiff)
    apply contDiff_tsum (fun k=>(hca k).add (hcb k))
      (v:=fun n k=>‖a k‖*‖L k‖^n+‖b k‖*‖L k‖^n)
      (fun n _=>(ha n).add (hb n))
    intro n k x hn
    have hna : ContDiffAt ℝ n (fun y:E=>a k*Real.cos (L k y)) x :=
      ((hca k).of_le (by exact_mod_cast (show (n:ℕ∞)≤⊤ from le_top))).contDiffAt
    have hnb : ContDiffAt ℝ n (fun y:E=>b k*Real.sin (L k y)) x :=
      ((hcb k).of_le (by exact_mod_cast (show (n:ℕ∞)≤⊤ from le_top))).contDiffAt
    change ‖iteratedFDeriv ℝ n ((fun y:E=>a k*Real.cos (L k y))+
      (fun y:E=>b k*Real.sin (L k y))) x‖≤_
    rw [iteratedFDeriv_add_apply hna hnb]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · have hc : ContDiffAt ℝ n (Real.cos ∘ L k) x :=
        (Real.contDiff_cos.comp (L k).contDiff).contDiffAt.of_le
          (show (n:ℕ∞ω)≤∞ by exact_mod_cast (show (n:ℕ∞)≤⊤ from le_top))
      change ‖iteratedFDeriv ℝ n (a k • (Real.cos ∘ L k)) x‖≤_
      rw [iteratedFDeriv_const_smul_apply hc,norm_smul]
      exact mul_le_mul_of_nonneg_left (pos_linear_trig_bound (L k) n x).1 (norm_nonneg _)
    · have hc : ContDiffAt ℝ n (Real.sin ∘ L k) x :=
        (Real.contDiff_sin.comp (L k).contDiff).contDiffAt.of_le
          (show (n:ℕ∞ω)≤∞ by exact_mod_cast (show (n:ℕ∞)≤⊤ from le_top))
      change ‖iteratedFDeriv ℝ n (b k • (Real.sin ∘ L k)) x‖≤_
      rw [iteratedFDeriv_const_smul_apply hc,norm_smul]
      exact mul_le_mul_of_nonneg_left (pos_linear_trig_bound (L k) n x).2 (norm_nonneg _)

  let pos_phase {d:ℕ} (k:Fin d→ℤ) : EuclideanSpace ℝ (Fin d)→L[ℝ]ℝ :=
    ∑j,(2*Real.pi*(k j:ℝ)) • EuclideanSpace.proj j

  have pos_phase_apply {d:ℕ} (k:Fin d→ℤ) (y:EuclideanSpace ℝ (Fin d)) :
      pos_phase k y = ∑j,2*Real.pi*(k j:ℝ)*y j := by simp [pos_phase]

  have pos_phase_norm_bound {d:ℕ} (k:Fin d→ℤ) :
      ‖pos_phase k‖≤(2*Real.pi*d)*(1+∑j,(k j:ℝ)^2) := by
    have hq : 0≤∑j,(k j:ℝ)^2 := Finset.sum_nonneg (fun _ _=>sq_nonneg _)
    have hj (j:Fin d) : |(k j:ℝ)| ≤ 1+∑i,(k i:ℝ)^2 := by
      have hs : (k j:ℝ)^2 ≤ ∑i,(k i:ℝ)^2 := Finset.single_le_sum (f:=fun i:Fin d=>(k i:ℝ)^2) (fun _ _=>sq_nonneg _) (Finset.mem_univ j)
      have ha : |(k j:ℝ)| ≤ 1+(k j:ℝ)^2 := by nlinarith [sq_nonneg (|(k j:ℝ)|-1),sq_abs (k j:ℝ)]
      linarith
    apply (pos_phase k).opNorm_le_bound (by positivity)
    intro y
    rw [pos_phase_apply,Real.norm_eq_abs]
    calc
      _ ≤ ∑j,|2*Real.pi*(k j:ℝ)*y j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑j,(2*Real.pi)*(1+∑i,(k i:ℝ)^2)*‖y‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul,abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),abs_of_pos Real.pi_pos]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hj j) (by positivity))
          (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le y j) (abs_nonneg _) (by positivity)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring

  have pos_phase_gaussian_summable (d:ℕ) (c:ℝ) (hc:0<c) (n:ℕ) :
      Summable (fun k:Fin d→ℤ=>Real.exp (-c*∑j,(k j:ℝ)^2)*‖pos_phase k‖^n) := by
    have hp := (pos_polynomial_gaussian_summable d c hc n).mul_left ((2*Real.pi*d)^n)
    apply Summable.of_nonneg_of_le (fun _=>by positivity) _ hp
    intro k
    have hn := pow_le_pow_left₀ (norm_nonneg (pos_phase k)) (pos_phase_norm_bound k) n
    rw [mul_pow] at hn
    calc
      _ ≤ Real.exp (-c*∑j,(k j:ℝ)^2)*((2*Real.pi*d)^n*(1+∑j,(k j:ℝ)^2)^n) :=
        mul_le_mul_of_nonneg_left hn (Real.exp_nonneg _)
      _ = _ := by ring

  have pos_character_lift {d:ℕ} (k:Fin d→ℤ) (y:EuclideanSpace ℝ (Fin d)) :
      UnitAddTorus.mFourier k (TorusLift d y)=Complex.exp ((pos_phase k y:ℂ)*Complex.I) := by
    simp only [UnitAddTorus.mFourier,ContinuousMap.coe_mk,TorusLift,fourier_coe_apply,
      div_one,pos_phase_apply,Complex.ofReal_sum]
    rw [←Complex.exp_sum]
    congr 1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring

  have pos_character_sub (d:ℕ) (k:Fin d→ℤ) (x y:UnitAddTorus (Fin d)) :
      mFourier k (x-y)=mFourier k x*mFourier (-k) y := by
    change (∏j,fourier (k j) (x j-y j))=(∏j,fourier (k j) (x j))*(∏j,fourier (-k j) (y j))
    rw [←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    simp only [fourier_apply]
    rw [zsmul_sub,sub_eq_add_neg,AddCircle.toCircle_add,Circle.coe_mul,neg_zsmul]

  have pos_character_bound (d:ℕ) (k:Fin d→ℤ) (x:UnitAddTorus (Fin d)) :
      |(mFourier k x).re|≤1 ∧ |(mFourier k x).im|≤1 := by
    have hnorm : ‖mFourier k x‖≤1 := by
      simpa only [mFourier_norm] using (mFourier k).norm_coe_le_norm x
    exact ⟨(Complex.abs_re_le_norm _).trans hnorm,(Complex.abs_im_le_norm _).trans hnorm⟩

  have pos_coefficient_bounds (d:ℕ) (f:UnitAddTorus (Fin d)→ℝ) (hf:Integrable f volume)
      (k:Fin d→ℤ) :
      Integrable (fun z=>(mFourier k z).re*f z) volume ∧
      Integrable (fun z=>(mFourier k z).im*f z) volume ∧
      |∫z,(mFourier k z).re*f z|≤∫z,‖f z‖ ∧
      |∫z,(mFourier k z).im*f z|≤∫z,‖f z‖ := by
    have hr : Integrable (fun z=>(mFourier k z).re*f z) volume := hf.bdd_mul
      (Complex.continuous_re.comp (mFourier k).continuous).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z=>by simpa only [Real.norm_eq_abs] using (pos_character_bound d k z).1)
    have hi : Integrable (fun z=>(mFourier k z).im*f z) volume := hf.bdd_mul
      (Complex.continuous_im.comp (mFourier k).continuous).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z=>by simpa only [Real.norm_eq_abs] using (pos_character_bound d k z).2)
    refine ⟨hr,hi,?_,?_⟩
    · simpa only [Real.norm_eq_abs] using norm_integral_le_of_norm_le (f:=fun z=>(mFourier k z).re*f z) hf.norm
        (Filter.Eventually.of_forall fun z=>by
          rw [norm_mul,Real.norm_eq_abs (mFourier k z).re]
          exact mul_le_of_le_one_left (norm_nonneg _) (pos_character_bound d k z).1)
    · simpa only [Real.norm_eq_abs] using norm_integral_le_of_norm_le (f:=fun z=>(mFourier k z).im*f z) hf.norm
        (Filter.Eventually.of_forall fun z=>by
          rw [norm_mul,Real.norm_eq_abs (mFourier k z).im]
          exact mul_le_of_le_one_left (norm_nonneg _) (pos_character_bound d k z).2)

  have pos_convolution_series (d:ℕ) (t:ℝ) (ht:0<t)
      (f:UnitAddTorus (Fin d)→ℝ) (hf:Integrable f volume) (x:UnitAddTorus (Fin d)) :
      HeatSemigroup d t f x = ∑'k:Fin d→ℤ,
        Real.exp (-4*Real.pi^2*t*∑j,(k j:ℝ)^2)*
         ((∫z,(mFourier k z).re*f z)*(mFourier k x).re+
          (∫z,(mFourier k z).im*f z)*(mFourier k x).im) := by
    let w := fun k:Fin d→ℤ=>Real.exp (-4*Real.pi^2*t*∑j,(k j:ℝ)^2)
    let F := fun (k:Fin d→ℤ) (z:UnitAddTorus (Fin d))=>w k*(mFourier k (x-z)).re*f z
    have hi (k:Fin d→ℤ) : Integrable (F k) volume := by
      apply hf.bdd_mul (c:=w k)
        (continuous_const.mul (Complex.continuous_re.comp
          ((mFourier k).continuous.comp (continuous_const.sub continuous_id)))).aestronglyMeasurable
      exact Filter.Eventually.of_forall fun z=>by
        change ‖w k*(mFourier k (x-z)).re‖≤w k
        rw [norm_mul,Real.norm_eq_abs (w k),abs_of_pos (Real.exp_pos _),Real.norm_eq_abs]
        exact mul_le_of_le_one_right (Real.exp_nonneg _) (pos_character_bound d k (x-z)).1
    have hs : Summable (fun k=>∫z,‖F k z‖) := by
      have hg := (pos_gaussian_lattice_summable d (4*Real.pi^2*t) (by positivity)).mul_right (∫z,‖f z‖)
      have hg' : Summable (fun k=>w k*(∫z,‖f z‖)) := by
        convert! hg using 1
        ext k
        dsimp only [w]
        congr 1 <;> ring
      apply Summable.of_nonneg_of_le (fun _=>integral_nonneg (fun _=>norm_nonneg _)) _ hg'
      intro k
      calc
        _ ≤ ∫z,w k*‖f z‖ := by
          apply integral_mono (hi k).norm (hf.norm.const_mul (w k))
          intro z
          dsimp [F]
          rw [abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
          exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (Real.exp_nonneg _)
            (pos_character_bound d k (x-z)).1) (abs_nonneg _)
        _ = w k*(∫z,‖f z‖) := integral_const_mul _ _
    have hswap : HeatSemigroup d t f x = ∫z,HeatKernel d t (x-z)*f z := by
      unfold HeatSemigroup
      convert! integral_sub_left_eq_self (fun z=>HeatKernel d t (x-z)*f z) volume x using 1
      congr 1
      funext z
      congr 1
      congr 1
      abel
    rw [hswap]
    have heq : (fun z=>HeatKernel d t (x-z)*f z)=fun z=>∑'k,F k z := by
      funext z
      simp only [HeatKernel,pos_cos_eq_character_re,tsum_mul_right,F,w]
    rw [heq,←integral_tsum_of_summable_integral_norm hi hs]
    apply tsum_congr
    intro k
    have hpoint (z:UnitAddTorus (Fin d)) : F k z =
        w k*((mFourier k x).re*((mFourier k z).re*f z)+
          (mFourier k x).im*((mFourier k z).im*f z)) := by
      dsimp [F]
      rw [pos_character_sub,mFourier_neg,Complex.mul_re,Complex.conj_re,Complex.conj_im]
      ring
    simp_rw [hpoint]
    rw [integral_const_mul,integral_add
      ((pos_coefficient_bounds d f hf k).1.const_mul _)
      ((pos_coefficient_bounds d f hf k).2.1.const_mul _),integral_const_mul,integral_const_mul]
    dsimp [w]
    ring

  have pos_heat_smoothing (d:ℕ) (t:ℝ) (ht:0<t)
      (f:UnitAddTorus (Fin d)→ℝ) (hf:Integrable f volume) :
      TorusSmooth (HeatSemigroup d t f) := by
    let w := fun k:Fin d→ℤ=>Real.exp (-4*Real.pi^2*t*∑j,(k j:ℝ)^2)
    let A := fun k:Fin d→ℤ=>w k*(∫z,(mFourier k z).re*f z)
    let B := fun k:Fin d→ℤ=>w k*(∫z,(mFourier k z).im*f z)
    let M := ∫z,‖f z‖
    have hm : 0≤M := integral_nonneg (fun _=>norm_nonneg _)
    have ha (k:Fin d→ℤ) : ‖A k‖≤w k*M := by
      dsimp only [A,M]
      rw [norm_mul,Real.norm_eq_abs (w k),abs_of_pos (Real.exp_pos _),Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (pos_coefficient_bounds d f hf k).2.2.1 (Real.exp_nonneg _)
    have hb (k:Fin d→ℤ) : ‖B k‖≤w k*M := by
      dsimp only [B,M]
      rw [norm_mul,Real.norm_eq_abs (w k),abs_of_pos (Real.exp_pos _),Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (pos_coefficient_bounds d f hf k).2.2.2 (Real.exp_nonneg _)
    have hmom (n:ℕ) : Summable (fun k=>w k*M*‖pos_phase k‖^n) := by
      have h := (pos_phase_gaussian_summable d (4*Real.pi^2*t) (by positivity) n).mul_left M
      convert! h using 1
      ext k
      dsimp only [w]
      ring_nf
    have hma (n:ℕ) : Summable (fun k=>‖A k‖*‖pos_phase k‖^n) :=
      Summable.of_nonneg_of_le (fun _=>by positivity)
        (fun k=>mul_le_mul_of_nonneg_right (ha k) (by positivity)) (hmom n)
    have hmb (n:ℕ) : Summable (fun k=>‖B k‖*‖pos_phase k‖^n) :=
      Summable.of_nonneg_of_le (fun _=>by positivity)
        (fun k=>mul_le_mul_of_nonneg_right (hb k) (by positivity)) (hmom n)
    have hc := pos_contDiff_trig_series (fun k:Fin d→ℤ=>pos_phase k) A B hma hmb
    change ContDiff ℝ ∞ (fun y=>HeatSemigroup d t f (TorusLift d y))
    convert! hc using 1
    funext y
    rw [pos_convolution_series d t ht f hf]
    apply tsum_congr
    intro k
    have hre : (mFourier k (TorusLift d y)).re=Real.cos (pos_phase k y) := by
      rw [pos_character_lift,Complex.exp_re]
      simp
    have him : (mFourier k (TorusLift d y)).im=Real.sin (pos_phase k y) := by
      rw [pos_character_lift,Complex.exp_im]
      simp
    rw [hre,him]
    dsimp only [A,B,w]
    ring

  have pos_riesz_positive_smooth (d:ℕ) (hd:2≤d) (s a ε:ℝ)
      (hs:0≤s) (hsd:s<(d:ℝ)) (ha:0<a) (hε:0<ε) :
      TorusSmooth (RieszKernel d s a ε) := by
    obtain ⟨c,hc,hall⟩ := RieszL1Foundation d hd s a hs hsd ha
    have hf : Integrable (RieszKernel d s a 0) volume := (hall 0 (by norm_num)).2.1
    have heq : RieszKernel d s a ε=HeatSemigroup d ε (RieszKernel d s a 0) := by
      funext x
      exact (hall ε hε.le).2.2.2.2.2.2 hε x
    rw [heq]
    exact pos_heat_smoothing d ε hε (RieszKernel d s a 0) hf
  exact ⟨RieszZeroCutoffSmooth d s a hsd,
    (fun ε hε => pos_riesz_positive_smooth d hd s a ε hs hsd ha hε),
    RieszZeroCutoffAsymptotic d hd s a hs hsd ha⟩
