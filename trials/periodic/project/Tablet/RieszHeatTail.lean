import Mathlib.Analysis.Real.Pi.Bounds
import Tablet.HeatKernelFacts
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
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
open MeasureTheory UnitAddTorus
open scoped ContDiff
-- [TABLET NODE: RieszHeatTail]
theorem RieszHeatTail (d : ℕ) (α : ℝ) (hα : 0 < α) :
    ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin d) =>
      ∫ t in Set.Ioi (1 : ℝ), t^(α - 1) * (HeatKernel d t (TorusLift d y) - 1)) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : UnitAddTorus (Fin d),
      IntegrableOn (fun t : ℝ => t^(α - 1) * (HeatKernel d t x - 1))
        (Set.Ioi (1 : ℝ)) volume ∧
      |∫ t in Set.Ioi (1 : ℝ), t^(α - 1) * (HeatKernel d t x - 1)| ≤ C := by
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

  have tail_heat_joint_measurable (d : ℕ) :
      Measurable (fun p : ℝ × UnitAddTorus (Fin d) => HeatKernel d p.1 p.2) := by
    unfold HeatKernel
    simp_rw [pos_cos_eq_character_re]
    apply Measurable.tsum
    intro k
    exact ((measurable_const.mul measurable_fst).mul measurable_const).exp.mul
      ((Complex.continuous_re.comp (UnitAddTorus.mFourier k).continuous).measurable.comp measurable_snd)

  have tail_nonzero_norm_sq {d : ℕ} (k : Fin d → ℤ) (hk : k≠0) :
      (1:ℝ)≤∑ j,(k j:ℝ)^2 := by
    have hex : ∃j,k j≠0 := by
      by_contra h
      push_neg at h
      apply hk
      funext j
      exact h j
    obtain ⟨j,hj⟩ := hex
    have hsq : (1:ℝ)≤(k j:ℝ)^2 := by
      have h : (1:ℤ)≤(k j)^2 := by
        have hp : 1≤k j ∨ k j≤-1 := by omega
        rcases hp with hp | hp <;> nlinarith
      exact_mod_cast h
    exact hsq.trans (Finset.single_le_sum (fun l _=>sq_nonneg (k l:ℝ)) (Finset.mem_univ j))

  have tail_heat_decay_half (d : ℕ) : ∃C:ℝ,0≤C ∧ ∀(t ε:ℝ),1/2≤t → 0≤ε →
      ∀x:UnitAddTorus (Fin d),|HeatKernel d (t+ε) x-1|≤C*Real.exp (-t) := by
    classical
    let C := ∑' k:Fin d→ℤ,Real.exp (-(∑j,(k j:ℝ)^2))
    have hg := pos_gaussian_lattice_summable d 1 zero_lt_one
    have hg' : Summable (fun k:Fin d→ℤ=>Real.exp (-(∑j,(k j:ℝ)^2))) := by simpa using hg
    refine ⟨C,tsum_nonneg (fun _=>Real.exp_nonneg _),?_⟩
    intro t ε ht hε x
    let f := fun k:Fin d→ℤ=>Real.exp (-4*Real.pi^2*(t+ε)*∑j,(k j:ℝ)^2)*
      Real.cos (2*Real.pi*∑j,(k j:ℝ)*(AddCircle.equivIco (1:ℝ) 0 (x j):ℝ))
    have ht0 : 0<t+ε := by linarith
    have htpos : 0≤t := by linarith
    have hgTime := pos_gaussian_lattice_summable d (4*Real.pi^2*(t+ε)) (by positivity)
    have hfg (k) : ‖f k‖≤Real.exp (-4*Real.pi^2*(t+ε)*∑j,(k j:ℝ)^2) := by
      simp only [f,Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (Real.exp_nonneg _) (Real.abs_cos_le_one _)
    have hgTime' : Summable (fun k:Fin d→ℤ=>Real.exp (-4*Real.pi^2*(t+ε)*∑j,(k j:ℝ)^2)) := by
      convert hgTime using 1 <;> ring_nf
    have hf : Summable f := summable_norm_iff.mp (Summable.of_nonneg_of_le (fun _=>norm_nonneg _) hfg hgTime')
    have hnonzero (k:Fin d→ℤ) : ‖if k=0 then (0:ℝ) else f k‖ ≤
        Real.exp (-t)*Real.exp (-(∑j,(k j:ℝ)^2)) := by
      by_cases hk:k=0
      · simp [hk,Real.exp_nonneg]
      · simp only [hk,↓reduceIte]
        apply (hfg k).trans
        rw [←Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hq := tail_nonzero_norm_sq k hk
        have hqpos : 0≤∑j,(k j:ℝ)^2 := Finset.sum_nonneg (fun _ _=>sq_nonneg _)
        have hπ : 3≤4*Real.pi^2 := by nlinarith [Real.pi_gt_three]
        have h1 := mul_le_mul_of_nonneg_left hq htpos
        have h2 := mul_le_mul_of_nonneg_right ht hqpos
        have heq := mul_nonneg hε hqpos
        have h3 := mul_le_mul_of_nonneg_right hπ (mul_nonneg (by linarith : 0≤t+ε) hqpos)
        nlinarith
    have hs := Summable.of_nonneg_of_le (fun k=>norm_nonneg _) hnonzero (hg'.mul_left (Real.exp (-t)))
    have he : HeatKernel d (t+ε) x-1=∑'k:Fin d→ℤ,if k=0 then 0 else f k := by
      have ht := hf.tsum_eq_add_tsum_ite 0
      have h0 : f 0=1 := by simp [f]
      change (∑'k,f k)-1=_
      rw [ht,h0]
      ring
    rw [he,←Real.norm_eq_abs]
    calc
      _ ≤ ∑'k:Fin d→ℤ,‖if k=0 then (0:ℝ) else f k‖ := norm_tsum_le_tsum_norm hs
      _ ≤ ∑'k:Fin d→ℤ,Real.exp (-t)*Real.exp (-(∑j,(k j:ℝ)^2)) :=
        Summable.tsum_le_tsum hnonzero hs (hg'.mul_left (Real.exp (-t)))
      _ = C*Real.exp (-t) := by rw [tsum_mul_left];exact mul_comm _ _

  haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1:ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
    infer_instance

  let tail_shiftedIntegrand (d : ℕ) (α : ℝ) (p : ℝ×UnitAddTorus (Fin d)) : ℝ :=
    p.1^(α-1)*(HeatKernel d (p.1-1/2) p.2-1)

  have tail_shifted_integrand_measurable (d : ℕ) (α : ℝ) : Measurable (tail_shiftedIntegrand d α) := by
    exact (measurable_fst.pow_const _).mul
      (((tail_heat_joint_measurable d).comp ((measurable_fst.sub_const (1/2)).prodMk measurable_snd)).sub measurable_const)

  have tail_shifted_integrand_bound (d : ℕ) : ∃C:ℝ,0≤C ∧ ∀ (α t:ℝ),1<t→
      ∀x:UnitAddTorus (Fin d),‖tail_shiftedIntegrand d α (t,x)‖≤C*(t^(α-1)*Real.exp (-t)) := by
    obtain ⟨K,hK,hdec⟩ := tail_heat_decay_half d
    refine ⟨K*Real.exp (1/2),by positivity,?_⟩
    intro α t ht x
    have ht0 : 0<t := by linarith
    have hr : 1/2≤t-1/2 := by linarith
    have hp : 0≤t^(α-1) := Real.rpow_nonneg ht0.le _
    dsimp [tail_shiftedIntegrand]
    rw [abs_mul,abs_of_nonneg hp]
    calc
      _ ≤ t^(α-1)*(K*Real.exp (-(t-1/2))) := mul_le_mul_of_nonneg_left (by simpa using hdec (t-1/2) 0 hr (by norm_num) x) hp
      _ = _ := by rw [show -(t-1/2)=(1/2:ℝ)+(-t) by ring,Real.exp_add];ring

  have tail_shifted_integrand_joint_integrable (d : ℕ) (α : ℝ) (hα : 0<α) :
      Integrable (tail_shiftedIntegrand d α)
        ((volume.restrict (Set.Ioi (1:ℝ))).prod (volume:Measure (UnitAddTorus (Fin d)))) := by
    obtain ⟨C,hC,hbd⟩ := tail_shifted_integrand_bound d
    have hD : Integrable (fun t:ℝ=>C*(t^(α-1)*Real.exp (-t))) (volume.restrict (Set.Ioi 1)) := by
      have hi : IntegrableOn (fun t:ℝ=>t^(α-1)*Real.exp (-t)) (Set.Ioi 0) volume := by
        simpa only [mul_comm] using Real.GammaIntegral_convergent hα
      exact (hi.mono_set (Set.Ioi_subset_Ioi (by norm_num))).const_mul C
    apply (hD.comp_fst (volume:Measure (UnitAddTorus (Fin d)))).mono'
      (tail_shifted_integrand_measurable d α).aestronglyMeasurable
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ:=volume.restrict (Set.Ioi (1:ℝ)))
      (ν:=(volume:Measure (UnitAddTorus (Fin d))))).ae (ae_restrict_mem measurableSet_Ioi)] with p hp
    exact hbd α p.1 hp p.2

  let tail_shiftedTail (d : ℕ) (α : ℝ) (x : UnitAddTorus (Fin d)) : ℝ :=
    ∫t in Set.Ioi (1:ℝ),tail_shiftedIntegrand d α (t,x)

  have tail_shifted_tail_integrable (d : ℕ) (α : ℝ) (hα : 0<α) :
      Integrable (tail_shiftedTail d α) (volume:Measure (UnitAddTorus (Fin d))) :=
    (tail_shifted_integrand_joint_integrable d α hα).integral_prod_right

  have tail_shifted_integrand_translated_integrable (d : ℕ) (α : ℝ) (hα : 0<α)
      (x : UnitAddTorus (Fin d)) :
      Integrable (fun p:ℝ×UnitAddTorus (Fin d)=>tail_shiftedIntegrand d α (p.1,x-p.2))
        ((volume.restrict (Set.Ioi (1:ℝ))).prod (volume:Measure (UnitAddTorus (Fin d)))) := by
    obtain ⟨C,hC,hbd⟩ := tail_shifted_integrand_bound d
    have hD : Integrable (fun t:ℝ=>C*(t^(α-1)*Real.exp (-t))) (volume.restrict (Set.Ioi 1)) := by
      have hi : IntegrableOn (fun t:ℝ=>t^(α-1)*Real.exp (-t)) (Set.Ioi 0) volume := by
        simpa only [mul_comm] using Real.GammaIntegral_convergent hα
      exact (hi.mono_set (Set.Ioi_subset_Ioi (by norm_num))).const_mul C
    apply (hD.comp_fst (volume:Measure (UnitAddTorus (Fin d)))).mono'
      ((tail_shifted_integrand_measurable d α).comp
        (measurable_fst.prodMk (measurable_const.sub measurable_snd))).aestronglyMeasurable
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ:=volume.restrict (Set.Ioi (1:ℝ)))
      (ν:=(volume:Measure (UnitAddTorus (Fin d))))).ae (ae_restrict_mem measurableSet_Ioi)] with p hp
    exact hbd α p.1 hp (x-p.2)

  have tail_tail_smoothing_identity (d : ℕ) (α : ℝ) (hα : 0<α) (x : UnitAddTorus (Fin d)) :
      HeatSemigroup d (1/2) (tail_shiftedTail d α) x =
        ∫t in Set.Ioi (1:ℝ), t^(α-1)*(HeatKernel d t x-1) := by
    let K := HeatKernel d (1/2)
    have hKc : Continuous K := (HeatKernelFacts d (1/2) (by norm_num)).1
    have hKi : Integrable K (volume:Measure (UnitAddTorus (Fin d))) :=
      hKc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hKm : (∫z:UnitAddTorus (Fin d),K z)=1 :=
      (HeatKernelFacts d (1/2) (by norm_num)).2.2.2.1
    obtain ⟨D,hD⟩ := (isCompact_univ : IsCompact (Set.univ:Set (UnitAddTorus (Fin d)))).exists_bound_of_continuousOn hKc.continuousOn
    have hJoint : Integrable (fun p:ℝ×UnitAddTorus (Fin d)=>K p.2*tail_shiftedIntegrand d α (p.1,x-p.2))
        ((volume.restrict (Set.Ioi (1:ℝ))).prod (volume:Measure (UnitAddTorus (Fin d)))) :=
      (tail_shifted_integrand_translated_integrable d α hα x).bdd_mul
        (hKc.measurable.comp measurable_snd).aestronglyMeasurable
        (Filter.Eventually.of_forall fun p=>hD p.2 (Set.mem_univ _))
    unfold HeatSemigroup tail_shiftedTail
    change (∫z:UnitAddTorus (Fin d),K z*(∫t in Set.Ioi (1:ℝ),tail_shiftedIntegrand d α (t,x-z)))=_
    calc
      _ = ∫z:UnitAddTorus (Fin d),∫t in Set.Ioi (1:ℝ),K z*tail_shiftedIntegrand d α (t,x-z) := by
        simp_rw [integral_const_mul]
      _ = ∫t in Set.Ioi (1:ℝ),∫z:UnitAddTorus (Fin d),K z*tail_shiftedIntegrand d α (t,x-z) :=
        (integral_integral_swap hJoint).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht1 : 1<t := ht
        have hr : 0<t-1/2 := by linarith
        have hrc := (HeatKernelFacts d (t-1/2) hr).1
        have hpi : Integrable (fun z:UnitAddTorus (Fin d)=>K z*HeatKernel d (t-1/2) (x-z)) volume :=
          (hKc.mul (hrc.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
        have heq : (fun z:UnitAddTorus (Fin d)=>K z*tail_shiftedIntegrand d α (t,x-z)) =
            fun z=>t^(α-1)*(K z*HeatKernel d (t-1/2) (x-z)-K z) := by
          funext z
          dsimp [tail_shiftedIntegrand]
          ring
        rw [heq,integral_const_mul,integral_sub hpi hKi,hKm]
        have hh := (HeatKernelFacts d (1/2) (by norm_num)).2.2.2.2.2 (t-1/2) hr x
        have htime : (1/2:ℝ)+(t-1/2)=t := by ring
        rw [htime] at hh
        exact congrArg (fun u:ℝ=>t^(α-1)*(u-1)) hh

  have tail_long_tail_smooth (d : ℕ) (α : ℝ) (hα : 0<α) :
      ContDiff ℝ ∞ (fun y:EuclideanSpace ℝ (Fin d)=>
        ∫t in Set.Ioi (1:ℝ),t^(α-1)*(HeatKernel d t (TorusLift d y)-1)) := by
    have hs := pos_heat_smoothing d (1/2) (by norm_num) (tail_shiftedTail d α)
      (tail_shifted_tail_integrable d α hα)
    change ContDiff ℝ ∞ (fun y:EuclideanSpace ℝ (Fin d)=>HeatSemigroup d (1/2) (tail_shiftedTail d α) (TorusLift d y)) at hs
    convert hs using 1
    funext y
    exact (tail_tail_smoothing_identity d α hα (TorusLift d y)).symm

  have tail_long_tail_integrable_bound (d : ℕ) (α : ℝ) (hα : 0<α) :
      ∃C:ℝ,0≤C ∧ ∀x:UnitAddTorus (Fin d),
        IntegrableOn (fun t:ℝ=>t^(α-1)*(HeatKernel d t x-1)) (Set.Ioi (1:ℝ)) volume ∧
        |∫t in Set.Ioi (1:ℝ),t^(α-1)*(HeatKernel d t x-1)|≤C := by
    obtain ⟨K,hK,hdec⟩ := tail_heat_decay_half d
    let D := fun t:ℝ=>K*(t^(α-1)*Real.exp (-t))
    have hDi : IntegrableOn D (Set.Ioi 1) volume := by
      have hi : IntegrableOn (fun t:ℝ=>t^(α-1)*Real.exp (-t)) (Set.Ioi 0) volume := by
        simpa only [mul_comm] using Real.GammaIntegral_convergent hα
      exact (hi.mono_set (Set.Ioi_subset_Ioi (by norm_num))).const_mul K
    let C := ∫t in Set.Ioi (1:ℝ),D t
    refine ⟨C,integral_nonneg_of_ae ?_,?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0≤t := le_trans (by norm_num) (le_of_lt ht)
      dsimp [D]
      positivity
    · intro x
      have hm : Measurable (fun t:ℝ=>t^(α-1)*(HeatKernel d t x-1)) :=
        (measurable_id.pow_const _).mul
          (((tail_heat_joint_measurable d).comp (measurable_id.prodMk measurable_const)).sub measurable_const)
      have hb : ∀ᵐt:ℝ∂volume.restrict (Set.Ioi 1),‖t^(α-1)*(HeatKernel d t x-1)‖≤D t := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht1 : 1<t := ht
        have ht0 : 0<t := by linarith
        have hr : 1/2≤t := by linarith
        have hp : 0≤t^(α-1) := Real.rpow_nonneg ht0.le _
        rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg hp,Real.norm_eq_abs]
        calc
          _ ≤ t^(α-1)*(K*Real.exp (-t)) := mul_le_mul_of_nonneg_left (by simpa using hdec t 0 hr (by norm_num) x) hp
          _ = D t := by dsimp [D];ring
      refine ⟨hDi.mono' hm.aestronglyMeasurable hb,?_⟩
      simpa only [Real.norm_eq_abs] using norm_integral_le_of_norm_le hDi hb

  exact ⟨tail_long_tail_smooth d α hα, tail_long_tail_integrable_bound d α hα⟩
