import Tablet.TorusLift
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Tablet.Preamble
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Separation.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Tablet.DominatedSmoothIntegral
import Tablet.RieszKernel
import Tablet.RieszHeatTail
import Tablet.RieszGaussianImageRemainder
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
open MeasureTheory Set Function Filter
open scoped ContDiff Topology
-- [TABLET NODE: RieszZeroCutoffSmooth]
theorem RieszZeroCutoffSmooth (d : ℕ) (s a : ℝ) (hsd : s < (d : ℝ)) :
    ContDiffOn ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin d) => RieszKernel d s a 0 (TorusLift d y))
      {y | TorusLift d y ≠ 0} := by
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

  let latticePoint {d:ℕ} (n:Fin d→ℤ) : EuclideanSpace ℝ (Fin d) :=
    WithLp.toLp 2 (fun j=>(n j:ℝ))
  have lift_lattice {d:ℕ} (n:Fin d→ℤ) : TorusLift d (latticePoint n)=0 := by
    funext j
    change ((n j:ℝ):AddCircle (1:ℝ))=0
    exact (AddCircle.coe_eq_zero_iff (p:=(1:ℝ))).mpr ⟨n j,by simp⟩
  have lift_neg_lattice {d:ℕ} (n:Fin d→ℤ) : TorusLift d (-latticePoint n)=0 := by
    funext j
    have hj:=congrFun (lift_lattice n) j
    change ((n j:ℝ):AddCircle (1:ℝ))=0 at hj
    change ((-(n j:ℝ)):AddCircle (1:ℝ))=0
    simpa only [AddCircle.coe_neg,neg_zero] using congrArg Neg.neg hj
  
  have lift_continuous (d:ℕ) : Continuous (TorusLift d) := by
    apply continuous_pi
    intro j
    dsimp [TorusLift]
    fun_prop
  
  have distance_to_lattice (d:ℕ) (y:EuclideanSpace ℝ (Fin d))
      (hy:TorusLift d y≠0) :
      ∃δ:ℝ,0<δ ∧ ∀n:Fin d→ℤ,δ≤‖y+latticePoint n‖ := by
    have hU : IsOpen {z:EuclideanSpace ℝ (Fin d)|TorusLift d z≠0} :=
      isOpen_compl_singleton.preimage (lift_continuous d)
    obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hU y hy
    refine ⟨δ,hδ,?_⟩
    intro n
    have hn : ¬(-latticePoint n:EuclideanSpace ℝ (Fin d))∈Metric.ball y δ := by
      intro h
      have hbad:=hball h
      exact hbad (lift_neg_lattice n)
    have hdist : δ≤dist (-latticePoint n) y := le_of_not_gt hn
    simpa only [dist_eq_norm',sub_neg_eq_add] using hdist
  
  have nat_le_inf (n:ℕ) : (n:ℕ∞ω)≤∞ := by exact_mod_cast (show (n:ℕ∞)≤⊤ from le_top)
  have affine_iterated_bound {E:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a x:E) (n:ℕ) :
   ‖iteratedFDeriv ℝ n (fun y:E=>y+a) x‖≤‖x+a‖+1 := by
    change ‖iteratedFDeriv ℝ n (fun y:E=>id (y+a)) x‖≤_
    rw [iteratedFDeriv_comp_add_right (f:=id)]
    cases n with
    | zero => rw [norm_iteratedFDeriv_zero]; simp only [id_eq]; linarith
    | succ n =>
      rw [← norm_iteratedFDeriv_fderiv]
      have hfd : fderiv ℝ (id:E→E) = fun _=>ContinuousLinearMap.id ℝ E := by
        funext y
        exact fderiv_id
      rw [hfd]
      cases n with
      | zero => simpa only [norm_iteratedFDeriv_zero] using
          (ContinuousLinearMap.norm_id_le (𝕜:=ℝ) (E:=E)).trans (by linarith [norm_nonneg (x+a)] : (1:ℝ)≤‖x+a‖+1)
      | succ n => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]; positivity
  have square_iterated_bound {E:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a x:E) (n:ℕ) :
   ‖iteratedFDeriv ℝ n (fun y:E=>‖y+a‖^2) x‖≤(2:ℝ)^n*(‖x+a‖+1)^2 := by
    have hf : ContDiff ℝ ∞ (fun y:E=>y+a) := contDiff_id.add contDiff_const
    have heq : (fun y:E=>‖y+a‖^2)=(fun y:E => (innerSL ℝ) (y+a) (y+a)) := by
      funext y; simp only [innerSL_apply_apply,real_inner_self_eq_norm_sq]
    rw [heq]
    calc
     _ ≤ ∑ i ∈ Finset.range (n+1),(n.choose i:ℝ)*
         ‖iteratedFDeriv ℝ i (fun y:E=>y+a) x‖*
         ‖iteratedFDeriv ℝ (n-i) (fun y:E=>y+a) x‖ :=
        (innerSL ℝ).norm_iteratedFDeriv_le_of_bilinear_of_le_one hf hf x (nat_le_inf n) (norm_innerSL_le ℝ)
     _ ≤ ∑ i ∈ Finset.range (n+1),(n.choose i:ℝ)*(‖x+a‖+1)*(‖x+a‖+1) := by
        apply Finset.sum_le_sum; intro i hi
        exact mul_le_mul (mul_le_mul_of_nonneg_left (affine_iterated_bound a x i) (by positivity))
          (affine_iterated_bound a x (n-i)) (by positivity) (by positivity)
     _ = (2:ℝ)^n*(‖x+a‖+1)^2 := by
        simp only [mul_assoc, ← sq, ← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose n
  have exponential_square_bound {E:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a x:E) (c:ℝ) (hc:0≤c) (n:ℕ) :
   ‖iteratedFDeriv ℝ n (fun y:E=>Real.exp (-c*‖y+a‖^2)) x‖ ≤
   (n.factorial:ℝ)*Real.exp (-c*‖x+a‖^2)*
     (2*max c 1*(‖x+a‖+1)^2)^n := by
    have hf : ContDiff ℝ ∞ (fun y:E=>-c*‖y+a‖^2) := by
      have : ContDiff ℝ ∞ (fun y:E=>‖y+a‖^2) := (contDiff_id.add contDiff_const).norm_sq (𝕜:=ℝ)
      exact contDiff_const.mul this
    change ‖iteratedFDeriv ℝ n (Real.exp ∘ (fun y:E=>-c*‖y+a‖^2)) x‖≤_
    apply norm_iteratedFDeriv_comp_le Real.contDiff_exp hf (nat_le_inf n) x
    · intro i hi
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      have he : iteratedDeriv i Real.exp = Real.exp := by
        simpa only [one_mul,one_pow] using iteratedDeriv_exp_const_mul i 1
      rw [he,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    · intro i hi hin
      have hsi : ContDiffAt ℝ i (fun y:E=>‖y+a‖^2) x :=
        ((contDiff_id.add contDiff_const).norm_sq (𝕜:=ℝ) : ContDiff ℝ ∞ (fun y:E=>‖y+a‖^2)).contDiffAt.of_le (nat_le_inf i)
      change ‖iteratedFDeriv ℝ i ((-c) • (fun y:E=>‖y+a‖^2)) x‖≤_
      rw [iteratedFDeriv_const_smul_apply hsi,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg hc]
      have hR : 1≤(‖x+a‖+1)^2 := by nlinarith [norm_nonneg (x+a)]
      have hM : 1≤max c 1 := le_max_right _ _
      have hp : max c 1*(‖x+a‖+1)^2 ≤ (max c 1*(‖x+a‖+1)^2)^i := by
        simpa only [pow_one] using (pow_le_pow_right₀ (by nlinarith : 1≤max c 1*(‖x+a‖+1)^2) hi)
      calc
       _ ≤ c*((2:ℝ)^i*(‖x+a‖+1)^2) := mul_le_mul_of_nonneg_left (square_iterated_bound a x i) hc
       _ ≤ (2:ℝ)^i*(max c 1*(‖x+a‖+1)^2) := by
         have hh := mul_le_mul_of_nonneg_right (le_max_left c 1) (show 0≤(2:ℝ)^i*(‖x+a‖+1)^2 by positivity)
         nlinarith only [hh]
       _ ≤ (2:ℝ)^i*(max c 1*(‖x+a‖+1)^2)^i := mul_le_mul_of_nonneg_left hp (by positivity)
       _ = (2*max c 1*(‖x+a‖+1)^2)^i := by rw [← mul_pow];congr 1;ring
  have lattice_norm_sq {d:ℕ} (n:Fin d→ℤ) : ‖latticePoint n‖^2=∑j,(n j:ℝ)^2 := by
   rw [EuclideanSpace.real_norm_sq_eq] <;> rfl
  have shifted_polynomial_bound {d:ℕ} (y:EuclideanSpace ℝ (Fin d)) (n:Fin d→ℤ)
   (R:ℝ) (hR:0≤R) (hy:‖y‖≤R) :
   (‖y+latticePoint n‖+1)^2 ≤ (2*(R+1)^2)*(1+∑j,(n j:ℝ)^2) := by
   have hh := norm_add_le y (latticePoint n)
   have hn0 := norm_nonneg (latticePoint n)
   have hsum : ‖y+latticePoint n‖+1≤(R+1)+‖latticePoint n‖ := by linarith
   have hs := pow_le_pow_left₀ (show 0≤‖y+latticePoint n‖+1 by positivity) hsum 2
   have hpoly : (R+1+‖latticePoint n‖)^2≤2*(R+1)^2+2*‖latticePoint n‖^2 := by
     nlinarith [sq_nonneg ((R+1)-‖latticePoint n‖)]
   have hR1 : 1≤(R+1)^2 := by nlinarith
   have hn2 := sq_nonneg ‖latticePoint n‖
   rw [← lattice_norm_sq n]
   nlinarith [mul_nonneg (sub_nonneg.mpr hR1) hn2]
  have gaussian_local_split {d:ℕ} (y:EuclideanSpace ℝ (Fin d)) (n:Fin d→ℤ)
   (R δ t:ℝ) (hR:0≤R) (hδ:0<δ) (hy:‖y‖≤R)
   (hsep:δ≤‖y+latticePoint n‖) (ht:0<t) (ht1:t≤1) :
   Real.exp (-‖y+latticePoint n‖^2/(4*t)) ≤
   Real.exp (-δ^2/(8*t))*
   Real.exp (-(δ^2/(16*(δ^2+R^2+1)))*(∑j,(n j:ℝ)^2)) := by
   let r:=‖y+latticePoint n‖
   let q:=‖latticePoint n‖^2
   let S:=δ^2+R^2+1
   have hr : 0≤r := norm_nonneg _
   have hq : 0≤q := sq_nonneg _
   have hS : 0<S := by dsimp [S];positivity
   have hδ2 : δ^2≤r^2 := pow_le_pow_left₀ hδ.le hsep 2
   have hh : ‖latticePoint n‖≤r+R := by
     have hh := norm_sub_le (y+latticePoint n) y
     simp only [add_sub_cancel_left] at hh
     dsimp [r];linarith
   have hh2 := pow_le_pow_left₀ (norm_nonneg (latticePoint n)) hh 2
   have hqr : q≤2*r^2+2*R^2 := by
     dsimp [q];nlinarith [sq_nonneg (r-R)]
   have hqδ : q*δ^2≤2*S*r^2 := by
     have h1:=mul_le_mul_of_nonneg_right hqr (sq_nonneg δ)
     have h2:=mul_le_mul_of_nonneg_left hδ2 (show 0≤2*R^2 by positivity)
     dsimp [S];nlinarith [sq_nonneg r]
   have hgq : δ^2/(16*S)*q≤r^2/8 := by
     rw [div_mul_eq_mul_div]
     apply (div_le_iff₀ (show 0<16*S by positivity)).mpr
     calc
      δ^2*q ≤ 2*S*r^2 := by nlinarith only [hqδ]
      _ = r^2/8*(16*S) := by ring
   have hgt : r^2/8≤r^2/(8*t) := by
     apply (le_div_iff₀ (show 0<8*t by positivity)).mpr
     nlinarith [mul_le_of_le_one_right (sq_nonneg r) ht1]
   have hds : δ^2/(8*t)≤r^2/(8*t) := div_le_div_of_nonneg_right hδ2 (by positivity)
   rw [← Real.exp_add]
   apply Real.exp_le_exp.mpr
   rw [← lattice_norm_sq n]
   change -r^2/(4*t)≤ -δ^2/(8*t)+ -(δ^2/(16*S))*q
   have hsum : δ^2/(8*t)+δ^2/(16*S)*q≤r^2/(4*t) := by
     calc
      _ ≤ r^2/(8*t)+r^2/(8*t) := add_le_add hds (hgq.trans hgt)
      _ = _ := by ring
   simpa only [neg_add,neg_div,neg_mul] using neg_le_neg hsum
  have gaussian_smalltime_derivative_bound {E:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
   (a x:E) (t:ℝ) (ht:0<t) (ht1:t≤1) (m:ℕ) :
   ‖iteratedFDeriv ℝ m (fun y:E=>Real.exp (-‖y+a‖^2/(4*t))) x‖ ≤
   (m.factorial:ℝ)*Real.exp (-‖x+a‖^2/(4*t))*
     ((2*(‖x+a‖+1)^2)/t)^m := by
   have heq : (fun y:E=>Real.exp (-‖y+a‖^2/(4*t)))=
       (fun y:E=>Real.exp (-(1/(4*t))*‖y+a‖^2)) := by
     funext y;congr 1;ring
   rw [heq]
   have hm : max (1/(4*t)) 1≤1/t := by
     apply max_le
     · apply (div_le_div_iff_of_pos_left (by norm_num : (0:ℝ)<1) (by positivity) ht).mpr
       linarith
     · apply (le_div_iff₀ ht).mpr;linarith
   have hD : 2*max (1/(4*t)) 1*(‖x+a‖+1)^2 ≤ (2*(‖x+a‖+1)^2)/t := by
     have hh:=mul_le_mul_of_nonneg_right hm (show 0≤2*(‖x+a‖+1)^2 by positivity)
     simpa only [div_eq_mul_inv,one_mul,mul_assoc,mul_comm,mul_left_comm] using hh
   calc
    _ ≤ (m.factorial:ℝ)*Real.exp (-(1/(4*t))*‖x+a‖^2)*
       (2*max (1/(4*t)) 1*(‖x+a‖+1)^2)^m :=
         exponential_square_bound a x (1/(4*t)) (by positivity) m
    _ ≤ (m.factorial:ℝ)*Real.exp (-(1/(4*t))*‖x+a‖^2)*
       ((2*(‖x+a‖+1)^2)/t)^m := mul_le_mul_of_nonneg_left
         (pow_le_pow_left₀ (by positivity) hD m) (by positivity)
    _ = _ := by congr 2;congr 1;ring
  have gaussian_local_derivative_bound {d:ℕ} (y:EuclideanSpace ℝ (Fin d)) (n:Fin d→ℤ)
   (R δ t:ℝ) (hR:0≤R) (hδ:0<δ) (hy:‖y‖≤R)
   (hsep:δ≤‖y+latticePoint n‖) (ht:0<t) (ht1:t≤1) (m:ℕ) :
   ‖iteratedFDeriv ℝ m (fun z:EuclideanSpace ℝ (Fin d)=>
       Real.exp (-‖z+latticePoint n‖^2/(4*t))) y‖ ≤
   (m.factorial:ℝ)*(4*(R+1)^2)^m*
   (t⁻¹)^m*Real.exp (-δ^2/(8*t))*
   (Real.exp (-(δ^2/(16*(δ^2+R^2+1)))*(∑j,(n j:ℝ)^2))*(1+∑j,(n j:ℝ)^2)^m) := by
   have hpoly := shifted_polynomial_bound y n R hR hy
   have hD : (2*(‖y+latticePoint n‖+1)^2)/t≤
       (4*(R+1)^2)*(1+∑j,(n j:ℝ)^2)*t⁻¹ := by
     calc
      _ = (2/t)*(‖y+latticePoint n‖+1)^2 := by ring
      _ ≤ (2/t)*((2*(R+1)^2)*(1+∑j,(n j:ℝ)^2)) :=
        mul_le_mul_of_nonneg_left hpoly (by positivity)
      _ = _ := by ring
   have hb := gaussian_smalltime_derivative_bound (latticePoint n) y t ht ht1 m
   calc
    _ ≤ (m.factorial:ℝ)*(Real.exp (-δ^2/(8*t))*
          Real.exp (-(δ^2/(16*(δ^2+R^2+1)))*(∑j,(n j:ℝ)^2)))*
         (((4*(R+1)^2)*(1+∑j,(n j:ℝ)^2)*t⁻¹)^m) := hb.trans
      (mul_le_mul
        (mul_le_mul_of_nonneg_left (gaussian_local_split y n R δ t hR hδ hy hsep ht ht1) (by positivity))
        (pow_le_pow_left₀ (by positivity) hD m) (by positivity) (by positivity))
    _ = _ := by simp only [mul_pow];ring
  
  have polynomial_gaussian_bound (c:ℝ) (hc:0<c) (n:ℕ) :
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
  
  have polynomial_gaussian_summable (d:ℕ) (c:ℝ) (hc:0<c) (n:ℕ) :
      Summable (fun k:Fin d→ℤ=>Real.exp (-c*∑j,(k j:ℝ)^2)*(1+∑j,(k j:ℝ)^2)^n) := by
    obtain ⟨C,hC,hb⟩ := polynomial_gaussian_bound c hc n
    have hg := (gaussian_lattice_summable d (c/2) (half_pos hc)).mul_left C
    apply Summable.of_nonneg_of_le
      (fun k=>by positivity)
      (fun k=>by simpa only [add_comm] using hb (∑j,(k j:ℝ)^2) (Finset.sum_nonneg (fun _ _=>sq_nonneg _))) hg
  
  have partial_iterated_smooth {T E F:Type} [NormedAddCommGroup T] [NormedSpace ℝ T] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (f:T→E→F)
   (hf:ContDiff ℝ ∞ f.uncurry) (n:ℕ) :
   ContDiff ℝ ∞ (fun p:T×E=>iteratedFDeriv ℝ n (f p.1) p.2) := by
   induction n with
   | zero =>
     have heq : (fun p:T×E=>iteratedFDeriv ℝ 0 (f p.1) p.2)=
       (fun p=>((continuousMultilinearCurryFin0 ℝ E F).symm : F→L[ℝ] E[×0]→L[ℝ]F) (f.uncurry p)) := by
       funext p
       ext m
       simp [Function.uncurry]
     rw [heq]
     exact ((continuousMultilinearCurryFin0 ℝ E F).symm : F→L[ℝ] E[×0]→L[ℝ]F).contDiff.comp hf
   | succ n ih =>
     have hg : ContDiff ℝ ∞ (fun p:(T×E)×E => iteratedFDeriv ℝ n (f p.1.1) p.2) :=
       ih.comp ((contDiff_fst.fst).prodMk contDiff_snd)
     have hd : ContDiff ℝ ∞ (fun p:T×E=>fderiv ℝ (fun z:E=>iteratedFDeriv ℝ n (f p.1) z) p.2) :=
       hg.fderiv contDiff_snd (by simp)
     simp only [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply]
     exact ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) F).symm :
         (E→L[ℝ]E[×n]→L[ℝ]F)→L[ℝ]E[×(n+1)]→L[ℝ]F).contDiff.comp hd
  
  have inverse_gaussian_integrable (β c : ℝ) (hc : 0 < c) :
      IntegrableOn (fun t : ℝ => t^β*Real.exp (-c/t)) (Ioc 0 1) volume := by
    classical
    let f := fun t : ℝ => t^β*Real.exp (-c/t)
    have hlim : Tendsto f (𝓝[>] 0) (𝓝 0) := by
      have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-β) c hc).comp
        (tendsto_inv_nhdsGT_zero)
      apply h.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      change 0 < t at ht
      dsimp [f]
      rw [Real.inv_rpow ht.le,← Real.rpow_neg ht.le]
      congr 2
      ring
    have hc : ContinuousOn (Function.update f 0 0) (Icc 0 1) := by
      rw [continuousOn_update_iff]
      refine ⟨?_,fun _ => hlim.mono_left (nhdsWithin_mono _ ?_)⟩
      · intro t ht
        have ht0 : t ≠ 0 := by simpa using ht.2
        have htpos : 0 < t := lt_of_le_of_ne ht.1.1 (Ne.symm ht0)
        exact ((Real.continuousAt_rpow_const t β (Or.inl ht0)).mul
          (Real.continuous_exp.continuousAt.comp
            (continuousAt_const.div continuousAt_id ht0))).continuousWithinAt
      · intro t ht
        have ht0 : t ≠ 0 := by simpa using ht.2
        exact lt_of_le_of_ne ht.1.1 (Ne.symm ht0)
    have hi : IntegrableOn (Function.update f 0 0) (Icc 0 1) volume := hc.integrableOn_Icc
    have hi' := hi.mono_set Ioc_subset_Icc_self
    apply hi'.congr_fun _ measurableSet_Ioc
    intro t ht
    rw [Function.update_of_ne (ne_of_gt ht.1)]
  let image {d:ℕ} (α:ℝ) (n:Fin d→ℤ) (t:ℝ) (y:EuclideanSpace ℝ (Fin d)) :ℝ :=
   t^(α-1)*(4*Real.pi*t)^(-(d:ℝ)/2)*Real.exp (-‖y+latticePoint n‖^2/(4*t))
  have image_smooth {d:ℕ} (α:ℝ) (n:Fin d→ℤ) (t:ℝ) : ContDiff ℝ ∞ (image α n t) := by
   change ContDiff ℝ ∞ (fun y:EuclideanSpace ℝ (Fin d)=>
   t^(α-1)*(4*Real.pi*t)^(-(d:ℝ)/2)*Real.exp (-‖y+latticePoint n‖^2/(4*t)))
   apply contDiff_const.mul
   apply Real.contDiff_exp.comp
   exact ((contDiff_id.add contDiff_const).norm_sq (𝕜:=ℝ)).neg.div_const _
  have image_exp_joint_smooth {d:ℕ} (α:ℝ) (n:Fin d→ℤ) :
   ContDiff ℝ ∞ (fun p:ℝ×EuclideanSpace ℝ (Fin d)=>image α n (Real.exp p.1) p.2) := by
   dsimp [image]
   have ht : ContDiff ℝ ∞ (fun p:ℝ×EuclideanSpace ℝ (Fin d)=>Real.exp p.1) := Real.contDiff_exp.comp contDiff_fst
   have h4 : ContDiff ℝ ∞ (fun p:ℝ×EuclideanSpace ℝ (Fin d)=>4*Real.pi*Real.exp p.1) := contDiff_const.mul ht
   apply ((ht.rpow_const_of_ne (fun _=>ne_of_gt (Real.exp_pos _))).mul
     (h4.rpow_const_of_ne (fun _=>by positivity))).mul
   apply Real.contDiff_exp.comp
   exact ((contDiff_snd.add contDiff_const).norm_sq (𝕜:=ℝ)).neg.div (contDiff_const.mul ht) (fun _=>by positivity)
  have image_derivative_measurable {d:ℕ} (α:ℝ) (n:Fin d→ℤ) (y:EuclideanSpace ℝ (Fin d)) (m:ℕ) :
   MeasureTheory.AEStronglyMeasurable
     (fun t:ℝ=>iteratedFDeriv ℝ m (image α n t) y)
     (MeasureTheory.volume.restrict (Set.Ioc 0 1)) := by
   have hc := (partial_iterated_smooth
     (fun u:ℝ=>image α n (Real.exp u)) (image_exp_joint_smooth α n) m).continuous
   have hm := hc.stronglyMeasurable.comp_measurable (Real.measurable_log.prodMk (measurable_const (a:=y)))
   have hae : (fun t:ℝ=>iteratedFDeriv ℝ m (image α n t) y)=ᵐ[MeasureTheory.volume.restrict (Set.Ioc 0 1)]
     (fun t=>iteratedFDeriv ℝ m (image α n (Real.exp (Real.log t))) y) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.exp_log ht.1]
   exact hm.aestronglyMeasurable.congr hae.symm
  have image_derivative_local_bound {d:ℕ} (α:ℝ) (y:EuclideanSpace ℝ (Fin d)) (n:Fin d→ℤ)
   (R δ t:ℝ) (hR:0≤R) (hδ:0<δ) (hy:‖y‖≤R)
   (hsep:δ≤‖y+latticePoint n‖) (ht:0<t) (ht1:t≤1) (m:ℕ) :
   ‖iteratedFDeriv ℝ m (image α n t) y‖ ≤
   (t^(α-1)*(4*Real.pi*t)^(-(d:ℝ)/2))*
   ((m.factorial:ℝ)*(4*(R+1)^2)^m*(t⁻¹)^m*Real.exp (-δ^2/(8*t))*
   (Real.exp (-(δ^2/(16*(δ^2+R^2+1)))*(∑j,(n j:ℝ)^2))*(1+∑j,(n j:ℝ)^2)^m)) := by
   have hg : ContDiffAt ℝ m (fun z:EuclideanSpace ℝ (Fin d)=>
      Real.exp (-‖z+latticePoint n‖^2/(4*t))) y := by
    apply (Real.contDiff_exp.comp (((contDiff_id.add contDiff_const).norm_sq (𝕜:=ℝ)).neg.div_const (4*t))).contDiffAt.of_le
    exact nat_le_inf m
   change ‖iteratedFDeriv ℝ m ((t^(α-1)*(4*Real.pi*t)^(-(d:ℝ)/2)) •
      (fun z:EuclideanSpace ℝ (Fin d)=>Real.exp (-‖z+latticePoint n‖^2/(4*t)))) y‖≤_
   rw [iteratedFDeriv_const_smul_apply hg,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
   exact mul_le_mul_of_nonneg_left (gaussian_local_derivative_bound y n R δ t hR hδ hy hsep ht ht1 m) (by positivity)
  let μ (d:ℕ) : Measure (ℝ × (Fin d→ℤ)) :=
   (volume.restrict (Ioc 0 1)).prod Measure.count
  have image_product_derivative_measurable (d:ℕ) (α:ℝ) (y:EuclideanSpace ℝ (Fin d)) (m:ℕ) :
   AEStronglyMeasurable (fun p:ℝ×(Fin d→ℤ)=>iteratedFDeriv ℝ m (image α p.2 p.1) y) (μ d) := by
   letI : MeasurableSpace (EuclideanSpace ℝ (Fin d)[×m]→L[ℝ]ℝ) := borel _
   letI : BorelSpace (EuclideanSpace ℝ (Fin d)[×m]→L[ℝ]ℝ) := ⟨rfl⟩
   have hbranch (n:Fin d→ℤ) : StronglyMeasurable (fun t:ℝ=>
       iteratedFDeriv ℝ m (image α n (Real.exp (Real.log t))) y) := by
     have hc := (partial_iterated_smooth
       (fun u:ℝ=>image α n (Real.exp u)) (image_exp_joint_smooth α n) m).continuous
     exact hc.stronglyMeasurable.comp_measurable (Real.measurable_log.prodMk (measurable_const (a:=y)))
   have hm : StronglyMeasurable (fun p:ℝ×(Fin d→ℤ)=>
       iteratedFDeriv ℝ m (image α p.2 (Real.exp (Real.log p.1))) y) := by
     apply stronglyMeasurable_iff_measurable_separable.mpr
     constructor
     · exact measurable_from_prod_countable_left (fun n=>(hbranch n).measurable)
     · have hs := TopologicalSpace.IsSeparable.iUnion (fun n=>(hbranch n).isSeparable_range)
       apply hs.mono
       rintro _ ⟨⟨t,n⟩,rfl⟩
       exact Set.mem_iUnion.mpr ⟨n,Set.mem_range_self t⟩
   have hpos : ∀ᵐp:ℝ×(Fin d→ℤ)∂μ d, 0<p.1 := by
     apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const measurable_fst)).mpr
     filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
     exact Filter.Eventually.of_forall (fun n=>ht.1)
   apply hm.aestronglyMeasurable.congr
   filter_upwards [hpos] with p hp
   rw [Real.exp_log hp]
  let timeBound (d:ℕ) (α δ:ℝ) (m:ℕ) (t:ℝ) :ℝ :=
   t^(α-1)*(4*Real.pi*t)^(-(d:ℝ)/2)*(t⁻¹)^m*Real.exp (-δ^2/(8*t))
  have timeBound_integrable (d:ℕ) (α δ:ℝ) (hδ:0<δ) (m:ℕ) :
   IntegrableOn (timeBound d α δ m) (Ioc 0 1) volume := by
   have hi : IntegrableOn (fun t:ℝ=>(4*Real.pi)^(-(d:ℝ)/2)*(t^(α-1-(d:ℝ)/2-(m:ℝ))*Real.exp (-(δ^2/8)/t))) (Ioc 0 1) volume := (inverse_gaussian_integrable (α-1-(d:ℝ)/2-(m:ℝ)) (δ^2/8) (by positivity)).const_mul
      ((4*Real.pi)^(-(d:ℝ)/2))
   apply hi.congr_fun _ measurableSet_Ioc
   intro t ht
   symm
   dsimp [timeBound]
   rw [Real.mul_rpow (show 0≤4*Real.pi by positivity) ht.1.le]
   rw [←Real.rpow_natCast (t⁻¹) m,Real.inv_rpow ht.1.le,←Real.rpow_neg ht.1.le]
   have he : -(δ^2/8)/t = -δ^2/(8*t) := by ring
   rw [he]
   calc
    _ = ((4*Real.pi)^(-(d:ℝ)/2)) *
      ((t^(α-1)*t^(-(d:ℝ)/2)*t^(-(m:ℝ)))*Real.exp (-δ^2/(8*t))) := by ring
    _ = _ := by rw [← Real.rpow_add ht.1,←Real.rpow_add ht.1];congr 3;ring
  let latticeBound (d:ℕ) (R δ:ℝ) (m:ℕ) (n:Fin d→ℤ) :ℝ :=
   Real.exp (-(δ^2/(16*(δ^2+R^2+1)))*(∑j,(n j:ℝ)^2))*(1+∑j,(n j:ℝ)^2)^m
  have latticeBound_integrable (d:ℕ) (R δ:ℝ) (hδ:0<δ) (m:ℕ) :
   Integrable (latticeBound d R δ m) Measure.count := by
   apply integrable_count_iff.mpr
   have hp (n:Fin d→ℤ) : 0≤latticeBound d R δ m n := by dsimp [latticeBound];positivity
   simp_rw [Real.norm_eq_abs,abs_of_nonneg (hp _)]
   exact
     polynomial_gaussian_summable d (δ^2/(16*(δ^2+R^2+1))) (by positivity) m
  have joint_bound_integrable (d:ℕ) (α R δ:ℝ) (hδ:0<δ) (m:ℕ) :
   Integrable (fun p:ℝ×(Fin d→ℤ)=>(m.factorial:ℝ)*(4*(R+1)^2)^m*
     timeBound d α δ m p.1*latticeBound d R δ m p.2) (μ d) := by
   have hi := ((timeBound_integrable d α δ hδ m).mul_prod (latticeBound_integrable d R δ hδ m)).const_mul
     ((m.factorial:ℝ)*(4*(R+1)^2)^m)
   apply hi.congr
   exact Filter.Eventually.of_forall (fun p=>by ring)
  have local_uniform_separation (d:ℕ) (y:EuclideanSpace ℝ (Fin d)) (hy:TorusLift d y≠0) :
   ∃ρ R δ:ℝ, 0<ρ ∧ 0≤R ∧ 0<δ ∧
   ∀z:EuclideanSpace ℝ (Fin d),z∈Metric.ball y ρ→
     ‖z‖≤R ∧ ∀n:Fin d→ℤ,δ≤‖z+latticePoint n‖ := by
   obtain ⟨η,hη,hsep⟩ := distance_to_lattice d y hy
   refine ⟨min (η/2) 1,‖y‖+1,η/2,lt_min (half_pos hη) zero_lt_one,
     by positivity,half_pos hη,?_⟩
   intro z hz
   have hd : ‖z-y‖<min (η/2) 1 := by simpa only [Metric.mem_ball,dist_eq_norm] using hz
   have hnorm : ‖z‖≤‖z-y‖+‖y‖ := by
     simpa only [sub_add_cancel] using norm_add_le (z-y) y
   refine ⟨by linarith [min_le_right (η/2) (1:ℝ)],?_⟩
   intro n
   have ht : ‖y+latticePoint n‖≤‖y-z‖+‖z+latticePoint n‖ := by
     convert norm_add_le (y-z) (z+latticePoint n) using 1 <;> abel
   rw [norm_sub_rev] at ht
   linarith [hsep n,min_le_left (η/2) (1:ℝ)]
  have image_local_dominated (d:ℕ) (α:ℝ) (y:EuclideanSpace ℝ (Fin d))
   (hy:TorusLift d y≠0) (m:ℕ) :
   ∃ρ:ℝ,0<ρ ∧ ∃b:ℝ×(Fin d→ℤ)→ℝ,Integrable b (μ d) ∧
     ∀ᵐp:ℝ×(Fin d→ℤ)∂μ d,∀z∈Metric.ball y ρ,
       ‖iteratedFDeriv ℝ m (image α p.2 p.1) z‖≤b p := by
   obtain ⟨ρ,R,δ,hρ,hR,hδ,hsep⟩:=local_uniform_separation d y hy
   refine ⟨ρ,hρ,(fun p=>(m.factorial:ℝ)*(4*(R+1)^2)^m*
     timeBound d α δ m p.1*latticeBound d R δ m p.2),joint_bound_integrable d α R δ hδ m,?_⟩
   have ht : ∀ᵐp:ℝ×(Fin d→ℤ)∂μ d,p.1∈Ioc 0 1 := by
     apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_fst)).mpr
     filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
     exact Filter.Eventually.of_forall (fun n=>ht)
   filter_upwards [ht] with p hp
   intro z hz
   obtain ⟨hzR,hzn⟩:=hsep z hz
   have hb:=image_derivative_local_bound α z p.2 R δ p.1 hR hδ hzR (hzn p.2) hp.1 hp.2 m
   calc
    _ ≤ (p.1^(α-1)*(4*Real.pi*p.1)^(-(d:ℝ)/2))*
      ((m.factorial:ℝ)*(4*(R+1)^2)^m*(p.1⁻¹)^m*Real.exp (-δ^2/(8*p.1))*
        (Real.exp (-(δ^2/(16*(δ^2+R^2+1)))*(∑j,(p.2 j:ℝ)^2))*(1+∑j,(p.2 j:ℝ)^2)^m)) := hb
    _ = _ := by dsimp [timeBound,latticeBound];ring
  have short_images_smooth (d:ℕ) (α:ℝ) :
   ContDiffOn ℝ ∞ (fun y:EuclideanSpace ℝ (Fin d)=>
    ∫p:ℝ×(Fin d→ℤ),image α p.2 p.1 y∂μ d) {y|TorusLift d y≠0} := by
   apply DominatedSmoothIntegral (μ d) {y|TorusLift d y≠0}
     (isOpen_compl_singleton.preimage (lift_continuous d))
     (fun y p=>image α p.2 p.1 y)
   · exact Filter.Eventually.of_forall (fun p=>image_smooth α p.2 p.1)
   · intro m y hy
     exact image_product_derivative_measurable d α y m
   · intro y hy m
     exact image_local_dominated d α y hy m
  have short_images_integrable (d:ℕ) (α:ℝ) (y:EuclideanSpace ℝ (Fin d)) (hy:TorusLift d y≠0) :
   Integrable (fun p:ℝ×(Fin d→ℤ)=>image α p.2 p.1 y) (μ d) := by
   obtain ⟨ρ,hρ,b,hbi,hb⟩:=image_local_dominated d α y hy 0
   have hm := image_product_derivative_measurable d α y 0
   simp only [norm_iteratedFDeriv_zero] at hb
   have hmeas : AEStronglyMeasurable (fun p:ℝ×(Fin d→ℤ)=>image α p.2 p.1 y) (μ d) := by
     simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,LinearIsometryEquiv.apply_symm_apply] using
       (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin d)) ℝ).continuous.comp_aestronglyMeasurable hm
   apply hbi.mono' hmeas
   filter_upwards [hb] with p hp
   exact hp y (Metric.mem_ball_self hρ)
  have image_tsum (d : ℕ) (α t : ℝ) (ht : 0 < t)
      (y : EuclideanSpace ℝ (Fin d)) :
      (∑' n : Fin d → ℤ, image α n t y) =
        t^(α-1) * HeatKernel d t (TorusLift d y) := by
    rw [(RieszGaussianImageRemainder d).1 t ht y]
    simp only [image, EuclideanSpace.real_norm_sq_eq]
    change (∑' n : Fin d → ℤ,
      (t^(α-1)*(4*Real.pi*t)^(-(d:ℝ)/2)) *
        Real.exp (-(∑ j, (y j + (n j:ℝ))^2)/(4*t))) = _
    rw [tsum_mul_left]
    ring
  have weighted_heat_integrable_and_product_eq (d : ℕ) (α : ℝ)
      (y : EuclideanSpace ℝ (Fin d))
      (hF : Integrable (fun p : ℝ × (Fin d → ℤ) => image α p.2 p.1 y) (μ d)) :
      IntegrableOn (fun t : ℝ => t^(α-1)*HeatKernel d t (TorusLift d y)) (Ioc 0 1) volume ∧
      (∫ p : ℝ × (Fin d → ℤ), image α p.2 p.1 y ∂μ d) =
        ∫ t in Ioc 0 1, t^(α-1)*HeatKernel d t (TorusLift d y) := by
    have hF' : Integrable (fun p : ℝ × (Fin d → ℤ) => image α p.2 p.1 y)
        ((volume.restrict (Ioc 0 1)).prod Measure.count) := hF
    have hae : (fun t : ℝ => ∫ n : Fin d → ℤ, image α n t y ∂Measure.count)
        =ᵐ[volume.restrict (Ioc 0 1)]
        (fun t : ℝ => t^(α-1)*HeatKernel d t (TorusLift d y)) := by
      filter_upwards [hF'.prod_right_ae, ae_restrict_mem measurableSet_Ioc] with t hf ht
      rw [integral_countable hf]
      simp only [count_real_singleton, one_smul]
      exact image_tsum d α t ht.1 y
    refine ⟨hF'.integral_prod_left.congr hae, ?_⟩
    change (∫ p : ℝ × (Fin d → ℤ), image α p.2 p.1 y
      ∂((volume.restrict (Ioc 0 1)).prod Measure.count)) = _
    rw [integral_prod _ hF']
    exact integral_congr_ae hae
  have weighted_heat_sub_one (d : ℕ) (α : ℝ) (hα : 0 < α)
      (y : EuclideanSpace ℝ (Fin d))
      (hF : Integrable (fun p : ℝ × (Fin d → ℤ) => image α p.2 p.1 y) (μ d)) :
      IntegrableOn (fun t : ℝ => t^(α-1)*(HeatKernel d t (TorusLift d y)-1))
        (Ioc 0 1) volume ∧
      (∫ t in Ioc 0 1, t^(α-1)*(HeatKernel d t (TorusLift d y)-1)) =
        (∫ p : ℝ × (Fin d → ℤ), image α p.2 p.1 y ∂μ d) -
        ∫ t in Ioc 0 1, t^(α-1) := by
    obtain ⟨hh, he⟩ := weighted_heat_integrable_and_product_eq d α y hF
    have hw : IntegrableOn (fun t : ℝ => t^(α-1)) (Ioc 0 1) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))
    have hfun : (fun t : ℝ => t^(α-1)*(HeatKernel d t (TorusLift d y)-1)) =
        (fun t : ℝ => t^(α-1)*HeatKernel d t (TorusLift d y)-t^(α-1)) := by
      funext t
      ring
    rw [hfun]
    exact ⟨hh.sub hw, by rw [integral_sub hh hw, he]⟩
  have off_zero_weighted_heat_sub_one (d : ℕ) (α : ℝ) (hα : 0 < α)
      (y : EuclideanSpace ℝ (Fin d)) (hy : TorusLift d y ≠ 0) :
      IntegrableOn (fun t : ℝ => t^(α-1)*(HeatKernel d t (TorusLift d y)-1))
        (Ioc 0 1) volume ∧
      (∫ t in Ioc 0 1, t^(α-1)*(HeatKernel d t (TorusLift d y)-1)) =
        (∫ p : ℝ × (Fin d → ℤ), image α p.2 p.1 y ∂μ d) -
        ∫ t in Ioc 0 1, t^(α-1) :=
    weighted_heat_sub_one d α hα y (short_images_integrable d α y hy)
  have off_zero_short_heat_smooth (d : ℕ) (α : ℝ) (hα : 0 < α) :
      ContDiffOn ℝ ∞
        (fun y : EuclideanSpace ℝ (Fin d) =>
          ∫ t in Ioc 0 1, t^(α-1)*(HeatKernel d t (TorusLift d y)-1))
        {y | TorusLift d y ≠ 0} := by
    apply ((short_images_smooth d α).sub
      (contDiffOn_const (c := ∫ t in Ioc 0 1, t^(α-1)))).congr
    intro y hy
    exact (off_zero_weighted_heat_sub_one d α hα y hy).2
  let α : ℝ := ((d:ℝ)-s)/2
  have hα : 0<α := by dsimp [α];linarith
  let A : ℝ := a/Real.Gamma α
  have hshort : ContDiffOn ℝ ∞ (fun y:EuclideanSpace ℝ (Fin d)=>
    (∫p:ℝ×(Fin d→ℤ),image α p.2 p.1 y∂μ d)-∫t in Ioc 0 1,t^(α-1))
      {y|TorusLift d y≠0} := (short_images_smooth d α).sub contDiffOn_const
  have htail := (RieszHeatTail d α hα).1
  have hmodel : ContDiffOn ℝ ∞ (fun y:EuclideanSpace ℝ (Fin d)=>A*
     (((∫p:ℝ×(Fin d→ℤ),image α p.2 p.1 y∂μ d)-∫t in Ioc 0 1,t^(α-1))+
       ∫t in Ioi 1,t^(α-1)*(HeatKernel d t (TorusLift d y)-1)))
       {y|TorusLift d y≠0} := contDiffOn_const.mul (hshort.add htail.contDiffOn)
  apply hmodel.congr
  intro y hy
  change TorusLift d y≠0 at hy
  obtain ⟨hsint,hseq⟩:=off_zero_weighted_heat_sub_one d α hα y hy
  obtain ⟨C,hC,htailint⟩:=(RieszHeatTail d α hα).2
  have htint:IntegrableOn (fun t:ℝ=>t^(α-1)*(HeatKernel d t (TorusLift d y)-1)) (Ioi 1) volume :=
    (htailint (TorusLift d y)).1
  have hsplit : (∫t in Ioi 0,t^(α-1)*(HeatKernel d t (TorusLift d y)-1))=
    (∫t in Ioc 0 1,t^(α-1)*(HeatKernel d t (TorusLift d y)-1))+
    (∫t in Ioi 1,t^(α-1)*(HeatKernel d t (TorusLift d y)-1)) := by
    rw [←Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ)≤1),
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hsint htint]
  have hk : RieszKernel d s a 0 (TorusLift d y)=
    A*(∫t in Ioi 0,t^(α-1)*(HeatKernel d t (TorusLift d y)-1)) := by
    simp only [RieszKernel,hy,and_false,if_false,add_zero]
    rfl
  rw [hk,hsplit,hseq]
