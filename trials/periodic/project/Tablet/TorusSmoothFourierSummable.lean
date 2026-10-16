import Tablet.TorusFourierLaplacian
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
open MeasureTheory Filter Set UnitAddTorus
set_option maxHeartbeats 1500000
-- [TABLET NODE: TorusSmoothFourierSummable]
theorem TorusSmoothFourierSummable (d : ℕ) (f : UnitAddTorus (Fin d)→ℝ)
    (hf : TorusSmooth f) :
    Summable (UnitAddTorus.mFourierCoeff (fun x => (f x:ℂ))) := by
-- BODY
  classical
  have coordinate_weight : Summable (fun n:ℤ=>1/(1+(n:ℝ)^2)) := by
    have hs := (Real.summable_one_div_int_pow (p:=2)).2 (by norm_num)
    have hz : Summable (fun n:ℤ=>if n=0 then (1:ℝ) else 0) := (hasSum_ite_eq _ _).summable
    apply (hz.add hs).of_nonneg_of_le
    · intro n; positivity
    · intro n
      by_cases hn:n=0
      · simp [hn]
      · simp only [if_neg hn,zero_add]
        have hn' : (n:ℝ)≠0 := by exact_mod_cast hn
        exact one_div_le_one_div_of_le (sq_pos_of_ne_zero hn') (by linarith [sq_nonneg (n:ℝ)])

  have lattice_weight (d:ℕ) : Summable (fun k:Fin d→ℤ=>∏j:Fin d,1/(1+(k j:ℝ)^2)) := by
    induction d with
    | zero => exact (hasSum_fintype _).summable
    | succ d ih =>
      have hs := coordinate_weight.mul_of_nonneg ih (fun _=>by positivity) (fun _=>by positivity)
      apply (Fin.consEquiv (fun _:Fin (d+1)=>ℤ)).summable_iff.mp
      convert hs using 1
      ext k
      simp only [Function.comp_apply,Fin.consEquiv_apply,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]

  have volume_eq_haar (d:ℕ) : (volume:Measure (UnitAddTorus (Fin d)))=Measure.pi (fun _:Fin d=>AddCircle.haarAddCircle) := by
    change Measure.pi _ = _
    congr 1;funext j
    rw [AddCircle.volume_eq_smul_haarAddCircle];simp

  have coefficient_laplacian (d:ℕ) (f:UnitAddTorus (Fin d)→ℝ) (hf:TorusSmooth f) (k:Fin d→ℤ) :
      mFourierCoeff (fun x=>(TorusLaplacian f x:ℂ)) k =
        ((-(4*Real.pi^2*∑j,(k j:ℝ)^2):ℝ):ℂ)*mFourierCoeff (fun x=>(f x:ℂ)) k := by
    unfold mFourierCoeff
    simp only [smul_eq_mul]
    change (∫t, mFourier (-k) t * (TorusLaplacian f t:ℂ) ∂Measure.pi (fun _:Fin d=>AddCircle.haarAddCircle)) = _
    change _ = ((-(4*Real.pi^2*∑j,(k j:ℝ)^2):ℝ):ℂ)*(∫t,mFourier (-k) t * (f t:ℂ) ∂Measure.pi (fun _:Fin d=>AddCircle.haarAddCircle))
    rw [←volume_eq_haar]
    have hh := (TorusFourierLaplacian d f hf).2.2.2 (-k)
    simpa only [Pi.neg_apply,Int.cast_neg,neg_sq,mul_comm] using hh

  have iterated_coefficients (d:ℕ) (f:UnitAddTorus (Fin d)→ℝ) (hf:TorusSmooth f) :
      ∀n:ℕ,TorusSmooth ((TorusLaplacian (d:=d))^[n] f) ∧
        ∀k:Fin d→ℤ,mFourierCoeff (fun x=>(((TorusLaplacian (d:=d))^[n] f) x:ℂ)) k =
          ((-(4*Real.pi^2*∑j,(k j:ℝ)^2):ℝ):ℂ)^n * mFourierCoeff (fun x=>(f x:ℂ)) k := by
    intro n
    induction n with
    | zero => exact ⟨hf,fun k=>by simp⟩
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      refine ⟨(TorusFourierLaplacian d _ ih.1).2.1,?_⟩
      intro k
      rw [coefficient_laplacian d _ ih.1 k,ih.2 k,pow_succ]
      ring

  have coefficient_bound (d:ℕ) (f:UnitAddTorus (Fin d)→ℝ) (hf:Continuous f) (C:ℝ) (hC:∀x,‖f x‖≤C) :
      ∀k:Fin d→ℤ,‖mFourierCoeff (fun x=>(f x:ℂ)) k‖≤C := by
    intro k
    unfold mFourierCoeff
    have hb : ∀ᵐx∂Measure.pi (fun _:Fin d=>AddCircle.haarAddCircle), ‖mFourier (-k) x • (f x:ℂ)‖≤C :=
      Eventually.of_forall fun x=>by
        rw [norm_smul,show ‖mFourier (-k) x‖=1 from by
          simp only [mFourier,ContinuousMap.coe_mk,norm_prod,fourier_apply,Circle.norm_coe,Finset.prod_const_one],
          one_mul,Complex.norm_real]
        exact hC x
    change ‖∫x,mFourier (-k) x • (f x:ℂ) ∂Measure.pi (fun _:Fin d=>AddCircle.haarAddCircle)‖≤C
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const hb

  have coefficient_decay (d:ℕ) (f:UnitAddTorus (Fin d)→ℝ) (hf:TorusSmooth f) :
      ∃D:ℝ,0≤D ∧ ∀k:Fin d→ℤ,
        ‖mFourierCoeff (fun x=>(f x:ℂ)) k‖≤D*(∏j:Fin d,1/(1+(k j:ℝ)^2)) := by
    classical
    let g : C(UnitAddTorus (Fin d),ℝ) := ⟨(TorusLaplacian (d:=d))^[d] f,
      (TorusFourierLaplacian d _ (iterated_coefficients d f hf d).1).1⟩
    let C : ℝ := ‖g‖
    let a := mFourierCoeff (fun x=>(f x:ℂ))
    let D : ℝ := 2^d*C+‖a 0‖
    have hC : 0≤C := norm_nonneg _
    have hD : 0≤D := by dsimp [D]; positivity
    refine ⟨D,hD,fun k=>?_⟩
    change ‖a k‖≤_
    by_cases hk:k=0
    · subst k
      simp only [Pi.zero_apply,Int.cast_zero,zero_pow (by omega : 2≠0),add_zero,div_one,Finset.prod_const_one,mul_one]
      dsimp [D]
      exact le_add_of_nonneg_left (by positivity)
    have hj : ∃j:Fin d,k j≠0 := by
      by_contra h
      apply hk
      ext j
      simpa using not_exists.mp h j
    obtain ⟨j,hj⟩ := hj
    let S:ℝ := ∑i:Fin d,(k i:ℝ)^2
    let L:ℝ := 4*Real.pi^2*S
    have hS : 1≤S := by
      have hnj : (1:ℤ)≤(k j)^2 := by
        have hh := sq_pos_of_ne_zero hj
        omega
      have hnj' : (1:ℝ)≤(k j:ℝ)^2 := by exact_mod_cast hnj
      exact hnj'.trans (Finset.single_le_sum (fun i _=>sq_nonneg (k i:ℝ)) (Finset.mem_univ j))
    have hpi : (1:ℝ)≤4*Real.pi^2 := by nlinarith [Real.pi_gt_three]
    have hSL : S≤L := by dsimp [L];nlinarith
    have hL : 0<L := lt_of_lt_of_le (by linarith : 0<S) hSL
    have hLP : 0<L^d := pow_pos hL _
    let P:ℝ := ∏i:Fin d,(1+(k i:ℝ)^2)
    have hP : 0<P := Finset.prod_pos (fun i _=>by positivity)
    have hPL : P≤2^d*L^d := by
      have hprod : P≤∏i:Fin d,(2*L) := by
        apply Finset.prod_le_prod (fun i _=>by positivity)
        intro i _
        have hi : (k i:ℝ)^2≤S := Finset.single_le_sum (fun j _=>sq_nonneg (k j:ℝ)) (Finset.mem_univ i)
        linarith
      simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_pow] using hprod
    have hb := coefficient_bound d g g.continuous C g.norm_coe_le_norm k
    have hi := (iterated_coefficients d f hf d).2 k
    have hi' : L^d*‖a k‖≤C := by
      change ‖mFourierCoeff (fun x=>(((TorusLaplacian (d:=d))^[d] f) x:ℂ)) k‖≤C at hb
      rw [hi,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_neg,abs_of_pos hL] at hb
      exact hb
    have hPa : P*‖a k‖≤D := by
      have hh := mul_le_mul_of_nonneg_right hPL (norm_nonneg (a k))
      have hh' := mul_le_mul_of_nonneg_left hi' (by positivity : 0≤(2:ℝ)^d)
      calc
        P*‖a k‖ ≤ 2^d*L^d*‖a k‖ := hh
        _ = 2^d*(L^d*‖a k‖) := by ring
        _ ≤ 2^d*C := hh'
        _ ≤ D := by dsimp [D]; exact le_add_of_nonneg_right (norm_nonneg _)
    have hd : ‖a k‖≤D/P := (le_div_iff₀ hP).2 (by simpa only [mul_comm] using hPa)
    convert hd using 1
    rw [div_eq_mul_inv]
    congr 1
    simp only [P,one_div,Finset.prod_inv_distrib]

  obtain ⟨D,hD,hbound⟩ := coefficient_decay d f hf
  apply summable_norm_iff.mp
  exact ((lattice_weight d).mul_left D).of_nonneg_of_le
    (fun k=>norm_nonneg _) hbound
