import Tablet.RieszKernel
import Tablet.GaussianMellinAsymptotic
import Tablet.RieszGaussianImageRemainder
import Tablet.RieszHeatTail
import Mathlib.MeasureTheory.Integral.Bochner.Set
open MeasureTheory Set
-- [TABLET NODE: RieszZeroCutoffAsymptotic]
theorem RieszZeroCutoffAsymptotic (d : ℕ) (hd : 2 ≤ d) (s a : ℝ)
    (hs : 0 ≤ s) (hsd : s < (d : ℝ)) (ha : 0 < a) :
    ∃ b C : ℝ, 0 < b ∧ 0 ≤ C ∧
      ∀ y : EuclideanSpace ℝ (Fin d), 0 < ‖y‖ → ‖y‖ < 1 / 4 →
        |RieszKernel d s a 0 (TorusLift d y) -
          (if s = 0 then b * Real.log (1 / ‖y‖)
           else b * Real.rpow ‖y‖ (-s))| ≤ C := by
-- BODY
  have lift_ne_zero_small (d : ℕ) (y : EuclideanSpace ℝ (Fin d))
      (hy : 0 < ‖y‖) (hsmall : ‖y‖<1/4) : TorusLift d y≠0 := by
    intro h
    have hz : y=0 := by
      apply PiLp.ext
      intro j
      change y j=(0:ℝ)
      have hj : (y j:AddCircle (1:ℝ))=0 := congrFun h j
      obtain ⟨n,hn⟩ := (AddCircle.coe_eq_zero_iff (p:=(1:ℝ))).mp hj
      simp only [zsmul_eq_mul,mul_one] at hn
      have hb : |y j|<1/4 :=
        lt_of_le_of_lt (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le y j) hsmall
      have hnzero : n=0 := by
        by_contra hn0
        have hh : (1:ℤ) ≤ n ∨ n ≤ -1 := by omega
        rcases hh with hh | hh
        · have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hh
          linarith [(abs_lt.mp hb).1,(abs_lt.mp hb).2]
        · have : (n:ℝ) ≤ -1 := by exact_mod_cast hh
          linarith [(abs_lt.mp hb).1,(abs_lt.mp hb).2]
      simpa only [hnzero,Int.cast_zero] using hn.symm
    simpa [hz] using hy

  have time_integral_split (f z : ℝ → ℝ)
      (hz : IntegrableOn z (Ioc 0 1) volume)
      (hr : IntegrableOn (fun t => f t-z t) (Ioc 0 1) volume)
      (ht : IntegrableOn f (Ioi 1) volume) :
      IntegrableOn f (Ioi 0) volume  ∧ 
        (∫t in Ioi 0,f t)=(∫t in Ioc 0 1,z t)+
          (∫t in Ioc 0 1,f t-z t)+(∫t in Ioi 1,f t) := by
    have hs : IntegrableOn f (Ioc 0 1) volume := by
      apply (hz.add hr).congr_fun _ measurableSet_Ioc
      intro t ht
      simp
    constructor
    · rw [←Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 1),integrableOn_union]
      exact ⟨hs,ht⟩
    · rw [←Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 1),
        setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hs ht]
      congr 1
      rw [←integral_add hz hr]
      congr 1
      funext t
      simp

  have riesz_asymptotic_assembly (d : ℕ) (s a : ℝ) (hs : 0 ≤ s)
      (hsd : s < (d:ℝ)) (ha : 0 < a)
      (hscalar : ∃  b C : ℝ,0 < b  ∧ 0 ≤ C  ∧ ∀ r :ℝ,0 < r → r < 1/4 → 
        IntegrableOn (fun t :ℝ => t^(((d:ℝ)-s)/2-1)*(4*Real.pi*t)^(-(d:ℝ)/2)*
          Real.exp (-r^2/(4*t))) (Ioc 0 1) volume  ∧ 
        |(∫t in Ioc 0 1,t^(((d:ℝ)-s)/2-1)*(4*Real.pi*t)^(-(d:ℝ)/2)*
          Real.exp (-r^2/(4*t)))-(if s = 0 then b * Real.log (1/r) else b * r^(-s))| ≤ C)
      (htail : ∃ C :ℝ,0 ≤ C  ∧ ∀ y :EuclideanSpace ℝ (Fin d),
        IntegrableOn (fun t :ℝ => t^(((d:ℝ)-s)/2-1)*(HeatKernel d t (TorusLift d y)-1)) (Ioi 1) volume  ∧ 
        |∫t in Ioi 1,t^(((d:ℝ)-s)/2-1)*(HeatKernel d t (TorusLift d y)-1)| ≤ C) :
      ∃ b C :ℝ,0 < b  ∧ 0 ≤ C  ∧ ∀ y :EuclideanSpace ℝ (Fin d),0 < ‖y‖ → ‖y‖<1/4 → 
        |RieszKernel d s a 0 (TorusLift d y)-
          (if s = 0 then b * Real.log (1/‖y‖) else b * Real.rpow ‖y‖ (-s))| ≤ C := by
    let α : ℝ := ((d:ℝ)-s)/2
    let A : ℝ := a/Real.Gamma α
    have hα : 0 < α := by dsimp [α];linarith
    have hA : 0 < A := div_pos ha (Real.Gamma_pos_of_pos hα)
    obtain ⟨b,C0,hb,hC0,hscalar⟩ := hscalar
    obtain ⟨Cr,hCr,hrem⟩ := (RieszGaussianImageRemainder d).2.2 α hα
    obtain ⟨Ct,hCt,htail⟩ := htail
    refine ⟨A*b,A*(C0+Cr+Ct),mul_pos hA hb,by positivity,?_⟩
    intro y hy hsmall
    obtain ⟨hzi,hzb⟩ := hscalar ‖y‖ hy hsmall
    obtain ⟨hri,hrb⟩ := hrem y hsmall.le
    obtain ⟨hti,htb⟩ := htail y
    let f := fun t :ℝ => t^(α-1)*(HeatKernel d t (TorusLift d y)-1)
    let z := fun t :ℝ => t^(α-1)*(4*Real.pi*t)^(-(d:ℝ)/2)*Real.exp (-‖y‖^2/(4*t))
    have hsplit := (time_integral_split f z hzi hri hti).2
    have hx := lift_ne_zero_small d y hy hsmall
    have hk : RieszKernel d s a 0 (TorusLift d y)=A*(∫t in Ioi 0,f t) := by
      simp only [RieszKernel,hx,and_false,if_false,add_zero]
      rfl
    let model : ℝ := if s = 0 then b * Real.log (1/‖y‖) else b * Real.rpow ‖y‖ (-s)
    have hm : (if s = 0 then (A*b)*Real.log (1/‖y‖) else (A*b)*Real.rpow ‖y‖ (-s))=A*model := by
      dsimp [model]
      split_ifs <;>ring
    rw [hk,hsplit,hm]
    have heq : A*((∫t in Ioc 0 1,z t)+(∫t in Ioc 0 1,f t-z t)+(∫t in Ioi 1,f t))-A*model =
        A*(((∫t in Ioc 0 1,z t)-model)+(∫t in Ioc 0 1,f t-z t)+(∫t in Ioi 1,f t)) := by ring
    rw [heq,abs_mul,abs_of_pos hA]
    apply mul_le_mul_of_nonneg_left _ hA.le
    calc
      _  ≤  |(∫t in Ioc 0 1,z t)-model|+|∫t in Ioc 0 1,f t-z t|+|∫t in Ioi 1,f t| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
      _  ≤  C0+Cr+Ct := add_le_add (add_le_add hzb hrb) htb

  obtain ⟨Ct,hCt,htail⟩ := (RieszHeatTail d (((d : ℝ) - s) / 2) (by linarith)).2
  exact riesz_asymptotic_assembly d s a hs hsd ha (GaussianMellinAsymptotic d s hs)
    ⟨Ct,hCt,fun y => htail (TorusLift d y)⟩
