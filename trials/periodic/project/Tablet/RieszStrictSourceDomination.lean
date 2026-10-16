import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Tablet.RieszWeakSource
import Tablet.RieszLocalStructure
import Tablet.HeatSourceDensity
import Tablet.HeatOperatorBounds
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Group.Integral
open MeasureTheory Set Metric
open scoped ContDiff
open MeasureTheory Set
open scoped ENNReal
-- [TABLET NODE: RieszStrictSourceDomination]
theorem RieszStrictSourceDomination (d : ℕ) (hd : 2 ≤ d) (s a a₂ : ℝ)
    (hs : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (ha : 0 < a) (ha₂ : 0 < a₂) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ x, 0 ≤ (a/a₂)*RieszKernel d (s+2) a₂ 0 x+M) ∧ IsFiniteMeasure (RieszSourceMeasure d s a a₂ M) ∧
      (RieszSourceMeasure d s a a₂ M) Set.univ = ENNReal.ofReal M ∧
      (∀ φ : UnitAddTorus (Fin d) → ℝ, TorusSmooth φ →
        -(∫ x, RieszKernel d s a 0 x * TorusLaplacian φ x) + M*(∫ x, φ x) =
          ∫ x, φ x ∂RieszSourceMeasure d s a a₂ M) ∧
      ∀ θ : ℝ, 0 < θ → ∃ C : ℝ, 0 ≤ C ∧
        (∀ x, max (RieszKernel d s a 0 x) 0 ≤
          θ*((a/a₂)*RieszKernel d (s+2) a₂ 0 x+M)+C) ∧
        ∀ ε : ℝ, 0 < ε → ∀ x, max (RieszKernel d s a ε x) 0 ≤
          θ*HeatSourceDensity d ε (RieszSourceMeasure d s a a₂ M) x+C := by
-- BODY
  have power_domination (s b k θ : ℝ) (hb : 0 < b) (hk : 0 < k) (hθ : 0 < θ) :
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧ ∀ r : ℝ, 0 < r → r < δ →
        b * r ^ (-s) ≤ θ * k * r ^ (-(s+2)) := by
    let δ := min (1/4 : ℝ) (Real.sqrt (θ*k/b))
    have hq : 0 < θ*k/b := div_pos (mul_pos hθ hk) hb
    have hδ : 0 < δ := lt_min (by norm_num) (Real.sqrt_pos.mpr hq)
    refine ⟨δ, hδ, min_le_left _ _, ?_⟩
    intro r hr hrd
    have hrroot : r ≤ Real.sqrt (θ*k/b) := hrd.le.trans (min_le_right _ _)
    have hrsq : r^2 ≤ θ*k/b := by
      have h := pow_le_pow_left₀ hr.le hrroot 2
      simpa only [Real.sq_sqrt hq.le] using h
    have hbnd : b*r^2 ≤ θ*k := by
      have h := (le_div_iff₀ hb).mp hrsq
      nlinarith
    have heq : r^(-s) = r^2*r^(-(s+2)) := by
      rw [show -s = 2 + (-(s+2)) by ring, Real.rpow_add hr, Real.rpow_two]
    rw [heq, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hbnd (Real.rpow_nonneg hr.le _)
  
  have logarithmic_domination (b k θ : ℝ) (hb : 0 < b) (hk : 0 < k) (hθ : 0 < θ) :
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧ ∀ r : ℝ, 0 < r → r < δ →
        b * Real.log (1/r) ≤ θ*k*r^(-2 : ℝ) := by
    let δ := min (1/4 : ℝ) (θ*k/b)
    have hq : 0 < θ*k/b := div_pos (mul_pos hθ hk) hb
    refine ⟨δ, lt_min (by norm_num) hq, min_le_left _ _, ?_⟩
    intro r hr hrd
    have hbr : b*r ≤ θ*k := by
      have h := (le_div_iff₀ hb).mp (hrd.le.trans (min_le_right _ _))
      nlinarith
    have hlog : Real.log (1/r) ≤ 1/r := by
      have h := Real.log_le_sub_one_of_pos (one_div_pos.mpr hr)
      linarith
    have heq : (1/r) = r * r^(-2 : ℝ) := by
      rw [Real.rpow_neg hr.le, Real.rpow_two]
      field_simp
    apply (mul_le_mul_of_nonneg_left hlog hb.le).trans
    rw [heq, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hbr (Real.rpow_nonneg hr.le _)
  
  let closedCube (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
    {y | ∀ j, y j ∈ Icc (-(1:ℝ)/2) (1/2)}
  have lift_zero_closedCube (d:ℕ) (y:EuclideanSpace ℝ (Fin d)) (hy:y∈closedCube d) :
        TorusLift d y=0 ↔ y=0 := by
      constructor
      · intro h
        apply PiLp.ext
        intro j
        have hj : (y j:AddCircle (1:ℝ))=0 := congrFun h j
        obtain ⟨n,hn⟩ := (AddCircle.coe_eq_zero_iff (p:=(1:ℝ))).mp hj
        simp only [zsmul_eq_mul,mul_one] at hn
        have hlo := (hy j).1
        have hhi := (hy j).2
        have hnzero : n=0 := by
          by_contra hn0
          have hh : (1:ℤ)≤n ∨ n≤-1 := by omega
          rcases hh with hh | hh
          · have : (1:ℝ)≤(n:ℝ) := by exact_mod_cast hh
            linarith
          · have : (n:ℝ)≤-1 := by exact_mod_cast hh
            linarith
        change y j = 0
        simpa only [hnzero,Int.cast_zero] using hn.symm
      · rintro rfl
        rfl
  
  have compact_closedCube (d:ℕ) : IsCompact (closedCube d) := by
      have hc := isCompact_univ_pi (fun _:Fin d=>isCompact_Icc (a:=-(1:ℝ)/2) (b:=1/2))
      have hp := (PiLp.homeomorph 2 (fun _:Fin d=>ℝ)).isCompact_preimage.mpr hc
      convert hp using 1
      ext y
      simp only [closedCube,Set.mem_preimage,Set.mem_setOf_eq,
        Set.mem_pi,Set.mem_univ,true_implies]
      rfl
  
  
  have strict_domination (d : ℕ) (hd : 2 ≤ d) (s a a₂ : ℝ)
      (hs : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (ha : 0 < a) (ha₂ : 0 < a₂)
      (M : ℝ) (hM : 0 ≤ M)
      (hk : ∀ x, 0 ≤ (a/a₂)*RieszKernel d (s+2) a₂ 0 x + M)
      (θ : ℝ) (hθ : 0 < θ) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x, max (RieszKernel d s a 0 x) 0 ≤
        θ*((a/a₂)*RieszKernel d (s+2) a₂ 0 x+M)+C := by
    classical
    have hsd0 : s < (d : ℝ) := by linarith
    have hs2 : 0 ≤ s+2 := by linarith
    have hsd2 : s+2 < (d : ℝ) := by linarith
    obtain ⟨b, C, hb, hC, hlocal⟩ := (RieszLocalStructure d hd s a hs hsd0 ha).2.2
    obtain ⟨b₂, C₂, hb₂, hC₂, hlocal₂⟩ := (RieszLocalStructure d hd (s+2) a₂ hs2 hsd2 ha₂).2.2
    have hq : 0 < a/a₂ := div_pos ha ha₂
    have hbq : 0 < (a/a₂)*b₂ := mul_pos hq hb₂
    obtain ⟨δ, hδ, hδ4, hdom⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/4 ∧
        ∀ r : ℝ, 0 < r → r < δ →
        (if s=0 then b*Real.log (1/r) else b*r^(-s)) ≤
          θ*((a/a₂)*b₂)*r^(-(s+2)) := by
      by_cases hs0 : s=0
      · subst s
        obtain ⟨δ, hd, hd4, hh⟩ := logarithmic_domination b ((a/a₂)*b₂) θ hb hbq hθ
        refine ⟨δ, hd, hd4, ?_⟩
        intro r hr hrδ
        simpa using hh r hr hrδ
      · obtain ⟨δ, hd, hd4, hh⟩ := power_domination s b ((a/a₂)*b₂) θ hb hbq hθ
        exact ⟨δ, hd, hd4, fun r hr hrδ => by simpa [hs0] using hh r hr hrδ⟩
    let Cnear : ℝ := C + θ*(a/a₂)*C₂
    have hCnear : 0 ≤ Cnear := add_nonneg hC (mul_nonneg (mul_nonneg hθ.le hq.le) hC₂)
    have hnear : ∀ y : EuclideanSpace ℝ (Fin d), 0 < ‖y‖ → ‖y‖ < δ →
        max (RieszKernel d s a 0 (TorusLift d y)) 0 ≤
        θ*((a/a₂)*RieszKernel d (s+2) a₂ 0 (TorusLift d y)+M)+Cnear := by
      intro y hy hyδ
      have hy4 : ‖y‖ < 1/4 := hyδ.trans_le hδ4
      have hu := (abs_le.mp (hlocal y hy hy4)).2
      have hl := (abs_le.mp (hlocal₂ y hy hy4)).1
      have h2ne : s+2 ≠ 0 := by linarith
      simp only [if_neg h2ne] at hl
      have hh := hdom ‖y‖ hy hyδ
      have hlmul := mul_le_mul_of_nonneg_left hl (mul_nonneg hθ.le hq.le)
      have hthM := mul_nonneg hθ.le hM
      apply max_le
      · dsimp [Cnear]
        simp only [Real.rpow_eq_pow] at hu hlmul
        by_cases hs0 : s=0 <;> simp only [hs0, if_true, if_false] at hu hh hlmul ⊢ <;> nlinarith
      · exact add_nonneg (mul_nonneg hθ.le (hk _)) hCnear
    let F : EuclideanSpace ℝ (Fin d) → ℝ := fun y =>
      max (RieszKernel d s a 0 (TorusLift d y)) 0 -
        θ*((a/a₂)*RieszKernel d (s+2) a₂ 0 (TorusLift d y)+M)
    have hc : ContinuousOn F {y | TorusLift d y ≠ 0} := by
      exact ((RieszLocalStructure d hd s a hs hsd0 ha).1.continuousOn.sup continuousOn_const).sub
        (continuousOn_const.mul ((continuousOn_const.mul
          (RieszLocalStructure d hd (s+2) a₂ hs2 hsd2 ha₂).1.continuousOn).add continuousOn_const))
    let K := closedCube d ∩ (ball (0 : EuclideanSpace ℝ (Fin d)) δ)ᶜ
    have hK : IsCompact K := (compact_closedCube d).inter_right isOpen_ball.isClosed_compl
    have hKU : K ⊆ {y | TorusLift d y ≠ 0} := by
      intro y hy hzero
      have hy0 := (lift_zero_closedCube d y hy.1).mp hzero
      subst y
      exact hy.2 (by simpa using hδ)
    obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn (hc.mono hKU)
    refine ⟨max Cnear D, le_trans hCnear (le_max_left _ _), ?_⟩
    intro x
    let y : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2
      (fun j => (AddCircle.equivIco (1 : ℝ) (-(1:ℝ)/2) (x j) : ℝ))
    have hylift : TorusLift d y = x := by
      ext j; simp [TorusLift, y]
    have hycube : y ∈ closedCube d := by
      intro j
      exact ⟨(AddCircle.equivIco (1:ℝ) (-(1:ℝ)/2) (x j)).property.1,
        by have h := (AddCircle.equivIco (1:ℝ) (-(1:ℝ)/2) (x j)).property.2; dsimp [y]; linarith⟩
    rw [← hylift]
    by_cases hyzero : y = 0
    · have hlift0 : TorusLift d y = 0 := by rw [hyzero]; rfl
      simp only [hlift0, RieszKernel, and_self, if_true, mul_zero, zero_add, max_self]
      exact add_nonneg (mul_nonneg hθ.le hM) (le_trans hCnear (le_max_left _ _))
    · by_cases hynear : ‖y‖ < δ
      · exact (hnear y (norm_pos_iff.mpr hyzero) hynear).trans
          (add_le_add_right (le_max_left Cnear D) _)
      · have hyK : y ∈ K := ⟨hycube, by change ¬ dist y 0 < δ; simpa only [dist_zero_right] using hynear⟩
        have hbound := le_trans (le_abs_self (F y)) (by simpa only [Real.norm_eq_abs] using hD y hyK)
        have hDD := le_max_right Cnear D
        dsimp [F] at hbound
        linarith
  have heat_density_eq (d : ℕ) (t : ℝ) (k : UnitAddTorus (Fin d) → ℝ)
      (hm : Measurable k) (hk : ∀ y, 0 ≤ k y) (x : UnitAddTorus (Fin d)) :
      HeatSourceDensity d t (volume.withDensity (fun y => ENNReal.ofReal (k y))) x =
        HeatSemigroup d t k x := by
    unfold HeatSourceDensity
    rw [integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hk _), smul_eq_mul]
    have h := integral_sub_left_eq_self (fun y => k y * HeatKernel d t (x-y)) volume x
    simp only [sub_sub_cancel] at h
    simpa only [HeatSemigroup, mul_comm] using h.symm
  
  have heat_domination (d : ℕ) (t : ℝ) (ht : 0 < t)
      (g k : UnitAddTorus (Fin d) → ℝ) (hg : Integrable g volume)
      (hk : Integrable k volume) (hkm : Measurable k) (hkn : ∀ x, 0 ≤ k x)
      (θ C : ℝ) (hθ : 0 ≤ θ) (hC : 0 ≤ C)
      (hbound : ∀ x, max (g x) 0 ≤ θ*k x+C) :
      ∀ x, max (HeatSemigroup d t g x) 0 ≤
        θ*HeatSourceDensity d t (volume.withDensity (fun y => ENNReal.ofReal (k y))) x+C := by
    let p := HeatKernel d t
    have hpc : Continuous p := (HeatKernelFacts d t ht).1
    have hpn : ∀ y, 0 ≤ p y := (HeatKernelFacts d t ht).2.1
    have hpi : Integrable p volume := hpc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hpm : (∫ y, p y) = 1 := (HeatKernelFacts d t ht).2.2.2.1
    obtain ⟨D, hD⟩ := isCompact_univ.exists_bound_of_continuousOn hpc.continuousOn
    have hpb : ∀ y, ‖p y‖ ≤ D := fun y => hD y (mem_univ y)
    intro x
    rw [heat_density_eq d t k hkm hkn x]
    have h1 : Integrable (fun y => p y*g (x-y)) volume :=
      (hg.comp_sub_left x).bdd_mul hpc.aestronglyMeasurable (Filter.Eventually.of_forall hpb)
    have h2 : Integrable (fun y => p y*k (x-y)) volume :=
      (hk.comp_sub_left x).bdd_mul hpc.aestronglyMeasurable (Filter.Eventually.of_forall hpb)
    have hbd : ∀ y, p y*g (x-y) ≤ θ*(p y*k (x-y))+C*p y := by
      intro y
      have h := mul_le_mul_of_nonneg_left ((le_max_left _ _).trans (hbound (x-y))) (hpn y)
      nlinarith
    have h2c := integral_add (h2.const_mul θ) (hpi.const_mul C)
    have hmono := integral_mono h1 ((h2.const_mul θ).add (hpi.const_mul C)) hbd
    change (∫ y, p y * g (x-y)) ≤ ∫ y, θ*(p y * k (x-y))+C*p y at hmono
    rw [h2c, integral_const_mul, integral_const_mul, hpm, mul_one] at hmono
    have hPkn : 0 ≤ HeatSemigroup d t k x :=
      integral_nonneg fun y => mul_nonneg (hpn y) (hkn (x-y))
    exact max_le hmono (add_nonneg (mul_nonneg hθ hPkn) hC)
  obtain ⟨M, hM, hEnd, hPos, hFin, hMass, hWeak⟩ :=
    RieszWeakSource d hd s a a₂ hs hsd.le ha ha₂
  refine ⟨M, hM, hPos hsd, hFin, hMass, hWeak, ?_⟩
  intro θ hθ
  obtain ⟨C, hC, hbound⟩ := strict_domination d hd s a a₂ hs hsd ha ha₂ M hM (hPos hsd) θ hθ
  refine ⟨C, hC, hbound, ?_⟩
  intro ε hε x
  obtain ⟨c, hc, hF⟩ := RieszL1Foundation d hd s a hs (by linarith) ha
  obtain ⟨c₂, hc₂, hF₂⟩ := RieszL1Foundation d hd (s+2) a₂ (by linarith) (by linarith) ha₂
  have h0 := hF 0 le_rfl
  have hεF := hF ε hε.le
  have h₂ := hF₂ 0 le_rfl
  let k : UnitAddTorus (Fin d) → ℝ := fun y => (a/a₂)*RieszKernel d (s+2) a₂ 0 y+M
  have hkm : Measurable k := (h₂.1.const_mul (a/a₂)).add_const M
  have hki : Integrable k volume := (h₂.2.1.const_mul (a/a₂)).add (integrable_const M)
  have hk : ∀ y, 0 ≤ k y := hPos hsd
  have hsource : RieszSourceMeasure d s a a₂ M = volume.withDensity (fun y => ENNReal.ofReal (k y)) := by
    unfold RieszSourceMeasure; rw [if_pos hsd]
  rw [hεF.2.2.2.2.2.2 hε x, hsource]
  exact heat_domination d ε hε _ k h0.2.1 hki hkm hk θ C hθ.le hC hbound x
