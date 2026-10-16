module

public import Tablet.RieszL1Foundation
public import Tablet.RieszL2Threshold
public import Tablet.TorusSobolev
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section
open MeasureTheory Set Function
open scoped ENNReal ContDiff

-- [TABLET NODE: RieszCoulombTranslatedFormBound]
theorem RieszCoulombTranslatedFormBound (d : ℕ) (hd : 2 ≤ d) (s a : ℝ)
    (hs : 0 ≤ s) (ha : 0 < a) (hC : s = (d : ℝ) - 2)
    (hL : s < (d : ℝ) / 2) :
    ((d = 2 ∧ s = 0) ∨ (d = 3 ∧ s = 1)) ∧
    ∃ A C : ℝ, 0 ≤ A ∧ 0 ≤ C ∧
      ∀ ε : ℝ, 0 ≤ ε → ∀ z : UnitAddTorus (Fin d), ∀ u : UnitAddTorus (Fin d) → ℝ, TorusSmooth u →
        (∫ x, max (RieszKernel d s a ε (x-z)) 0 * (u x)^2) ≤
          A * (∫ x, ‖TorusGradient u x‖^2) + C * (∫ x, (u x)^2) := by
-- BODY
  have smooth_continuous {d : ℕ} {f : UnitAddTorus (Fin d) → ℝ}
      (hf : TorusSmooth f) : Continuous f := by
    have hc : IsOpenQuotientMap ((↑) : ℝ → AddCircle (1 : ℝ)) :=
      QuotientAddGroup.isOpenQuotientMap_mk
    have hp : IsOpenQuotientMap
        (Pi.map (fun _ : Fin d => ((↑) : ℝ → AddCircle (1 : ℝ)))) :=
      IsOpenQuotientMap.piMap (fun _ => hc)
    have hq : IsOpenQuotientMap (TorusLift d) :=
      hp.comp (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isOpenQuotientMap
    exact hq.isQuotientMap.continuous_iff.mpr hf.continuous
  
  have continuous_memLp {d : ℕ} (f : UnitAddTorus (Fin d) → ℝ)
      (hf : Continuous f) (p : ℝ≥0∞) : MemLp f p volume := by
    rcases isCompact_univ.exists_isMaxOn Set.univ_nonempty hf.norm.continuousOn
      with ⟨x0, _, hmax⟩
    exact MemLp.of_bound hf.aestronglyMeasurable ‖f x0‖
      (Filter.Eventually.of_forall fun x => hmax (Set.mem_univ x))
  
  have fourth_le_sixth {d : ℕ} {f : UnitAddTorus (Fin d) → ℝ}
      (hf : Continuous f) :
      (∫ x, |f x| ^ (4 : ℝ)) ^ (1 / 2 : ℝ) ≤
        (∫ x, |f x| ^ (6 : ℝ)) ^ (1 / 3 : ℝ) := by
    haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
      rw [AddCircle.volume_eq_smul_haarAddCircle]; simp; infer_instance
    haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := inferInstance
    have hm := eLpNorm_le_eLpNorm_of_exponent_le (f := f) (μ := volume)
      (by norm_num : (4 : ℝ≥0∞) ≤ 6)
    have h := ENNReal.toReal_mono (continuous_memLp f hf 6).eLpNorm_ne_top hm
    rw [toReal_eLpNorm (f := f) (p := 4), toReal_eLpNorm (f := f) (p := 6),
      lpNorm_eq_integral_norm_rpow_toReal (f := f) (μ := volume)
        (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num) hf.aestronglyMeasurable,
      lpNorm_eq_integral_norm_rpow_toReal (f := f) (μ := volume)
        (by norm_num : (6 : ℝ≥0∞) ≠ 0) (by norm_num) hf.aestronglyMeasurable] at h
    simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs] at h
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg (integral_nonneg fun x =>
      Real.rpow_nonneg (abs_nonneg _) _) _) h 2
    have h4 : ((∫ x, |f x| ^ (4 : ℝ)) ^ (4 : ℝ)⁻¹)^2 =
        (∫ x, |f x| ^ (4 : ℝ)) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_two, ← Real.rpow_mul (integral_nonneg fun x =>
        Real.rpow_nonneg (abs_nonneg _) _)]; norm_num
    have h6 : ((∫ x, |f x| ^ (6 : ℝ)) ^ (6 : ℝ)⁻¹)^2 =
        (∫ x, |f x| ^ (6 : ℝ)) ^ (1 / 3 : ℝ) := by
      rw [← Real.rpow_two, ← Real.rpow_mul (integral_nonneg fun x =>
        Real.rpow_nonneg (abs_nonneg _) _)]; norm_num
    rwa [h4, h6] at hh
  
  have weighted_fourth {d : ℕ} {g f : UnitAddTorus (Fin d) → ℝ}
      (hg : MemLp g 2 volume) (hf : Continuous f) :
      ∫ x, max (g x) 0 * (f x)^2 ≤
        (∫ x, (g x)^2) ^ (1 / 2 : ℝ) * (∫ x, |f x| ^ (4 : ℝ)) ^ (1 / 2 : ℝ) := by
    have habs : MemLp (fun x => |g x|) 2 volume := by simpa [Real.norm_eq_abs] using hg.norm
    have hfsq : MemLp (fun x => (f x)^2) 2 volume := continuous_memLp _ (hf.pow 2) 2
    have hi : Integrable (fun x => |g x| * (f x)^2) volume :=
      habs.integrable_mul hfsq
    have hmaxi : Integrable (fun x => max (g x) 0 * (f x)^2) volume :=
      hi.mono' ((continuous_id.max continuous_const).comp_aestronglyMeasurable hg.aestronglyMeasurable |>.mul
        (hf.pow 2).aestronglyMeasurable) (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_max_right _ _) (sq_nonneg _))]
          exact mul_le_mul_of_nonneg_right (max_le (le_abs_self _) (abs_nonneg _)) (sq_nonneg _))
    have hh := integral_mul_le_Lp_mul_Lq_of_nonneg
      Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall fun x => abs_nonneg (g x))
      (Filter.Eventually.of_forall fun x => sq_nonneg (f x))
      (by simpa using habs) (by simpa using hfsq)
    have heq1 : (fun x => |g x| ^ (2 : ℝ)) = (fun x => (g x)^2) := by
      funext x; simp [Real.rpow_ofNat, sq_abs]
    have heq2 : (fun x => ((f x)^2) ^ (2 : ℝ)) = (fun x => |f x| ^ (4 : ℝ)) := by
      funext x; rw [Real.rpow_ofNat, Real.rpow_ofNat, ← sq_abs (f x), ← pow_mul]
    rw [heq1, heq2] at hh
    exact (integral_mono hmaxi hi (fun x =>
      mul_le_mul_of_nonneg_right (max_le (le_abs_self _) (abs_nonneg _)) (sq_nonneg _))).trans hh
  have heat_l2_contraction (d : ℕ) (t : ℝ) (ht : 0 < t)
      (f : UnitAddTorus (Fin d) → ℝ) (hm : Measurable f) (hf : MemLp f 2 volume) :
      MemLp (HeatSemigroup d t f) 2 volume ∧
        (∫ x, (HeatSemigroup d t f x)^2) ≤ ∫ x, (f x)^2 := by
    haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
      rw [AddCircle.volume_eq_smul_haarAddCircle]; simp; infer_instance
    haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := inferInstance
    let p := HeatKernel d t
    have hpc : Continuous p := (HeatKernelFacts d t ht).1
    have hpn : ∀ y, 0 ≤ p y := (HeatKernelFacts d t ht).2.1
    have hpi : Integrable p volume := hpc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hpm : (∫ y, p y) = 1 := (HeatKernelFacts d t ht).2.2.2.1
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hpc.continuousOn
    have hpb : ∀ y, ‖p y‖ ≤ C := fun y => hC y (mem_univ y)
    have hi : Integrable f volume := hf.integrable (by norm_num)
    have hisq : Integrable (fun x => (f x)^2) volume := hf.integrable_sq
    have hsmooth := HeatOperatorBounds d t ht f hm hi
    have hsq := HeatOperatorBounds d t ht (fun x => (f x)^2) (hm.pow_const _) hisq
    have hpoint : ∀ x, (HeatSemigroup d t f x)^2 ≤ HeatSemigroup d t (fun y => (f y)^2) x := by
      intro x
      let m := HeatSemigroup d t f x
      have h1 : Integrable (fun y => p y * f (x-y)) volume :=
        (hi.comp_sub_left x).bdd_mul hpc.aestronglyMeasurable (Filter.Eventually.of_forall hpb)
      have h2 : Integrable (fun y => p y * (f (x-y))^2) volume :=
        (hisq.comp_sub_left x).bdd_mul hpc.aestronglyMeasurable (Filter.Eventually.of_forall hpb)
      have heq : (fun y => p y * (f (x-y)-m)^2) =
          (fun y => p y * (f (x-y))^2 - (2*m)*(p y * f (x-y)) + m^2*p y) := by
        funext y; ring
      have hnon : 0 ≤ ∫ y, p y * (f (x-y)-m)^2 :=
        integral_nonneg fun y => mul_nonneg (hpn y) (sq_nonneg _)
      have hIE := integral_add (h2.sub (h1.const_mul (2*m))) (hpi.const_mul (m^2))
      have hIS := integral_sub h2 (h1.const_mul (2*m))
      simp only [Pi.add_apply, Pi.sub_apply] at hIE hIS
      rw [heq, hIE, hIS, integral_const_mul, integral_const_mul, hpm] at hnon
      change 0 ≤ HeatSemigroup d t (fun y => (f y)^2) x - (2*m)*m + m^2*1 at hnon
      change m^2 ≤ _
      nlinarith
    have hnon : ∀ x, 0 ≤ HeatSemigroup d t (fun y => (f y)^2) x := by
      intro x
      exact integral_nonneg fun y => mul_nonneg (hpn y) (sq_nonneg _)
    have hTi : Integrable (fun x => (HeatSemigroup d t f x)^2) volume :=
      hsq.2.1.mono' (hsmooth.1.pow_const _).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hpoint x)
    refine ⟨(memLp_two_iff_integrable_sq (hsmooth.1.aestronglyMeasurable)).mpr hTi, ?_⟩
    exact (integral_mono hTi hsq.2.1 hpoint).trans_eq hsq.2.2.1
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd4r : (d : ℝ) < 4 := by linarith
  have hd4 : d < 4 := by exact_mod_cast hd4r
  have hcases : d = 2 ∨ d = 3 := by omega
  have hclass : (d = 2 ∧ s = 0) ∨ (d = 3 ∧ s = 1) := by
    rcases hcases with h | h
    · left; refine ⟨h, ?_⟩; norm_num [h] at hC ⊢; exact hC
    · right; refine ⟨h, ?_⟩; norm_num [h] at hC ⊢; exact hC
  refine ⟨hclass, ?_⟩
  have hsd : s < (d : ℝ) := by linarith
  have hg : MemLp (RieszKernel d s a 0) 2 volume :=
    (RieszL2Threshold d hd s a hs hsd ha).mpr hL
  obtain ⟨S, hS, hSob⟩ : ∃ S : ℝ, 0 < S ∧
      ∀ u : UnitAddTorus (Fin d) → ℝ, TorusSmooth u →
        (∫ x, |u x| ^ (4 : ℝ)) ^ (1 / 2 : ℝ) ≤
          S * ((∫ x, (u x)^2) + ∫ x, ‖TorusGradient u x‖^2) := by
    rcases hcases with rfl | rfl
    · have h := (TorusSobolev 2 (by omega)).2
      norm_num at h
      simpa only [Real.rpow_ofNat] using h
    · obtain ⟨S, hS, hSob⟩ := (TorusSobolev 3 (by omega)).2
      refine ⟨S, hS, fun u hu => ?_⟩
      apply (fourth_le_sixth (smooth_continuous hu)).trans
      have h := hSob u hu
      norm_num at h
      simpa only [Real.rpow_ofNat] using h
  let G : ℝ := (∫ x, (RieszKernel d s a 0 x)^2) ^ (1 / 2 : ℝ)
  have hG : 0 ≤ G := Real.rpow_nonneg (integral_nonneg fun x => sq_nonneg _) _
  refine ⟨G*S, G*S, mul_nonneg hG hS.le, mul_nonneg hG hS.le, ?_⟩
  intro ε hε z u hu
  obtain ⟨c, hc, hFoundation⟩ := RieszL1Foundation d hd s a hs hsd ha
  have hF0 := hFoundation 0 le_rfl
  have hFε := hFoundation ε hε
  have hLpε : MemLp (RieszKernel d s a ε) 2 volume ∧
      (∫ x, (RieszKernel d s a ε x)^2) ≤ ∫ x, (RieszKernel d s a 0 x)^2 := by
    by_cases hzero : ε = 0
    · subst ε; exact ⟨hg, le_rfl⟩
    · have hpos : 0 < ε := lt_of_le_of_ne hε (Ne.symm hzero)
      have heq : RieszKernel d s a ε = HeatSemigroup d ε (RieszKernel d s a 0) :=
        funext (hFε.2.2.2.2.2.2 hpos)
      rw [heq]
      exact heat_l2_contraction d ε hpos _ hF0.1 hg
  have hGε : (∫ x, (RieszKernel d s a ε x)^2) ^ (1 / 2 : ℝ) ≤ G :=
    Real.rpow_le_rpow (integral_nonneg fun x => sq_nonneg _) hLpε.2 (by norm_num)
  have hQ : 0 ≤ (∫ x, |u x| ^ (4 : ℝ)) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _) _
  have hLpShift : MemLp (fun x => RieszKernel d s a ε (x-z)) 2 volume :=
    hLpε.1.comp_measurePreserving (measurePreserving_sub_right volume z)
  have hIntShift : (∫ x, (RieszKernel d s a ε (x-z))^2) =
      ∫ x, (RieszKernel d s a ε x)^2 := integral_sub_right_eq_self (μ := (volume : Measure (UnitAddTorus (Fin d))))
        (fun x => (RieszKernel d s a ε x)^2) z
  have hweight := weighted_fourth hLpShift (smooth_continuous hu)
  rw [hIntShift] at hweight
  have h := (hweight.trans (mul_le_mul_of_nonneg_right hGε hQ)).trans
    (mul_le_mul_of_nonneg_left (hSob u hu) hG)
  change (∫ x, max (RieszKernel d s a ε (x-z)) 0 * (u x)^2) ≤
    G * (S * ((∫ x, (u x)^2) + ∫ x, ‖TorusGradient u x‖^2)) at h
  convert h using 1 <;> ring
