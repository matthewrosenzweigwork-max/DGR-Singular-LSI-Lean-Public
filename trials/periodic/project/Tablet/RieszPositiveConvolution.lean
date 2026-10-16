import Tablet.PositiveFourierConvolution
import Tablet.RieszLocalStructure
import Tablet.RieszFourierCoefficients
open MeasureTheory UnitAddTorus
open scoped Topology

-- [TABLET NODE: RieszPositiveConvolution]
theorem RieszPositiveConvolution (d : ℕ) (hd : 2 ≤ d) (s a ε : ℝ)
    (hs : 0 ≤ s) (hsd : s < (d : ℝ)) (ha : 0 < a) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
    (∀ x, ‖RieszKernel d s a ε x‖ ≤ C) ∧
    ∃ T : Lp ℝ 2 (volume : Measure (UnitAddTorus (Fin d))) →L[ℝ]
        Lp ℝ 2 (volume : Measure (UnitAddTorus (Fin d))),
      ‖T‖ ≤ C ∧
      (∀ v w, inner ℝ v (T w) = inner ℝ (T v) w) ∧
      (∀ v, 0 ≤ inner ℝ v (T v)) ∧
      (∀ (f : UnitAddTorus (Fin d) → ℝ) (hf : MemLp f 2 volume),
        MemLp (fun x => ∫ y, RieszKernel d s a ε (x-y) * f y) 2 volume ∧
        ⇑(T (hf.toLp f)) =ᵐ[volume] fun x => ∫ y, RieszKernel d s a ε (x-y) * f y) := by
-- BODY
  classical
  have bounded_convolution (d : ℕ) (K : UnitAddTorus (Fin d) → ℝ)
    (C : ℝ) (hC : 0 < C) (hKm : Measurable K)
    (hK : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), ‖K x‖ ≤ C)
    (he : ∀ x, K (-x) = K x)
    (hF : ∀ k : Fin d → ℤ, 0 ≤ ∫ x, K x * (mFourier k x).re) :
    ∃ T : Lp ℝ 2 (volume : Measure (UnitAddTorus (Fin d))) →L[ℝ]
        Lp ℝ 2 (volume : Measure (UnitAddTorus (Fin d))),
      ‖T‖ ≤ C ∧
      (∀ v w, inner ℝ v (T w) = inner ℝ (T v) w) ∧
      (∀ v, 0 ≤ inner ℝ v (T v)) ∧
      (∀ (f : UnitAddTorus (Fin d) → ℝ) (hf : MemLp f 2 volume),
        MemLp (fun x => ∫ y, K (x-y) * f y) 2 volume ∧
        ⇑(T (hf.toLp f)) =ᵐ[volume] fun x => ∫ y, K (x-y) * f y) := by

    let L : UnitAddTorus (Fin d) → ℝ := fun x => C⁻¹ * K x
    have hLm : Measurable L := measurable_const.mul hKm
    have hL : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), ‖L x‖ ≤ 1 := by
      filter_upwards [hK] with x hx
      simpa [L, norm_mul, Real.norm_eq_abs, abs_of_pos hC, abs_of_pos (inv_pos.mpr hC), inv_mul_cancel₀ hC.ne'] using
        mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hC.le)
    have hLe : ∀ x, L (-x) = L x := fun x => by simp [L, he]
    have hLF (k : Fin d → ℤ) : 0 ≤ ∫ x, L x * (mFourier k x).re := by
      simp only [L, mul_assoc, integral_const_mul]
      exact mul_nonneg (inv_nonneg.mpr hC.le) (hF k)
    obtain ⟨S, hS, _⟩ := PositiveFourierConvolution d L hLm hL hLe hLF
    let T := C • S
    refine ⟨T, ?_, ?_, ?_, ?_⟩
    · exact (norm_smul_le C S).trans (by
        rw [Real.norm_eq_abs, abs_of_pos hC]
        simpa using mul_le_mul_of_nonneg_left hS.1 hC.le)
    · intro v w
      change inner ℝ v (C • S w) = inner ℝ (C • S v) w
      simp only [inner_smul_right, inner_smul_left, starRingEnd_apply, star_trivial]
      rw [hS.2.1 v w]
    · intro v
      change 0 ≤ inner ℝ v (C • S v)
      rw [inner_smul_right]
      exact mul_nonneg hC.le (hS.2.2.1 v)
    · intro f hf
      have heq : (fun x => ∫ y, K (x-y) * f y) =
          C • (fun x => ∫ y, L (x-y) * f y) := by
        funext x
        simp only [Pi.smul_apply, smul_eq_mul, ← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by dsimp [L]; field_simp
      have hi := (hS.2.2.2 f hf).1
      refine ⟨heq ▸ hi.const_smul C, ?_⟩
      change ⇑(C • S (hf.toLp f)) =ᵐ[volume] _
      filter_upwards [Lp.coeFn_smul C (S (hf.toLp f)), (hS.2.2.2 f hf).2] with x hx hy
      rw [congrFun heq x]
      simpa only [Pi.smul_apply, smul_eq_mul, hx, hy]
  have quotient : IsOpenQuotientMap (TorusLift d) := by
    have hc : IsOpenQuotientMap ((↑) : ℝ → AddCircle (1 : ℝ)) :=
      QuotientAddGroup.isOpenQuotientMap_mk
    have hp : IsOpenQuotientMap
        (Pi.map (fun _ : Fin d => ((↑) : ℝ → AddCircle (1 : ℝ)))) :=
      IsOpenQuotientMap.piMap (fun _ => hc)
    exact hp.comp (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isOpenQuotientMap
  have hcont : Continuous (RieszKernel d s a ε) := by
    apply quotient.continuous_comp_iff.mp
    exact ((RieszLocalStructure d hd s a hs hsd ha).2.1 ε hε).continuous
  obtain ⟨C₀, hC₀⟩ := (isCompact_univ : IsCompact (Set.univ : Set (UnitAddTorus (Fin d)))).exists_bound_of_continuousOn hcont.continuousOn
  let C := max 1 C₀
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hb : ∀ x, ‖RieszKernel d s a ε x‖ ≤ C :=
    fun x => (hC₀ x (Set.mem_univ x)).trans (le_max_right _ _)
  obtain ⟨c, _, hf⟩ := RieszL1Foundation d hd s a hs hsd ha
  have hfund := hf ε hε.le
  have hF (k : Fin d → ℤ) : 0 ≤ ∫ x, RieszKernel d s a ε x * (mFourier k x).re := by
    by_cases hk : k = 0
    · subst k
      simpa [mFourier] using hfund.2.2.1.ge
    · rw [RieszFourierCoefficients d hd s a ε hs hsd ha hε.le k hk]
      exact mul_nonneg (mul_nonneg ha.le (Real.rpow_nonneg (by positivity) _)) (Real.exp_pos _).le
  exact ⟨C, hC, hb, bounded_convolution d (RieszKernel d s a ε) C hC
    hfund.1 (Filter.Eventually.of_forall hb) hfund.2.2.2.1 hF⟩
