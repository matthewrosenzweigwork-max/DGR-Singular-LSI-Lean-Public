import Tablet.RieszWeakSource
import Tablet.RieszLocalStructure
import Tablet.HeatSourceDensity
import Tablet.HeatFourierCoefficients
import Tablet.TorusCharacterCalculus
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
open MeasureTheory
open scoped ComplexConjugate
set_option maxHeartbeats 4000000
-- [TABLET NODE: RieszHeatSource]
theorem RieszHeatSource (d : ℕ) (hd : 2 ≤ d) (s a a₂ : ℝ)
    (hs : 0 ≤ s) (hsd : s ≤ (d : ℝ) - 2) (ha : 0 < a) (ha₂ : 0 < a₂) :
    ∃ M : ℝ, 0 ≤ M ∧
      MeasureTheory.IsFiniteMeasure (RieszSourceMeasure d s a a₂ M) ∧
      (RieszSourceMeasure d s a a₂ M) Set.univ = ENNReal.ofReal M ∧
      ∀ ε : ℝ, 0 < ε →
        (∀ x, 0 ≤ HeatSourceDensity d ε (RieszSourceMeasure d s a a₂ M) x) ∧
        (∫ x, HeatSourceDensity d ε (RieszSourceMeasure d s a a₂ M) x
          ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d)))) = M ∧
        (∀ x, -TorusLaplacian (RieszKernel d s a ε) x + M =
          HeatSourceDensity d ε (RieszSourceMeasure d s a a₂ M) x) ∧
        (∀ x, TorusLaplacian (RieszKernel d s a ε) x ≤ M) := by
-- BODY
  classical
  have character_add_space (d : ℕ) (k : Fin d → ℤ) (x y : UnitAddTorus (Fin d)) :
      UnitAddTorus.mFourier k (x + y) = UnitAddTorus.mFourier k x * UnitAddTorus.mFourier k y := by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply,
      zsmul_add, AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

  have character_norm (d : ℕ) (k : Fin d → ℤ) (x : UnitAddTorus (Fin d)) :
      ‖UnitAddTorus.mFourier k x‖ = 1 := by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_apply,
      norm_prod, Circle.norm_coe, Finset.prod_const_one]

  have volume_eq_haar (d : ℕ) :
      (volume : Measure (UnitAddTorus (Fin d))) =
        Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle (T := (1 : ℝ))) := by
    change Measure.pi (fun _ : Fin d =>
      (volume : Measure (AddCircle (1 : ℝ)))) = _
    congr 1
    funext j
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp

  have continuous_fourier_unique (d : ℕ) (f : UnitAddTorus (Fin d) → ℂ)
      (hf : Continuous f)
      (hzero : ∀ k : Fin d → ℤ, (∫ x, f x * UnitAddTorus.mFourier k x) = 0) :
      ∀ x, f x = 0 := by
    let F : C(UnitAddTorus (Fin d), ℂ) := ⟨f,hf⟩
    have hc : ∀ k : Fin d → ℤ, UnitAddTorus.mFourierCoeff F k = 0 := by
      intro k
      simpa only [UnitAddTorus.mFourierCoeff, smul_eq_mul, mul_comm,
        ContinuousMap.coe_mk, F] using (by rw [volume_eq_haar] at hzero; exact hzero (-k))
    have hs : Summable (UnitAddTorus.mFourierCoeff F) := by
      simp only [funext hc]
      exact summable_zero
    intro x
    have he := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hs x
    simp only [hc, zero_smul] at he
    exact he.unique hasSum_zero

  have convolution_source_facts (d : ℕ) (p : UnitAddTorus (Fin d) → ℝ)
      (hpc : Continuous p) (hpn : ∀ x, 0 ≤ p x) (hpm : (∫ x, p x) = 1)
      (μ : Measure (UnitAddTorus (Fin d))) [IsFiniteMeasure μ] :
      Continuous (fun x => ∫ y, p (x-y) ∂μ) ∧
      (∀ x, 0 ≤ ∫ y, p (x-y) ∂μ) ∧
      Integrable (fun x => ∫ y, p (x-y) ∂μ) volume ∧
      (∫ x, (∫ y, p (x-y) ∂μ)) = μ.real Set.univ ∧
      ∀ k : Fin d → ℤ,
        (∫ x, ((∫ y, p (x-y) ∂μ : ℝ) : ℂ) * UnitAddTorus.mFourier k x) =
          (∫ x, (p x : ℂ) * UnitAddTorus.mFourier k x) *
            (∫ y, UnitAddTorus.mFourier k y ∂μ) := by
    classical
    let T := UnitAddTorus (Fin d)
    obtain ⟨C,hC⟩ := (isCompact_univ : IsCompact (Set.univ : Set T)).exists_bound_of_continuousOn hpc.continuousOn
    have hpbound : ∀ x, ‖p x‖ ≤ C := fun x => hC x (Set.mem_univ x)
    have hpjoint : Continuous (fun v : T × T => p (v.1-v.2)) :=
      hpc.comp (continuous_fst.sub continuous_snd)
    have hpi : Integrable (fun v : T × T => p (v.1-v.2)) (volume.prod μ) :=
      Integrable.of_bound hpjoint.aestronglyMeasurable C
        (Filter.Eventually.of_forall fun v => hpbound _)
    have hc : Continuous (fun x : T => ∫ y, p (x-y) ∂μ) :=
      continuous_of_dominated
        (fun x => (hpc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
        (fun x => Filter.Eventually.of_forall fun y => hpbound _)
        (integrable_const C) (Filter.Eventually.of_forall fun y =>
          hpc.comp (continuous_id.sub continuous_const))
    refine ⟨hc, fun x => integral_nonneg (fun y => hpn _), hpi.integral_prod_left, ?_, ?_⟩
    · rw [integral_integral_swap hpi]
      simp_rw [integral_sub_right_eq_self, hpm]
      simp [measureReal_def]
    · intro k
      have hHc : Continuous (fun v : T × T => (p (v.1-v.2) : ℂ) * UnitAddTorus.mFourier k v.1) :=
        (Complex.continuous_ofReal.comp hpjoint).mul ((UnitAddTorus.mFourier k).continuous.comp continuous_fst)
      have hHi : Integrable (fun v : T × T => (p (v.1-v.2) : ℂ) * UnitAddTorus.mFourier k v.1) (volume.prod μ) :=
        Integrable.of_bound hHc.aestronglyMeasurable C (Filter.Eventually.of_forall fun v => by
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, character_norm, mul_one]
          exact hpbound _)
      have hinner (x : T) :
          ((∫ y, p (x-y) ∂μ : ℝ) : ℂ) * UnitAddTorus.mFourier k x =
          ∫ y, (p (x-y) : ℂ) * UnitAddTorus.mFourier k x ∂μ := by
        rw [integral_mul_const]
        congr 1
        exact integral_complex_ofReal.symm
      simp_rw [hinner]
      rw [integral_integral_swap hHi]
      have htrans (y : T) :
          (∫ x, (p (x-y) : ℂ) * UnitAddTorus.mFourier k x) =
          (∫ x, (p x : ℂ) * UnitAddTorus.mFourier k x) * UnitAddTorus.mFourier k y := by
        calc
          _ = ∫ x, (p ((x+y)-y) : ℂ) * UnitAddTorus.mFourier k (x+y) :=
            (integral_add_right_eq_self (fun x => (p (x-y) : ℂ) * UnitAddTorus.mFourier k x) y).symm
          _ = _ := by
            calc
              _ = ∫ x, ((p x : ℂ) * UnitAddTorus.mFourier k x) * UnitAddTorus.mFourier k y := by
                apply integral_congr_ae
                exact Filter.Eventually.of_forall fun x => by
                  dsimp only
                  rw [add_sub_cancel_right, character_add_space d k x y]
                  ring
              _ = _ := integral_mul_const _ _
      simp_rw [htrans]
      rw [integral_const_mul]

  have weak_source_fourier (d : ℕ) (g : UnitAddTorus (Fin d) → ℝ) (M : ℝ)
      (μ : Measure (UnitAddTorus (Fin d))) [IsFiniteMeasure μ]
      (hgi : Integrable g volume)
      (hweak : ∀ φ : UnitAddTorus (Fin d) → ℝ, TorusSmooth φ →
        -(∫ x, g x * TorusLaplacian φ x) + M * (∫ x, φ x) = ∫ x, φ x ∂μ)
      (hchar : ∀ k : Fin d → ℤ,
        TorusSmooth (fun x => (UnitAddTorus.mFourier k x).re) ∧
        TorusSmooth (fun x => (UnitAddTorus.mFourier k x).im) ∧
        (∀ x, TorusLaplacian (fun x => (UnitAddTorus.mFourier k x).re) x =
          -(4 * Real.pi ^ 2 * ∑ j, (k j : ℝ)^2) * (UnitAddTorus.mFourier k x).re) ∧
        (∀ x, TorusLaplacian (fun x => (UnitAddTorus.mFourier k x).im) x =
          -(4 * Real.pi ^ 2 * ∑ j, (k j : ℝ)^2) * (UnitAddTorus.mFourier k x).im)) :
      ∀ k : Fin d → ℤ,
        (∫ x, UnitAddTorus.mFourier k x ∂μ) =
          ((4 * Real.pi ^ 2 * ∑ j, (k j : ℝ)^2 : ℝ) : ℂ) *
            (∫ x, (g x : ℂ) * UnitAddTorus.mFourier k x) +
          (M : ℂ) * (∫ x, UnitAddTorus.mFourier k x) := by
    intro k
    let B : ℝ := 4 * Real.pi ^ 2 * ∑ j, (k j : ℝ)^2
    let R : UnitAddTorus (Fin d) → ℝ := fun x => (UnitAddTorus.mFourier k x).re
    let S : UnitAddTorus (Fin d) → ℝ := fun x => (UnitAddTorus.mFourier k x).im
    have hiμ : Integrable (fun x => UnitAddTorus.mFourier k x) μ :=
      (UnitAddTorus.mFourier k).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hiv : Integrable (fun x => UnitAddTorus.mFourier k x) volume :=
      (UnitAddTorus.mFourier k).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hic : Integrable (fun x => (g x : ℂ) * UnitAddTorus.mFourier k x) volume :=
      (Complex.ofRealCLM.integrable_comp hgi).mul_bdd
        (UnitAddTorus.mFourier k).continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => (character_norm d k x).le)
    have hr : (∫ x, R x ∂μ) = B * (∫ x, g x * R x) + M * (∫ x, R x) := by
      have hw := hweak R (hchar k).1
      have he (x) : g x * TorusLaplacian R x = -B * (g x * R x) := by
        rw [(hchar k).2.2.1]
        dsimp [B,R]
        ring
      simp_rw [he] at hw
      rw [integral_const_mul] at hw
      linarith
    have hs : (∫ x, S x ∂μ) = B * (∫ x, g x * S x) + M * (∫ x, S x) := by
      have hw := hweak S (hchar k).2.1
      have he (x) : g x * TorusLaplacian S x = -B * (g x * S x) := by
        rw [(hchar k).2.2.2]
        dsimp [B,S]
        ring
      simp_rw [he] at hw
      rw [integral_const_mul] at hw
      linarith
    apply Complex.ext
    · have hμ := integral_re hiμ
      have hv := integral_re hiv
      have hg := integral_re hic
      simp only [RCLike.re_eq_complex_re] at hμ hv hg
      rw [← hμ]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      rw [← hg, ← hv]
      simpa only [RCLike.re_eq_complex_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero] using hr
    · have hμ := integral_im hiμ
      have hv := integral_im hiv
      have hg := integral_im hic
      simp only [RCLike.im_eq_complex_im] at hμ hv hg
      rw [← hμ]
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero]
      rw [← hg, ← hv]
      simpa only [RCLike.im_eq_complex_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero] using hs

  have character_mean (d : ℕ) (k : Fin d → ℤ) :
      (∫ x, UnitAddTorus.mFourier k x) = if k = 0 then (1 : ℂ) else 0 := by
    classical
    have h := (orthonormal_iff_ite.mp (UnitAddTorus.orthonormal_mFourier (d := Fin d))) (-k) 0
    simp only [ContinuousMap.inner_toLp, ← UnitAddTorus.mFourier_neg,
      ← UnitAddTorus.mFourier_add, neg_neg, zero_add, neg_eq_zero] at h
    rw [volume_eq_haar]
    exact h

  have spectral_source_identity (d : ℕ)
      (p f g : UnitAddTorus (Fin d) → ℝ) (M : ℝ)
      (μ : Measure (UnitAddTorus (Fin d))) [IsFiniteMeasure μ]
      (hpc : Continuous p) (hpn : ∀ x, 0 ≤ p x) (hpm : (∫ x, p x) = 1)
      (hf : TorusSmooth f)
      (hweakcoef : ∀ k : Fin d → ℤ,
        (∫ x, UnitAddTorus.mFourier k x ∂μ) =
          ((4 * Real.pi ^ 2 * ∑ j, (k j : ℝ)^2 : ℝ) : ℂ) *
            (∫ x, (g x : ℂ) * UnitAddTorus.mFourier k x) +
          (M : ℂ) * (∫ x, UnitAddTorus.mFourier k x))
      (htransfer : ∀ k : Fin d → ℤ,
        (∫ x, (f x : ℂ) * UnitAddTorus.mFourier k x) =
          (∫ x, (p x : ℂ) * UnitAddTorus.mFourier k x) *
            (∫ x, (g x : ℂ) * UnitAddTorus.mFourier k x)) :
      ∀ x, -TorusLaplacian f x + M = ∫ y, p (x-y) ∂μ := by
    classical
    let T := UnitAddTorus (Fin d)
    let C : T → ℝ := fun x => ∫ y, p (x-y) ∂μ
    have hc := convolution_source_facts d p hpc hpn hpm μ
    have hfl := TorusFourierLaplacian d f hf
    have hlc : Continuous (TorusLaplacian f) := (TorusFourierLaplacian d _ hfl.2.1).1
    have hD : Continuous (fun x : T => ((-TorusLaplacian f x + M - C x : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp ((hlc.neg.add continuous_const).sub hc.1)
    have hprodint (h : T → ℂ) (hh : Continuous h) (k : Fin d → ℤ) :
        Integrable (fun x => h x * UnitAddTorus.mFourier k x) volume :=
      (hh.mul (UnitAddTorus.mFourier k).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hcoeff (k : Fin d → ℤ) :
        (∫ x, ((-TorusLaplacian f x + M : ℝ) : ℂ) * UnitAddTorus.mFourier k x) =
          (∫ x, (C x : ℂ) * UnitAddTorus.mFourier k x) := by
      let B : ℝ := 4 * Real.pi ^ 2 * ∑ j, (k j : ℝ)^2
      have he : (∫ x, ((-TorusLaplacian f x + M : ℝ) : ℂ) * UnitAddTorus.mFourier k x) =
          (B : ℂ) * (∫ x, (f x : ℂ) * UnitAddTorus.mFourier k x) +
          (M : ℂ) * (∫ x, UnitAddTorus.mFourier k x) := by
        have halg (x : T) : ((-TorusLaplacian f x + M : ℝ) : ℂ) * UnitAddTorus.mFourier k x =
            -((TorusLaplacian f x : ℂ) * UnitAddTorus.mFourier k x) +
              (M : ℂ) * UnitAddTorus.mFourier k x := by push_cast; ring
        simp_rw [halg]
        have hadd := integral_add (hprodint _ (Complex.continuous_ofReal.comp hlc) k).neg
          (hprodint (fun _ => (M : ℂ)) continuous_const k)
        change (∫ x, -((TorusLaplacian f x : ℂ) * UnitAddTorus.mFourier k x) +
          (M : ℂ) * UnitAddTorus.mFourier k x) =
          (∫ x, -((TorusLaplacian f x : ℂ) * UnitAddTorus.mFourier k x)) +
          (∫ x, (M : ℂ) * UnitAddTorus.mFourier k x) at hadd
        rw [hadd]
        rw [integral_neg, integral_const_mul, hfl.2.2.2 k]
        dsimp [B]
        push_cast
        ring
      rw [he, hc.2.2.2.2 k, hweakcoef k, htransfer k]
      have hproj :
          (∫ x, (p x : ℂ) * UnitAddTorus.mFourier k x) *
            (∫ x, UnitAddTorus.mFourier k x) = (∫ x, UnitAddTorus.mFourier k x) := by
        rw [character_mean]
        split_ifs with hk
        · subst k
          simp only [UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, mul_one]
          rw [integral_complex_ofReal, hpm]
          norm_num
        · ring
      dsimp [B]
      linear_combination -(M : ℂ) * hproj
    have hz : ∀ k : Fin d → ℤ,
        (∫ x, ((-TorusLaplacian f x + M - C x : ℝ) : ℂ) * UnitAddTorus.mFourier k x) = 0 := by
      intro k
      have halg (x : T) : ((-TorusLaplacian f x + M - C x : ℝ) : ℂ) * UnitAddTorus.mFourier k x =
        ((-TorusLaplacian f x + M : ℝ) : ℂ) * UnitAddTorus.mFourier k x -
          (C x : ℂ) * UnitAddTorus.mFourier k x := by push_cast; ring
      simp_rw [halg]
      have hsub := integral_sub
        (hprodint (fun x => ((-TorusLaplacian f x + M : ℝ) : ℂ))
          (Complex.continuous_ofReal.comp (hlc.neg.add continuous_const)) k)
        (hprodint (fun x => (C x : ℂ)) (Complex.continuous_ofReal.comp hc.1) k)
      change (∫ x, ((-TorusLaplacian f x + M : ℝ) : ℂ) * UnitAddTorus.mFourier k x -
        (C x : ℂ) * UnitAddTorus.mFourier k x) =
        (∫ x, ((-TorusLaplacian f x + M : ℝ) : ℂ) * UnitAddTorus.mFourier k x) -
        (∫ x, (C x : ℂ) * UnitAddTorus.mFourier k x) at hsub
      rw [hsub, hcoeff, sub_self]
    have hzero := continuous_fourier_unique d _ hD hz
    intro x
    have hh := congrArg Complex.re (hzero x)
    simp only [Complex.ofReal_re, Complex.zero_re] at hh
    dsimp [C] at hh
    linarith

  have character_neg_space (d : ℕ) (k : Fin d → ℤ) (x : UnitAddTorus (Fin d)) :
      UnitAddTorus.mFourier k (-x) = conj (UnitAddTorus.mFourier k x) := by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply, fourier_apply, smul_neg,
      fourier_neg', map_prod]

  have even_fourier_coefficient (d : ℕ) (K : UnitAddTorus (Fin d) → ℝ)
      (hi : Integrable K volume) (he : ∀ x, K (-x) = K x) (k : Fin d → ℤ) :
      (∫ x, (K x : ℂ) * UnitAddTorus.mFourier k x) =
        ((∫ x, K x * (UnitAddTorus.mFourier k x).re : ℝ) : ℂ) := by
    have hic : Integrable (fun x => (K x : ℂ) * UnitAddTorus.mFourier k x) volume :=
      (Complex.ofRealCLM.integrable_comp hi).mul_bdd
        (UnitAddTorus.mFourier k).continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => (character_norm d k x).le)
    have hreal : conj (∫ x, (K x : ℂ) * UnitAddTorus.mFourier k x) =
        (∫ x, (K x : ℂ) * UnitAddTorus.mFourier k x) := by
      rw [← integral_conj]
      calc
        _ = ∫ x, (K (-x) : ℂ) * UnitAddTorus.mFourier k (-x) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by
            dsimp only
            simp only [map_mul, character_neg_space, he, Complex.conj_ofReal]
        _ = _ := integral_neg_eq_self (fun x => (K x : ℂ) * UnitAddTorus.mFourier k x) volume
    have hre : (∫ x, (K x : ℂ) * UnitAddTorus.mFourier k x).re =
        ∫ x, K x * (UnitAddTorus.mFourier k x).re := by
      have hh := integral_re hic
      simp only [RCLike.re_eq_complex_re] at hh
      rw [← hh]
      simp only [RCLike.re_eq_complex_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
    apply Complex.ext
    · simpa using hre
    · simpa using Complex.conj_eq_iff_im.mp hreal

  have riesz_heat_coefficient_transfer (d : ℕ) (hd : 2 ≤ d) (s a ε : ℝ)
      (hs : 0 ≤ s) (hsd : s < (d : ℝ)) (ha : 0 < a) (hε : 0 < ε) :
      ∀ k : Fin d → ℤ,
        (∫ x, (RieszKernel d s a ε x : ℂ) * UnitAddTorus.mFourier k x) =
          (∫ x, (HeatKernel d ε x : ℂ) * UnitAddTorus.mFourier k x) *
            (∫ x, (RieszKernel d s a 0 x : ℂ) * UnitAddTorus.mFourier k x) := by
    rcases RieszL1Foundation d hd s a hs hsd ha with ⟨c,hc,hfacts⟩
    have hg0 := hfacts 0 (le_refl _)
    have hgε := hfacts ε hε.le
    intro k
    by_cases hk : k = 0
    · subst k
      simp only [UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, mul_one,
        integral_complex_ofReal, hg0.2.2.1, hgε.2.2.1, Complex.ofReal_zero, mul_zero]
    · rw [even_fourier_coefficient d _ hgε.2.1 hgε.2.2.2.1,
        even_fourier_coefficient d _ hg0.2.1 hg0.2.2.2.1,
        (HeatFourierCoefficients d ε hε k).2]
      rw [RieszFourierCoefficients d hd s a ε hs hsd ha hε.le k hk,
        RieszFourierCoefficients d hd s a 0 hs hsd ha (le_refl _) k hk]
      simp only [mul_zero, zero_mul, neg_zero, Real.exp_zero, mul_one, Complex.ofReal_mul]
      ring

  classical
  have hslt : s < (d : ℝ) := by linarith
  rcases RieszWeakSource d hd s a a₂ hs hsd ha ha₂ with
    ⟨M,hMn,hcrit,hsub,hμ,hμmass,hweak⟩
  let μ := RieszSourceMeasure d s a a₂ M
  letI : IsFiniteMeasure μ := hμ
  rcases RieszL1Foundation d hd s a hs hslt ha with ⟨c,hc,hg⟩
  have hg0 := hg 0 (le_refl _)
  have hsourcecoef := weak_source_fourier d (RieszKernel d s a 0) M μ
    hg0.2.1 hweak (TorusCharacterCalculus d)
  refine ⟨M,hMn,hμ,hμmass,?_⟩
  intro ε hε
  have hheat := HeatKernelFacts d ε hε
  have hconv := convolution_source_facts d (HeatKernel d ε)
    hheat.1 hheat.2.1 hheat.2.2.2.1 μ
  have hid := spectral_source_identity d (HeatKernel d ε) (RieszKernel d s a ε)
    (RieszKernel d s a 0) M μ hheat.1 hheat.2.1 hheat.2.2.2.1
    ((RieszLocalStructure d hd s a hs hslt ha).2.1 ε hε)
    hsourcecoef (riesz_heat_coefficient_transfer d hd s a ε hs hslt ha hε)
  have hmassreal : μ.real Set.univ = M := by
    rw [measureReal_def, hμmass, ENNReal.toReal_ofReal hMn]
  refine ⟨hconv.2.1, ?_, hid, ?_⟩
  · change (∫ x, (∫ y, HeatKernel d ε (x-y) ∂μ)) = M
    rw [hconv.2.2.2.1, hmassreal]
  · intro x
    have hp := hconv.2.1 x
    rw [← hid x] at hp
    linarith
