import Tablet.TorusSmooth
import Tablet.TorusLaplacian
import Tablet.Preamble
import Tablet.TorusGradient
import Mathlib.Topology.Constructions
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
open scoped ContDiff
-- [TABLET NODE: TorusFourierLaplacian]
theorem TorusFourierLaplacian (d : ℕ) (f : UnitAddTorus (Fin d) → ℝ)
    (hf : TorusSmooth f) :
    Continuous f ∧ TorusSmooth (TorusLaplacian f) ∧
    (∫ x, TorusLaplacian f x ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d)))) = 0 ∧
    ∀ k : Fin d → ℤ,
      (∫ x, (TorusLaplacian f x : ℂ) * UnitAddTorus.mFourier k x ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d)))) =
        ((-(4 * Real.pi ^ 2 * ∑ j, (k j : ℝ) ^ 2) : ℝ) : ℂ) *
          (∫ x, (f x : ℂ) * UnitAddTorus.mFourier k x ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d)))) := by
-- BODY
  classical
  
  have quotient (d : ℕ) : IsOpenQuotientMap (TorusLift d) := by
    have hc : IsOpenQuotientMap ((↑) : ℝ → AddCircle (1 : ℝ)) :=
      QuotientAddGroup.isOpenQuotientMap_mk
    have hp : IsOpenQuotientMap
        (Pi.map (fun _ : Fin d => ((↑) : ℝ → AddCircle (1 : ℝ)))) :=
      IsOpenQuotientMap.piMap (fun _ => hc)
    exact hp.comp (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isOpenQuotientMap
  
  have continuous {d : ℕ} {f : UnitAddTorus (Fin d) → ℝ}
      (hf : TorusSmooth f) : Continuous f := by
    apply (quotient d).continuous_comp_iff.mp
    exact hf.continuous
  
  have lift_translation_eq {d : ℕ} (y z : EuclideanSpace ℝ (Fin d))
      (h : TorusLift d y = TorusLift d z) (x : EuclideanSpace ℝ (Fin d)) :
      TorusLift d (x + (z-y)) = TorusLift d x := by
    funext j
    have hj := congrFun h j
    change (y j : AddCircle (1 : ℝ)) = (z j : AddCircle (1 : ℝ)) at hj
    simp only [TorusLift, PiLp.add_apply, PiLp.sub_apply]
    rw [AddCircle.coe_add, AddCircle.coe_sub, ← hj, sub_self, add_zero]
  
  have lift_fderiv_eq {d : ℕ} (f : UnitAddTorus (Fin d) → ℝ)
      (y z : EuclideanSpace ℝ (Fin d)) (h : TorusLift d y = TorusLift d z) :
      fderiv ℝ (fun x => f (TorusLift d x)) y =
        fderiv ℝ (fun x => f (TorusLift d x)) z := by
    let q := fun x => f (TorusLift d x)
    have hfun : (fun x => q (x+(z-y))) = q := by
      funext x
      exact congrArg f (lift_translation_eq y z h x)
    have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := q) (x := y) (z-y)
    rw [hfun] at hd
    simpa using hd
  
  have gradient_on_lift {d : ℕ} (f : UnitAddTorus (Fin d) → ℝ)
      (y : EuclideanSpace ℝ (Fin d)) (j : Fin d) :
      TorusGradient f (TorusLift d y) j =
        fderiv ℝ (fun x => f (TorusLift d x)) y (EuclideanSpace.single j 1) := by
    let z : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2
      (fun j => (AddCircle.equivIco (1 : ℝ) 0 (TorusLift d y j) : ℝ))
    have hz : TorusLift d z = TorusLift d y := by
      funext j
      simp [TorusLift, z]
    change fderiv ℝ (fun x => f (TorusLift d x)) z (EuclideanSpace.single j 1) = _
    rw [lift_fderiv_eq f z y hz]
  
  have gradient_smooth {d : ℕ} {f : UnitAddTorus (Fin d) → ℝ}
      (hf : TorusSmooth f) (j : Fin d) : TorusSmooth (fun x => TorusGradient f x j) := by
    change ContDiff ℝ ∞ (fun y => TorusGradient f (TorusLift d y) j)
    simp_rw [gradient_on_lift]
    exact (hf.fderiv_right (by simp)).clm_apply contDiff_const
  
  have lift_add {d : ℕ} (y z : EuclideanSpace ℝ (Fin d)) :
      TorusLift d (y + z) = TorusLift d y + TorusLift d z := by
    ext j
    simp [TorusLift]
  
  have lift_single {d : ℕ} (j : Fin d) :
      TorusLift d (EuclideanSpace.single j 1) = 0 := by
    ext k
    by_cases h : j = k
    · subst k
      simp [TorusLift]
    · simp [TorusLift, h]
  
  have slice_hasDeriv {d : ℕ} {f : UnitAddTorus (Fin d) → ℝ}
      (hf : TorusSmooth f) (y : EuclideanSpace ℝ (Fin d)) (j : Fin d) (t : ℝ) :
      HasDerivAt (fun t => f (TorusLift d (y + t • EuclideanSpace.single j 1)))
        (TorusGradient f (TorusLift d (y + t • EuclideanSpace.single j 1)) j) t := by
    rw [gradient_on_lift]
    have hs : HasDerivAt (fun t : ℝ => y + t • EuclideanSpace.single j 1)
        (EuclideanSpace.single j 1) t := by
      convert! (show HasDerivAt _ _ t from
        (hasDerivAt_const t y).add ((hasDerivAt_id t).smul_const
        (EuclideanSpace.single j (1 : ℝ)))) using 1 <;> simp
    exact (hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t hs
  
  have integral_gradient_zero {d : ℕ} {f : UnitAddTorus (Fin d) → ℝ}
      (hf : TorusSmooth f) (j : Fin d) :
      (∫ x, TorusGradient f x j ∂(MeasureTheory.volume :
        MeasureTheory.Measure (UnitAddTorus (Fin d)))) = 0 := by
    let D : UnitAddTorus (Fin d) → ℝ := fun x => TorusGradient f x j
    have hD : Continuous D := continuous (gradient_smooth hf j)
    have hs : ∀ x : UnitAddTorus (Fin d),
        (∫ t in (0 : ℝ)..1, D (x + TorusLift d (t • EuclideanSpace.single j 1))) = 0 := by
      intro x
      obtain ⟨y, rfl⟩ := (quotient d).surjective x
      have hc : Continuous (fun t : ℝ =>
          D (TorusLift d y + TorusLift d (t • EuclideanSpace.single j 1))) :=
        hD.comp (continuous_const.add ((quotient d).continuous.comp
          (continuous_id.smul continuous_const)))
      have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := (0 : ℝ)) (b := 1) (fun t _ => slice_hasDeriv hf y j t)
        (by simpa only [lift_add] using hc.intervalIntegrable 0 1)
      simp only [one_smul, zero_smul, add_zero, lift_add, lift_single,
        sub_self] at hFTC
      simpa only [D, lift_add] using hFTC
    have hb : ∃ C : ℝ, ∀ x, ‖D x‖ ≤ C := by
      rcases isCompact_univ.exists_isMaxOn Set.univ_nonempty hD.norm.continuousOn
        with ⟨x0, _, hmax⟩
      exact ⟨‖D x0‖, fun x => hmax (Set.mem_univ x)⟩
    obtain ⟨C, hC⟩ := hb
    have : MeasureTheory.IsFiniteMeasure
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
      simp only [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      infer_instance
    have hcont : Continuous (fun p : ℝ × UnitAddTorus (Fin d) =>
        D (p.2 + TorusLift d (p.1 • EuclideanSpace.single j 1))) :=
      hD.comp (continuous_snd.add ((quotient d).continuous.comp
        (continuous_fst.smul continuous_const)))
    have hi : MeasureTheory.Integrable
        (fun p : ℝ × UnitAddTorus (Fin d) =>
          D (p.2 + TorusLift d (p.1 • EuclideanSpace.single j 1)))
        ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)).prod MeasureTheory.volume) :=
      (MeasureTheory.integrable_const C).mono' hcont.aestronglyMeasurable
        (Filter.Eventually.of_forall fun p => hC _)
    have hswap := MeasureTheory.intervalIntegral_integral_swap
      (f := fun t x => D (x + TorusLift d (t • EuclideanSpace.single j 1)))
      (a := (0 : ℝ)) (b := 1) hi
    simp only [MeasureTheory.integral_add_right_eq_self, hs,
      MeasureTheory.integral_zero, intervalIntegral.integral_const, sub_zero, one_smul] at hswap
    exact hswap
  
  have laplacian_gradient_sum {d : ℕ} (f : UnitAddTorus (Fin d) → ℝ)
      (x : UnitAddTorus (Fin d)) :
      TorusLaplacian f x = ∑ j, TorusGradient (fun x => TorusGradient f x j) x j := by
    let y : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2
      (fun j => (AddCircle.equivIco (1 : ℝ) 0 (x j) : ℝ))
    have hy : TorusLift d y = x := by
      ext j
      simp [TorusLift, y]
    calc
      TorusLaplacian f x = ∑ j, fderiv ℝ
          (fun z => fderiv ℝ (fun w => f (TorusLift d w)) z
            (EuclideanSpace.single j 1)) y (EuclideanSpace.single j 1) := rfl
      _ = ∑ j, TorusGradient (fun x => TorusGradient f x j) (TorusLift d y) j := by
        simp_rw [gradient_on_lift]
      _ = _ := by rw [hy]
  
  have gradient_mul {d : ℕ} {f h : UnitAddTorus (Fin d) → ℝ}
      (hf : TorusSmooth f) (hh : TorusSmooth h) (x : UnitAddTorus (Fin d))
      (j : Fin d) : TorusGradient (fun x => f x * h x) x j =
        TorusGradient f x j * h x + f x * TorusGradient h x j := by
    obtain ⟨y, rfl⟩ := (quotient d).surjective x
    simp_rw [gradient_on_lift]
    have hd := (hf.differentiable (by simp) y).hasFDerivAt.mul
      (hh.differentiable (by simp) y).hasFDerivAt
    change HasFDerivAt (fun x => f (TorusLift d x) * h (TorusLift d x)) _ y at hd
    rw [hd.fderiv]
    simp
    ring
  
  have integration_by_parts {d : ℕ} {f h : UnitAddTorus (Fin d) → ℝ}
      (hf : TorusSmooth f) (hh : TorusSmooth h) :
      (∫ x, f x * TorusLaplacian h x ∂(MeasureTheory.volume :
        MeasureTheory.Measure (UnitAddTorus (Fin d)))) =
        -(∫ x, ∑ j, TorusGradient f x j * TorusGradient h x j
          ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d)))) := by
    have hi (j : Fin d) : (∫ x, f x * TorusGradient (fun x => TorusGradient h x j) x j) =
        -(∫ x, TorusGradient f x j * TorusGradient h x j) := by
      have hg : TorusSmooth (fun x => TorusGradient h x j) := gradient_smooth hh j
      have hp : TorusSmooth (fun x => f x * TorusGradient h x j) := hf.mul hg
      have hz := integral_gradient_zero hp j
      simp_rw [gradient_mul hf hg] at hz
      have hi1 : MeasureTheory.Integrable
          (fun x => TorusGradient f x j * TorusGradient h x j) MeasureTheory.volume :=
        ((continuous (gradient_smooth hf j)).mul (continuous hg)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      have hi2 : MeasureTheory.Integrable
          (fun x => f x * TorusGradient (fun x => TorusGradient h x j) x j)
          MeasureTheory.volume :=
        ((continuous hf).mul (continuous (gradient_smooth hg j))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      rw [MeasureTheory.integral_add hi1 hi2] at hz
      linarith
    simp_rw [laplacian_gradient_sum, Finset.mul_sum]
    rw [MeasureTheory.integral_finsetSum, MeasureTheory.integral_finsetSum]
    · simp_rw [hi]
      simp
    · intro j _
      exact ((continuous (gradient_smooth hf j)).mul
        (continuous (gradient_smooth hh j))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    · intro j _
      exact ((continuous hf).mul
        (continuous (gradient_smooth (gradient_smooth hh j) j))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  
  let phase {d : ℕ} (k : Fin d → ℤ) : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
    ∑ j, (2 * Real.pi * (k j : ℝ)) • EuclideanSpace.proj j
  
  have phase_apply {d : ℕ} (k : Fin d → ℤ) (y : EuclideanSpace ℝ (Fin d)) :
      phase k y = ∑ j, 2 * Real.pi * (k j : ℝ) * y j := by
    simp [phase]
  
  have phase_single {d : ℕ} (k : Fin d → ℤ) (j : Fin d) :
      phase k (EuclideanSpace.single j 1) = 2 * Real.pi * (k j : ℝ) := by
    simp [phase, EuclideanSpace.proj]
  
  have character_exp {d : ℕ} (k : Fin d → ℤ) (y : EuclideanSpace ℝ (Fin d)) :
      UnitAddTorus.mFourier k (TorusLift d y) = Complex.exp ((phase k y : ℂ) * Complex.I) := by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, TorusLift, fourier_coe_apply,
      div_one, phase_apply, Complex.ofReal_sum]
    rw [← Complex.exp_sum]
    congr 1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  
  have character_re {d : ℕ} (k : Fin d → ℤ) (y : EuclideanSpace ℝ (Fin d)) :
      (UnitAddTorus.mFourier k (TorusLift d y)).re = Real.cos (phase k y) := by
    rw [character_exp, Complex.exp_re]
    simp
  
  have character_im {d : ℕ} (k : Fin d → ℤ) (y : EuclideanSpace ℝ (Fin d)) :
      (UnitAddTorus.mFourier k (TorusLift d y)).im = Real.sin (phase k y) := by
    rw [character_exp, Complex.exp_im]
    simp
  
  have cos_fderiv {d : ℕ} (L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
      (y : EuclideanSpace ℝ (Fin d)) :
      fderiv ℝ (fun y => Real.cos (L y)) y = (-Real.sin (L y)) • L := by
    have hd := (Real.hasDerivAt_cos (L y)).hasFDerivAt.comp y L.hasFDerivAt
    change HasFDerivAt (fun y => Real.cos (L y)) _ y at hd
    rw [hd.fderiv]
    ext v
    simp [mul_comm]
  
  have sin_fderiv {d : ℕ} (L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
      (y : EuclideanSpace ℝ (Fin d)) :
      fderiv ℝ (fun y => Real.sin (L y)) y = Real.cos (L y) • L := by
    have hd := (Real.hasDerivAt_sin (L y)).hasFDerivAt.comp y L.hasFDerivAt
    change HasFDerivAt (fun y => Real.sin (L y)) _ y at hd
    rw [hd.fderiv]
    ext v
    simp [mul_comm]
  
  have lap_cos {d : ℕ} (f : UnitAddTorus (Fin d) → ℝ)
      (L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
      (hf : ∀ y, f (TorusLift d y) = Real.cos (L y)) (x : UnitAddTorus (Fin d)) :
      TorusLaplacian f x = -(∑ j, (L (EuclideanSpace.single j 1)) ^ 2) * f x := by
    let y : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2
      (fun j => (AddCircle.equivIco (1 : ℝ) 0 (x j) : ℝ))
    have hy : TorusLift d y = x := by ext j; simp [TorusLift, y]
    change (∑ j, fderiv ℝ (fun z =>
      fderiv ℝ (fun w => f (TorusLift d w)) z (EuclideanSpace.single j 1)) y
        (EuclideanSpace.single j 1)) = _
    simp_rw [hf, cos_fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hd (j : Fin d) := ((Real.hasDerivAt_sin (L y)).hasFDerivAt.comp y
      L.hasFDerivAt).neg.mul_const (L (EuclideanSpace.single j 1))
    have he (j : Fin d) : fderiv ℝ (fun z => -Real.sin (L z) *
        L (EuclideanSpace.single j 1)) y (EuclideanSpace.single j 1) =
          -Real.cos (L y) * (L (EuclideanSpace.single j 1)) ^ 2 := by
      have hdj := hd j
      change HasFDerivAt (fun z => -Real.sin (L z) * L (EuclideanSpace.single j 1)) _ y at hdj
      rw [hdj.fderiv]
      simp
      ring
    simp_rw [he]
    rw [← Finset.mul_sum]
    have hxy : f x = Real.cos (L y) := by rw [← hy]; exact hf y
    rw [hxy]
    ring
  
  have lap_sin {d : ℕ} (f : UnitAddTorus (Fin d) → ℝ)
      (L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
      (hf : ∀ y, f (TorusLift d y) = Real.sin (L y)) (x : UnitAddTorus (Fin d)) :
      TorusLaplacian f x = -(∑ j, (L (EuclideanSpace.single j 1)) ^ 2) * f x := by
    let y : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2
      (fun j => (AddCircle.equivIco (1 : ℝ) 0 (x j) : ℝ))
    have hy : TorusLift d y = x := by ext j; simp [TorusLift, y]
    change (∑ j, fderiv ℝ (fun z =>
      fderiv ℝ (fun w => f (TorusLift d w)) z (EuclideanSpace.single j 1)) y
        (EuclideanSpace.single j 1)) = _
    simp_rw [hf, sin_fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hd (j : Fin d) := ((Real.hasDerivAt_cos (L y)).hasFDerivAt.comp y
      L.hasFDerivAt).mul_const (L (EuclideanSpace.single j 1))
    have he (j : Fin d) : fderiv ℝ (fun z => Real.cos (L z) *
        L (EuclideanSpace.single j 1)) y (EuclideanSpace.single j 1) =
          -Real.sin (L y) * (L (EuclideanSpace.single j 1)) ^ 2 := by
      have hdj := hd j
      change HasFDerivAt (fun z => Real.cos (L z) * L (EuclideanSpace.single j 1)) _ y at hdj
      rw [hdj.fderiv]
      simp
      ring
    simp_rw [he]
    rw [← Finset.mul_sum]
    have hxy : f x = Real.sin (L y) := by rw [← hy]; exact hf y
    rw [hxy]
    ring
  
  have fourier_laplacian (d : ℕ) (f : UnitAddTorus (Fin d) → ℝ)
      (hf : TorusSmooth f) :
      Continuous f ∧ TorusSmooth (TorusLaplacian f) ∧
      (∫ x, TorusLaplacian f x ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d)))) = 0 ∧
      ∀ k : Fin d → ℤ,
        (∫ x, (TorusLaplacian f x : ℂ) * UnitAddTorus.mFourier k x ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d)))) =
          ((-(4 * Real.pi ^ 2 * ∑ j, (k j : ℝ) ^ 2) : ℝ) : ℂ) *
            (∫ x, (f x : ℂ) * UnitAddTorus.mFourier k x ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d)))) := by
    have hlf : TorusSmooth (TorusLaplacian f) := by
      change ContDiff ℝ ∞ (fun y => TorusLaplacian f (TorusLift d y))
      simp_rw [laplacian_gradient_sum]
      apply ContDiff.sum
      intro j _
      exact gradient_smooth (gradient_smooth hf j) j
    refine ⟨continuous hf, hlf, ?_, ?_⟩
    · simp_rw [laplacian_gradient_sum]
      rw [MeasureTheory.integral_finsetSum]
      · simp_rw [integral_gradient_zero (gradient_smooth hf _)]
        simp
      · intro j _
        exact (continuous
          (gradient_smooth (gradient_smooth hf j) j)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
    · intro k
      let A : ℝ := 4 * Real.pi ^ 2 * ∑ j, (k j : ℝ) ^ 2
      let R : UnitAddTorus (Fin d) → ℝ := fun x => (UnitAddTorus.mFourier k x).re
      let S : UnitAddTorus (Fin d) → ℝ := fun x => (UnitAddTorus.mFourier k x).im
      have hR : TorusSmooth R := by
        change ContDiff ℝ ∞ (fun y => (UnitAddTorus.mFourier k (TorusLift d y)).re)
        simp_rw [character_re]
        exact Real.contDiff_cos.comp (phase k).contDiff
      have hS : TorusSmooth S := by
        change ContDiff ℝ ∞ (fun y => (UnitAddTorus.mFourier k (TorusLift d y)).im)
        simp_rw [character_im]
        exact Real.contDiff_sin.comp (phase k).contDiff
      have hA : (∑ j, (phase k (EuclideanSpace.single j 1)) ^ 2) = A := by
        simp_rw [phase_single]
        unfold A
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      have hLR (x) : TorusLaplacian R x = -A * R x := by
        simpa only [hA] using lap_cos R (phase k) (character_re k) x
      have hLS (x) : TorusLaplacian S x = -A * S x := by
        simpa only [hA] using lap_sin S (phase k) (character_im k) x
      have hsym (h : UnitAddTorus (Fin d) → ℝ) (hh : TorusSmooth h) :
          (∫ x, TorusLaplacian f x * h x) = (∫ x, f x * TorusLaplacian h x) := by
        calc
          (∫ x, TorusLaplacian f x * h x) = (∫ x, h x * TorusLaplacian f x) := by
            congr 1
            funext x
            ring
          _ = -(∫ x, ∑ j, TorusGradient h x j * TorusGradient f x j) :=
            integration_by_parts hh hf
          _ = -(∫ x, ∑ j, TorusGradient f x j * TorusGradient h x j) := by
            simp_rw [mul_comm]
          _ = (∫ x, f x * TorusLaplacian h x) := (integration_by_parts hf hh).symm
      have hreal : (∫ x, TorusLaplacian f x * R x) = -A * (∫ x, f x * R x) := by
        rw [hsym R hR]
        simp_rw [hLR, ← mul_assoc, mul_comm (f _) (-A), mul_assoc]
        rw [MeasureTheory.integral_const_mul]
      have himag : (∫ x, TorusLaplacian f x * S x) = -A * (∫ x, f x * S x) := by
        rw [hsym S hS]
        simp_rw [hLS, ← mul_assoc, mul_comm (f _) (-A), mul_assoc]
        rw [MeasureTheory.integral_const_mul]
      have hci : MeasureTheory.Integrable
          (fun x => (f x : ℂ) * UnitAddTorus.mFourier k x) MeasureTheory.volume :=
        ((Complex.continuous_ofReal.comp (continuous hf)).mul
          (UnitAddTorus.mFourier k).continuous).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      have hcli : MeasureTheory.Integrable
          (fun x => (TorusLaplacian f x : ℂ) * UnitAddTorus.mFourier k x) MeasureTheory.volume :=
        ((Complex.continuous_ofReal.comp (continuous hlf)).mul
          (UnitAddTorus.mFourier k).continuous).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      apply Complex.ext
      · have hReL := integral_re hcli
        have hReB := integral_re hci
        simp only [RCLike.re_eq_complex_re] at hReL hReB
        rw [← hReL]
        simp only [RCLike.re_eq_complex_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero]
        rw [← hReB]
        simpa only [RCLike.re_eq_complex_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero] using hreal
      · have hImL := integral_im hcli
        have hImB := integral_im hci
        simp only [RCLike.im_eq_complex_im] at hImL hImB
        rw [← hImL]
        simp only [RCLike.im_eq_complex_im, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, add_zero]
        rw [← hImB]
        simpa only [RCLike.im_eq_complex_im, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, add_zero] using himag
  exact fourier_laplacian d f hf
