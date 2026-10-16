import Tablet.TorusGradient
import Tablet.TorusFourierLaplacian
import Mathlib.Topology.Constructions
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
open scoped ContDiff
-- [TABLET NODE: TorusIntegrationByParts]
theorem TorusIntegrationByParts (d : ℕ) (f h : UnitAddTorus (Fin d) → ℝ)
    (hf : TorusSmooth f) (hh : TorusSmooth h) :
    (∫ x, f x * TorusLaplacian h x ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d)))) =
      -(∫ x, ∑ j : Fin d, TorusGradient f x j * TorusGradient h x j
        ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d)))) := by
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
  exact integration_by_parts hf hh
