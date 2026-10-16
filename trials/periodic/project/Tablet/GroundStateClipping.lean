module

public import Tablet.TorusGroundState
public import Tablet.TorusSobolev
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

@[expose] public section
open MeasureTheory
open scoped ContDiff
-- [TABLET NODE: GroundStateClipping]
theorem GroundStateClipping (d : ℕ) (hd : 0 < d) (L : ℝ) (hL : 0 ≤ L) :
    ∃ p C : ℝ, 2 < p ∧ 0 < C ∧
      ∀ (K : ℝ), 0 ≤ K →
      ∀ (V : UnitAddTorus (Fin d) → ℝ), TorusSmooth V →
      (∀ x, 0 ≤ V x) → (∫ x, V x) ≤ K →
      (∀ x, TorusLaplacian V x ≤ L) →
      let Z := ∫ x, Real.exp (-V x)
      let ν := NormalizedTilt MeasureTheory.volume (fun x => Real.exp (-V x))
      Real.exp (-K) ≤ Z ∧ Z ≤ 1 ∧
      (∀ x, Real.exp (-V x) / Z ≤ Real.exp K) ∧
      (∀ (t : ℝ) (x), V x ≤ t → Real.exp (-t) ≤ Real.exp (-V x) / Z) ∧
      ∀ f : UnitAddTorus (Fin d) → ℝ, TorusSmooth f →
      (∫ x, f x^2 ∂ν) = 1 → (∫ x, ‖TorusGradient f x‖^2 ∂ν) ≤ 1 →
      ∀ t R : ℝ, 0 < t → 0 < R →
      (∫ x in {x | R < |f x|}, f x^2 ∂ν) ≤
        C^2 * Real.rpow (K / t) (1 - 2 / p) +
        Real.rpow C p * Real.rpow R (2 - p) * Real.exp ((p - 2) * t / 2) ∧
      (∫ x, (f x - max (-R) (min (f x) R))^2 ∂ν) ≤
        C^2 * Real.rpow (K / t) (1 - 2 / p) +
        Real.rpow C p * Real.rpow R (2 - p) * Real.exp ((p - 2) * t / 2) := by
-- BODY
  classical
  have potential_normalizer (d : ℕ) (V : UnitAddTorus (Fin d) → ℝ)
      (hV : TorusSmooth V) (K : ℝ) (hpos : ∀ x, 0 ≤ V x) (hmean : (∫ x,V x) ≤ K) :
      let Z := ∫ x, Real.exp (-V x)
      Real.exp (-K) ≤ Z ∧ Z ≤ 1 ∧ 0 < Z ∧
      (∀ x, Real.exp (-V x)/Z ≤ Real.exp K) ∧
      (∀ t x, V x ≤ t → Real.exp (-t) ≤ Real.exp (-V x)/Z) := by
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
    
    haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
      rw [AddCircle.volume_eq_smul_haarAddCircle]
      simpa using (inferInstance : IsProbabilityMeasure AddCircle.haarAddCircle)
    haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) :=
      inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin d =>
        (volume : Measure (AddCircle (1 : ℝ))))))
    let Z := ∫ x, Real.exp (-V x)
    have hVi : Integrable V volume :=
      (continuous hV).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hwi : Integrable (fun x => Real.exp (-V x)) volume :=
      (Real.continuous_exp.comp (continuous hV).neg).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hj : Real.exp (-(∫ x,V x)) ≤ Z := by
      have h := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn
        isClosed_univ (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) hVi.neg hwi
      simpa only [Pi.neg_apply, integral_neg] using h
    have hzl : Real.exp (-K) ≤ Z :=
      (Real.exp_le_exp.mpr (neg_le_neg hmean)).trans hj
    have hZ : 0 < Z := (Real.exp_pos _).trans_le hzl
    have hzu : Z ≤ 1 := by
      have h := integral_mono hwi (integrable_const (1:ℝ))
        (fun x => Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hpos x)))
      simpa using h
    refine ⟨hzl,hzu,hZ,?_,?_⟩
    · intro x
      rw [div_le_iff₀ hZ]
      calc
        Real.exp (-V x) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hpos x))
        _ = Real.exp K * Real.exp (-K) := by rw [← Real.exp_add]; simp
        _ ≤ Real.exp K * Z := mul_le_mul_of_nonneg_left hzl (Real.exp_pos _).le
    · intro t x hx
      rw [le_div_iff₀ hZ]
      calc
        Real.exp (-t)*Z ≤ Real.exp (-t) := mul_le_of_le_one_right (Real.exp_pos _).le hzu
        _ ≤ Real.exp (-V x) := Real.exp_le_exp.mpr (neg_le_neg hx)

  have ground_energy (d : ℕ) (V f : UnitAddTorus (Fin d) → ℝ)
      (hV : TorusSmooth V) (hf : TorusSmooth f) (L : ℝ)
      (hlap : ∀ x, TorusLaplacian V x ≤ L)
      (hmass : (∫ x, f x^2 ∂NormalizedTilt volume (fun x => Real.exp (-V x))) = 1)
      (henergy : (∫ x, ‖TorusGradient f x‖^2 ∂NormalizedTilt volume (fun x => Real.exp (-V x))) ≤ 1) :
      let Z := ∫ x, Real.exp (-V x)
      let ψ := fun x => f x * Real.exp (-V x / 2) / Real.sqrt Z
      TorusSmooth ψ ∧ (∫ x, ψ x^2) = 1 ∧ (∫ x, ‖TorusGradient ψ x‖^2) ≤ 1+L/2 := by
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
    
    let Z := ∫ x, Real.exp (-V x)
    let ψ := fun x => f x * Real.exp (-V x/2) / Real.sqrt Z
    have hw : Continuous (fun x => Real.exp (-V x)) := Real.continuous_exp.comp (continuous hV).neg
    have ci {g : UnitAddTorus (Fin d) → ℝ} (hg : Continuous g) : Integrable g volume :=
      hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hwi := ci hw
    have hZ : 0 < Z := integral_exp_pos hwi
    have hs : (Real.sqrt Z)^2 = Z := Real.sq_sqrt hZ.le
    have hψ : TorusSmooth ψ := by
      exact (hf.mul (hV.neg.div_const 2).exp).div_const _
    have hsq (x) : ψ x^2 = f x^2 * Real.exp (-V x) / Z := by
      dsimp [ψ]
      rw [div_pow, mul_pow, ← Real.exp_nat_mul, hs]
      congr 2
      ring
    have htilt := (TiltNormalization volume _ hw.measurable
      (Filter.Eventually.of_forall (fun x => (Real.exp_pos (-V x)).le)) hwi hZ).2
        (fun x => f x^2) ((continuous hf).pow 2).measurable
        (ci (((continuous hf).pow 2).mul hw))
    have hψmass : (∫ x, ψ x^2) = 1 := by
      simp_rw [hsq]
      rw [integral_div, ← htilt.2, hmass]
    have cg {g : UnitAddTorus (Fin d) → ℝ} (hg : TorusSmooth g) : Continuous (TorusGradient g) :=
      (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).continuous_symm.comp
        (continuous_pi (fun j => continuous (gradient_smooth hg j)))
    have cl : Continuous (TorusLaplacian V) := by
      change Continuous (fun x => TorusLaplacian V x)
      simp_rw [laplacian_gradient_sum]
      exact continuous_finsetSum _ (fun j _ =>
        continuous (gradient_smooth (gradient_smooth hV j) j))
    have cψ := continuous hψ
    have hA : Integrable (fun x => ‖TorusGradient ψ x‖^2) volume := ci ((cg hψ).norm.pow 2)
    have hB : Integrable (fun x => (1/4:ℝ)*‖TorusGradient V x‖^2*ψ x^2) volume := ci ((continuous_const.mul ((cg hV).norm.pow 2)).mul (cψ.pow 2))
    have hD : Integrable (fun x => TorusLaplacian V x*ψ x^2) volume := ci (cl.mul (cψ.pow 2))
    have hBpos : 0 ≤ (∫ x, (1/4:ℝ)*‖TorusGradient V x‖^2*ψ x^2) :=
      integral_nonneg (fun x => by positivity)
    have hDle : (∫ x, TorusLaplacian V x*ψ x^2) ≤ L := by
      have hi := integral_mono hD ((ci (cψ.pow 2)).const_mul L)
        (fun x => mul_le_mul_of_nonneg_right (hlap x) (sq_nonneg _))
      simpa [integral_const_mul, hψmass] using hi
    have hid := (TorusGroundState d V f hV hf).2
    change (∫ x, ‖TorusGradient f x‖^2 ∂NormalizedTilt volume (fun x => Real.exp (-V x))) =
      ∫ x, ‖TorusGradient ψ x‖^2+(1/4:ℝ)*‖TorusGradient V x‖^2*ψ x^2-
        (1/2:ℝ)*TorusLaplacian V x*ψ x^2 at hid
    have hDh : Integrable (fun x => (1/2:ℝ)*TorusLaplacian V x*ψ x^2) volume := by
      convert hD.const_mul (1/2:ℝ) using 1 <;> ext x <;> ring
    have hAB : Integrable (fun x => ‖TorusGradient ψ x‖^2+
        (1/4:ℝ)*‖TorusGradient V x‖^2*ψ x^2) volume := hA.add hB
    rw [integral_sub hAB hDh, integral_add hA hB] at hid
    have hscale : (∫ x, (1/2:ℝ)*TorusLaplacian V x*ψ x^2) =
        (1/2:ℝ)*(∫ x, TorusLaplacian V x*ψ x^2) := by
      rw [← integral_const_mul]; congr 1; funext x; ring
    rw [hscale] at hid
    exact ⟨hψ,hψmass,by linarith⟩

  have square_rpow_abs (x p : ℝ) : (x^2)^(p/2) = |x|^p := by
    rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg x)]
    congr 1
    ring

  have set_square_holder {α : Type} [MeasurableSpace α] {μ : Measure α}
      [IsFiniteMeasure μ] (f : α → ℝ) (p : ℝ) (hp : 2 < p)
      (hf : MemLp (fun x => f x^2) (ENNReal.ofReal (p/2)) μ)
      (s : Set α) (hs : MeasurableSet s) :
      (∫ x in s, f x^2 ∂μ) ≤
        (∫ x, |f x|^p ∂μ)^(2/p) * (μ.real s)^(1-2/p) := by
    have hp0 : 0 < p := by linarith
    have hpm : 0 < p-2 := by linarith
    have hpq : (p/2).HolderConjugate (p/(p-2)) := by
      apply Real.holderConjugate_iff.mpr
      refine ⟨by linarith, ?_⟩
      field_simp
      ring
    have hg : MemLp (s.indicator (fun _ : α => (1:ℝ)))
        (ENNReal.ofReal (p/(p-2))) μ := (memLp_const (1:ℝ)).indicator hs
    have hgn : 0 ≤ᵐ[μ] s.indicator (fun _ : α => (1:ℝ)) :=
      Filter.Eventually.of_forall (fun x => by simp only [Set.indicator]; split_ifs <;> norm_num)
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
      (Filter.Eventually.of_forall (fun x => sq_nonneg (f x))) hgn hf hg
    have he : (fun x => f x^2 * s.indicator (fun _ : α => (1:ℝ)) x) =
        s.indicator (fun x => f x^2) := by
      funext x
      simp only [Set.indicator]
      split_ifs <;> simp
    have heq : 1/(p/2) = 2/p := by field_simp
    have heq' : 1/(p/(p-2)) = 1-2/p := by field_simp
    have hgpow : (fun x => (s.indicator (fun _ : α => (1:ℝ)) x)^(p/(p-2))) =
        s.indicator (fun _ : α => (1:ℝ)) := by
      funext x
      simp only [Set.indicator]
      split_ifs <;> simp [Real.zero_rpow (ne_of_gt (div_pos hp0 hpm))]
    rw [he, integral_indicator hs, hgpow, integral_indicator hs, setIntegral_const, smul_eq_mul,
      mul_one, heq, heq'] at h
    simpa only [square_rpow_abs] using h

  have potential_markov {α : Type} [MeasurableSpace α] {μ : Measure α}
      [IsFiniteMeasure μ] (V : α → ℝ) (hV : Integrable V μ)
      (hn : ∀ x, 0 ≤ V x) (t : ℝ) (ht : 0 < t)
      (hs : MeasurableSet {x | t < V x}) :
      μ.real {x | t < V x} ≤ (∫ x, V x ∂μ)/t := by
    have hi := (integrable_const (μ := μ) (1:ℝ)).indicator hs
    have h := integral_mono (hi.const_mul t) hV (fun x => by
      simp only [Set.indicator]
      split_ifs with hx
      · simpa using le_of_lt hx
      · simpa using hn x)
    rw [integral_const_mul, integral_indicator hs, setIntegral_const, smul_eq_mul, mul_one] at h
    apply (le_div_iff₀ ht).mpr
    simpa [mul_comm] using h

  have tail_pointwise (f ψ V p t R a : ℝ) (hp : 2 < p) (ha : 0 < a)
      (hgood : V ≤ t → R < |f| → a ≤ |ψ|) :
      (if R < |f| then ψ^2 else 0) ≤ (if t < V then ψ^2 else 0)+a^(2-p)*|ψ|^p := by
    have hc : 0 ≤ a^(2-p)*|ψ|^p := by positivity
    split_ifs with hf hV hV
    · linarith
    · have hψ := hgood (le_of_not_gt hV) hf
      have hψpos : 0 < |ψ| := ha.trans_le hψ
      have hpow : |ψ|^(2-p) ≤ a^(2-p) :=
        (Real.rpow_le_rpow_iff_of_neg hψpos ha (by linarith)).mpr hψ
      have hid : ψ^2 = |ψ|^p*|ψ|^(2-p) := by
        rw [← Real.rpow_add hψpos]
        simp [Real.rpow_two, sq_abs]
      rw [hid]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (abs_nonneg ψ) p)
    · positivity
    · simpa using hc

  have clipping_pointwise (x R : ℝ) (hR : 0 < R) :
      (x-max (-R) (min x R))^2 ≤ (if R < |x| then x^2 else 0) := by
    by_cases hlo : x < -R
    · rw [min_eq_left (by linarith),max_eq_left hlo.le,if_pos]
      · nlinarith
      · rw [abs_of_neg (by linarith)]; linarith
    · by_cases hhi : R < x
      · rw [min_eq_right hhi.le,max_eq_right (by linarith),if_pos]
        · nlinarith
        · exact hhi.trans_le (le_abs_self x)
      · rw [min_eq_left (le_of_not_gt hhi),max_eq_right (le_of_not_gt hlo)]
        simp only [sub_self, zero_pow (by decide : 2 ≠ 0)]
        split_ifs <;> positivity

  have tail_integral {α : Type} [TopologicalSpace α] [CompactSpace α]
      [MeasurableSpace α] [BorelSpace α] {μ : Measure α} [IsFiniteMeasure μ]
      (f ψ V : α → ℝ) (hf : Continuous f) (hψ : Continuous ψ) (hV : Continuous V)
      (p t R a : ℝ) (hp : 2 < p) (ha : 0 < a)
      (hgood : ∀ x, V x ≤ t → R < |f x| → a ≤ |ψ x|) :
      (∫ x in {x | R < |f x|}, ψ x^2 ∂μ) ≤
        (∫ x in {x | t < V x}, ψ x^2 ∂μ)+a^(2-p)*(∫ x, |ψ x|^p ∂μ) := by
    have ci {g : α → ℝ} (hg : Continuous g) : Integrable g μ :=
      hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have htail : MeasurableSet {x | R < |f x|} := measurableSet_lt measurable_const hf.abs.measurable
    have hbad : MeasurableSet {x | t < V x} := measurableSet_lt measurable_const hV.measurable
    have hpower : Continuous (fun x => |ψ x|^p) :=
      (hψ.abs.rpow_const (by intro x; right; linarith))
    have hiSq : Integrable (fun x => ψ x^2) μ := ci (hψ.pow 2)
    have hiBad := hiSq.indicator hbad
    have hiTail := hiSq.indicator htail
    have hi : Integrable (fun x =>
        {x | t < V x}.indicator (fun x => ψ x^2) x+a^(2-p)*|ψ x|^p) μ :=
      hiBad.add ((ci hpower).const_mul _)
    have h := integral_mono hiTail hi (fun x => by
      simpa only [Set.indicator, Set.mem_setOf_eq] using tail_pointwise
        (f x) (ψ x) (V x) p t R a hp ha (hgood x))
    rw [integral_add hiBad ((ci hpower).const_mul _),
      integral_const_mul, integral_indicator htail, integral_indicator hbad] at h
    exact h

  have torus_smooth_cont {d : ℕ} {f : UnitAddTorus (Fin d) → ℝ}
      (hf : TorusSmooth f) : Continuous f := by
    have hc : IsOpenQuotientMap ((↑) : ℝ → AddCircle (1 : ℝ)) :=
      QuotientAddGroup.isOpenQuotientMap_mk
    have hp : IsOpenQuotientMap
        (Pi.map (fun _ : Fin d => ((↑) : ℝ → AddCircle (1 : ℝ)))) :=
      IsOpenQuotientMap.piMap (fun _ => hc)
    have hq : IsOpenQuotientMap (TorusLift d) :=
      hp.comp (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isOpenQuotientMap
    exact hq.continuous_comp_iff.mp hf.continuous

  have ground_mass_set (d : ℕ) (V f : UnitAddTorus (Fin d) → ℝ)
      (hV : TorusSmooth V) (hf : TorusSmooth f)
      (s : Set (UnitAddTorus (Fin d))) (hs : MeasurableSet s) :
      (∫ x in s, f x^2 ∂NormalizedTilt volume (fun x => Real.exp (-V x))) =
      ∫ x in s, (f x*Real.exp (-V x/2)/Real.sqrt (∫ x, Real.exp (-V x)))^2 := by
    classical
    let Z := ∫ x, Real.exp (-V x)
    have cf := torus_smooth_cont hf
    have hw : Continuous (fun x => Real.exp (-V x)) :=
      Real.continuous_exp.comp (torus_smooth_cont hV).neg
    have ci {g : UnitAddTorus (Fin d) → ℝ} (hg : Continuous g) : Integrable g volume :=
      hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hwi := ci hw
    have hZ : 0 < Z := integral_exp_pos hwi
    have hc : (Real.sqrt Z)^2 = Z := Real.sq_sqrt hZ.le
    have hp (x) : (f x*Real.exp (-V x/2)/Real.sqrt Z)^2 =
        f x^2*Real.exp (-V x)/Z := by
      rw [div_pow,mul_pow,← Real.exp_nat_mul,hc]
      congr 2
      ring
    have hi : Integrable (fun x => s.indicator (fun x => f x^2) x*Real.exp (-V x)) volume := by
      have he : (fun x => s.indicator (fun x => f x^2) x*Real.exp (-V x)) =
          s.indicator (fun x => f x^2*Real.exp (-V x)) := by
        funext x
        simp only [Set.indicator]
        split_ifs <;> simp
      rw [he]
      exact (ci ((cf.pow 2).mul hw)).indicator hs
    have h := (TiltNormalization volume _ hw.measurable
      (Filter.Eventually.of_forall (fun x => (Real.exp_pos (-V x)).le)) hwi hZ).2
        (s.indicator (fun x => f x^2)) ((cf.pow 2).measurable.indicator hs) hi
    rw [integral_indicator hs] at h
    rw [h.2]
    change (∫ x, s.indicator (fun x => f x^2) x*Real.exp (-V x))/Z =
      ∫ x in s, (f x*Real.exp (-V x/2)/Real.sqrt Z)^2
    simp_rw [hp]
    rw [integral_div]
    congr 1
    rw [← integral_indicator hs]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      simp only [Set.indicator]; split_ifs <;> simp)

  have psi_good_bound (f V Z t R : ℝ) (hZ : 0 < Z) (hZu : Z ≤ 1)
      (hR : 0 < R) (hV : V ≤ t) (hf : R < |f|) :
      R*Real.exp (-t/2) ≤ |f*Real.exp (-V/2)/Real.sqrt Z| := by
    rw [abs_div, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.sqrt_pos.mpr hZ)]
    apply (le_div_iff₀ (Real.sqrt_pos.mpr hZ)).mpr
    have hs : Real.sqrt Z ≤ 1 := by
      have := Real.sqrt_le_sqrt hZu
      simpa using this
    calc
      (R*Real.exp (-t/2))*Real.sqrt Z ≤ R*Real.exp (-t/2) :=
        mul_le_of_le_one_right (by positivity) hs
      _ ≤ |f| *Real.exp (-V/2) := mul_le_mul hf.le
        (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le (abs_nonneg _)

  have threshold_power (R t p : ℝ) (hR : 0 < R) :
      (R*Real.exp (-t/2))^(2-p) = R^(2-p)*Real.exp ((p-2)*t/2) := by
    rw [Real.mul_rpow hR.le (Real.exp_pos _).le, ← Real.exp_mul]
    congr 2
    ring

  have moment_from_sobolev (m p A : ℝ) (hm : 0 ≤ m) (hp : 2 < p)
      (hA : 0 ≤ A) (h : m^(2/p) ≤ A) :
      m^(2/p) ≤ (A+1)^2 ∧ m ≤ (A+1)^p := by
    have hp0 : 0 < p := by linarith
    have hAc : A ≤ (A+1)^2 := by nlinarith [sq_nonneg A]
    have hC : 0 < A+1 := by linarith
    refine ⟨h.trans hAc, ?_⟩
    have hr := Real.rpow_le_rpow (Real.rpow_nonneg hm _) (h.trans hAc) (by positivity : 0 ≤ p/2)
    rw [← Real.rpow_mul hm] at hr
    have hexp : (2/p)*(p/2) = 1 := by field_simp
    rw [hexp, Real.rpow_one] at hr
    have hright : ((A+1)^2)^(p/2) = (A+1)^p := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hC.le]
      congr 1
      ring
    rwa [hright] at hr

  classical
  haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1:ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simpa using (inferInstance : IsProbabilityMeasure AddCircle.haarAddCircle)
  haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin d =>
      (volume : Measure (AddCircle (1:ℝ))))))
  obtain ⟨hp,Cs,hCs,hSob⟩ := TorusSobolev d hd
  let p : ℝ := if d ≤ 2 then 4 else 2*(d:ℝ)/((d:ℝ)-2)
  change 2 < p at hp
  let A := Cs*(2+L/2)
  let C := A+1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨p,C,hp,hC,?_⟩
  intro K hK V hV hVp hmean hlap
  dsimp only
  obtain ⟨hzl,hzu,hZ,hdens,hsub⟩ := potential_normalizer d V hV K hVp hmean
  refine ⟨hzl,hzu,hdens,hsub,?_⟩
  intro f hf hmass henergy t R ht hR
  let Z := ∫ x, Real.exp (-V x)
  let ν := NormalizedTilt volume (fun x => Real.exp (-V x))
  let ψ := fun x => f x*Real.exp (-V x/2)/Real.sqrt Z
  obtain ⟨hψ,hψm,hψe⟩ := ground_energy d V f hV hf L hlap hmass henergy
  change TorusSmooth ψ at hψ
  change (∫ x, ψ x^2)=1 at hψm
  change (∫ x, ‖TorusGradient ψ x‖^2)≤1+L/2 at hψe
  have cf := torus_smooth_cont hf
  have cψ := torus_smooth_cont hψ
  have cV := torus_smooth_cont hV
  have ci {g : UnitAddTorus (Fin d) → ℝ} (hg : Continuous g) : Integrable g volume :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let m := ∫ x, |ψ x|^p
  have hm : 0 ≤ m := integral_nonneg (fun x => Real.rpow_nonneg (abs_nonneg _) _)
  have hmA : m^(2/p) ≤ A := by
    have h := hSob ψ hψ
    change m^(2/p) ≤ Cs*((∫ x, ψ x^2)+∫ x, ‖TorusGradient ψ x‖^2) at h
    rw [hψm] at h
    exact h.trans (by dsimp [A]; nlinarith)
  obtain ⟨hmC2,hmCp⟩ := moment_from_sobolev m p A hm hp hA hmA
  change m^(2/p)≤C^2 at hmC2
  change m≤C^p at hmCp
  have hb : MeasurableSet {x | t < V x} := measurableSet_lt measurable_const cV.measurable
  have hα : 0 ≤ 1-2/p := by
    have hp0 : 0 < p := by linarith
    have : 2/p < 1 := (div_lt_one hp0).mpr hp
    linarith
  have hmark : volume.real {x | t < V x} ≤ K/t :=
    (potential_markov V (ci cV) hVp t ht hb).trans (div_le_div_of_nonneg_right hmean ht.le)
  have hmem : MemLp (fun x => ψ x^2) (ENNReal.ofReal (p/2)) volume :=
    (cψ.pow 2).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hset := set_square_holder ψ p hp hmem {x | t < V x} hb
  change (∫ x in {x | t < V x}, ψ x^2)≤m^(2/p)*volume.real {x | t < V x}^(1-2/p) at hset
  have hfirst : (∫ x in {x | t < V x}, ψ x^2) ≤ C^2*(K/t)^(1-2/p) := by
    apply hset.trans
    exact mul_le_mul hmC2 (Real.rpow_le_rpow (by positivity) hmark hα)
      (by positivity) (sq_nonneg C)
  let a := R*Real.exp (-t/2)
  have ha : 0 < a := by dsimp [a]; positivity
  have htail := tail_integral (μ := volume) f ψ V cf cψ cV p t R a hp ha
    (fun x hx hfx => psi_good_bound (f x) (V x) Z t R hZ hzu hR hx hfx)
  have htailν : (∫ x in {x | R < |f x|}, f x^2 ∂ν) ≤
      C^2*(K/t)^(1-2/p)+C^p*R^(2-p)*Real.exp ((p-2)*t/2) := by
    rw [ground_mass_set d V f hV hf _ (measurableSet_lt measurable_const cf.abs.measurable)]
    change (∫ x in {x | R < |f x|}, ψ x^2) ≤ _
    apply htail.trans
    have hsecond : a^(2-p)*m ≤ C^p*R^(2-p)*Real.exp ((p-2)*t/2) := by
      calc
        a^(2-p)*m ≤ a^(2-p)*C^p := mul_le_mul_of_nonneg_left hmCp (by positivity)
        _ = _ := by rw [threshold_power R t p hR]; ring
    exact add_le_add hfirst hsecond
  refine ⟨htailν,?_⟩
  have hw : Continuous (fun x => Real.exp (-V x)) := Real.continuous_exp.comp cV.neg
  have hnu := (TiltNormalization volume _ hw.measurable
    (Filter.Eventually.of_forall (fun x => (Real.exp_pos (-V x)).le)) (ci hw) hZ).1
  letI : IsProbabilityMeasure ν := hnu
  have htmeas : MeasurableSet {x | R < |f x|} := measurableSet_lt measurable_const cf.abs.measurable
  have hfsq : Integrable (fun x => f x^2) ν :=
    (cf.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hclip : Continuous (fun x => (f x-max (-R) (min (f x) R))^2) :=
    (cf.sub (continuous_const.max (cf.min continuous_const))).pow 2
  have hci : Integrable (fun x => (f x-max (-R) (min (f x) R))^2) ν :=
    hclip.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hle := integral_mono hci (hfsq.indicator htmeas) (fun x => by
    simpa only [Set.indicator,Set.mem_setOf_eq] using clipping_pointwise (f x) R hR)
  rw [integral_indicator htmeas] at hle
  exact hle.trans htailν
