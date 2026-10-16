module

public import Tablet.AtomicPotential
public import Tablet.CompactWeightedPoincare
public import Tablet.RieszHeatSource
public import Tablet.BoundedDensityComparison
public import Tablet.RieszL1Foundation
public import Tablet.RieszLocalStructure
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Constructions
public import Mathlib.MeasureTheory.Group.Integral

@[expose] public section
open MeasureTheory
open scoped ContDiff
-- [TABLET NODE: HolesPoincare]
theorem HolesPoincare (d : ℕ) (hd : 2 ≤ d) (s a B : ℝ)
    (hs : 0 ≤ s) (hsd : s ≤ (d : ℝ) - 2) (ha : 0 < a) (hB : 0 ≤ B) :
    ∃ rate : ℝ, 0 < rate ∧
      ∀ (n : ℕ) (w : Fin n → ℝ) (y : Fin n → UnitAddTorus (Fin d)),
      (∀ j, 0 ≤ w j) → (∑ j, w j) ≤ B →
      ∀ ε : ℝ, 0 < ε →
      let U := AtomicPotential (RieszKernel d s a ε) w y
      let ν := NormalizedTilt MeasureTheory.volume (fun x => Real.exp (-U x))
      (∀ f : UnitAddTorus (Fin d) → ℝ, TorusSmooth f →
        ProbabilityTheory.variance f ν ≤ rate⁻¹ * (∫ x, ‖TorusGradient f x‖^2 ∂ν)) ∧
      (∀ (b : UnitAddTorus (Fin d) → ℝ) (l u : ℝ),
        Measurable b → 0 < l →
        (∀ᵐ x, l ≤ b x ∧ b x ≤ u) →
        ∀ f : UnitAddTorus (Fin d) → ℝ, TorusSmooth f →
        ProbabilityTheory.variance f
          (NormalizedTilt MeasureTheory.volume (fun x => b x * Real.exp (-U x))) ≤
        (u / l) * rate⁻¹ *
          (∫ x, ‖TorusGradient f x‖^2
            ∂NormalizedTilt MeasureTheory.volume (fun x => b x * Real.exp (-U x)))) := by
-- BODY
  classical
  let second {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
      (H : A → ℝ) (z v : A) : ℝ := fderiv ℝ (fun y => fderiv ℝ H y v) z v
  have second_const_mul {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
      (H : A → ℝ) (hH : ContDiff ℝ ∞ H) (b : ℝ) (z v : A) :
      second (fun y => b*H y) z v = b * second H z v := by
    have hd := hH.differentiable (by simp)
    have hc := (((contDiff_infty_iff_fderiv.mp hH).2).clm_apply
      (contDiff_const : ContDiff ℝ ∞ (fun _ : A => v))).differentiable (by simp)
    have he : (fun y => fderiv ℝ (fun x => b*H x) y v) =
        (fun y => b * fderiv ℝ H y v) := by
      funext y
      rw [fderiv_const_mul hd.differentiableAt]
      rfl
    unfold second
    rw [he, fderiv_const_mul hc.differentiableAt]
    rfl

  have second_sum {A ι : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
      [Fintype ι] (H : ι → A → ℝ) (hH : ∀ k, ContDiff ℝ ∞ (H k)) (z v : A) :
      second (fun y => ∑ k, H k y) z v = ∑ k, second (H k) z v := by
    have he : (fun y => fderiv ℝ (fun x => ∑ k, H k x) y v) =
        fun y => ∑ k, fderiv ℝ (H k) y v := by
      funext y
      have hf : (fun x => ∑ k, H k x) = ∑ k, H k := by ext x; simp
      rw [hf, fderiv_sum (fun k _ => ((hH k).differentiable (by simp)).differentiableAt)]
      simp
    unfold second
    rw [he]
    have hf : (fun y => ∑ k, fderiv ℝ (H k) y v) = ∑ k, (fun y => fderiv ℝ (H k) y v) := by ext y; simp
    rw [hf, fderiv_sum (fun k _ =>
      ((((contDiff_infty_iff_fderiv.mp (hH k)).2).clm_apply contDiff_const).differentiable
        (by simp)).differentiableAt)]
    simp

  have torus_translation_eq {d : ℕ} (y z : EuclideanSpace ℝ (Fin d))
      (h : TorusLift d y = TorusLift d z) (x : EuclideanSpace ℝ (Fin d)) :
      TorusLift d (x+(z-y)) = TorusLift d x := by
    funext k
    have hk := congrFun h k
    change (y k : AddCircle (1 : ℝ)) = (z k : AddCircle (1 : ℝ)) at hk
    simp only [TorusLift, PiLp.add_apply, PiLp.sub_apply]
    rw [AddCircle.coe_add, AddCircle.coe_sub, ← hk, sub_self, add_zero]

  have torus_fderiv_eq {d : ℕ} (G : UnitAddTorus (Fin d) → ℝ)
      (y z : EuclideanSpace ℝ (Fin d)) (h : TorusLift d y = TorusLift d z) :
      fderiv ℝ (fun x => G (TorusLift d x)) y =
        fderiv ℝ (fun x => G (TorusLift d x)) z := by
    let H := fun x => G (TorusLift d x)
    have hfun : (fun x => H (x+(z-y))) = H := by
      funext x
      exact congrArg G (torus_translation_eq y z h x)
    have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := H) (x := y) (z-y)
    rw [hfun] at hd
    simpa using hd

  have torus_second_eq {d : ℕ} (G : UnitAddTorus (Fin d) → ℝ)
      (y z v : EuclideanSpace ℝ (Fin d)) (h : TorusLift d y = TorusLift d z) :
      fderiv ℝ (fun x => fderiv ℝ (fun w => G (TorusLift d w)) x v) y v =
        fderiv ℝ (fun x => fderiv ℝ (fun w => G (TorusLift d w)) x v) z v := by
    let F := fun x => fderiv ℝ (fun w => G (TorusLift d w)) x v
    have hfun : (fun x => F (x+(z-y))) = F := by
      funext x
      exact congrArg (fun L => L v)
        (torus_fderiv_eq G (x+(z-y)) x (torus_translation_eq y z h x))
    have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := F) (x := y) (z-y)
    rw [hfun] at hd
    have he := congrArg (fun L => L v) hd
    simpa [F] using he

  let rep {d : ℕ} (x : UnitAddTorus (Fin d)) : EuclideanSpace ℝ (Fin d) :=
    WithLp.toLp 2 (fun j => (AddCircle.equivIco (1 : ℝ) 0 (x j) : ℝ))

  have lift_rep {d : ℕ} (x : UnitAddTorus (Fin d)) : TorusLift d (rep x) = x := by
    funext j
    simp [TorusLift, rep]

  have lift_sub {d : ℕ} (y z : EuclideanSpace ℝ (Fin d)) :
      TorusLift d (y-z) = TorusLift d y - TorusLift d z := by
    funext j
    simp [TorusLift, AddCircle.coe_sub]

  have smooth_translate {d : ℕ} (G : UnitAddTorus (Fin d) → ℝ)
      (hG : TorusSmooth G) (z : UnitAddTorus (Fin d)) :
      TorusSmooth (fun x => G (x-z)) := by
    have h := hG.comp (contDiff_id.sub (contDiff_const :
      ContDiff ℝ ∞ (fun _ : EuclideanSpace ℝ (Fin d) => rep z)))
    simpa only [TorusSmooth, Function.comp_def, id_eq, lift_sub, lift_rep] using h

  have lap_translate {d : ℕ} (G : UnitAddTorus (Fin d) → ℝ)
      (z x : UnitAddTorus (Fin d)) :
      TorusLaplacian (fun x => G (x-z)) x = TorusLaplacian G (x-z) := by
    have he : (fun y => G (TorusLift d y-z)) =
        fun y => G (TorusLift d (y-rep z)) := by
      funext y
      rw [lift_sub, lift_rep]
    change (∑ j : Fin d, second (fun y => G (TorusLift d y-z))
      (rep x) (EuclideanSpace.single j 1)) =
      ∑ j : Fin d, second (fun y => G (TorusLift d y)) (rep (x-z)) (EuclideanSpace.single j 1)
    rw [he]
    apply Finset.sum_congr rfl
    intro j _
    unfold second
    have hfirst : (fun y => fderiv ℝ (fun w => G (TorusLift d (w-rep z))) y
        (EuclideanSpace.single j 1)) =
        fun y => fderiv ℝ (fun w => G (TorusLift d w)) (y-rep z) (EuclideanSpace.single j 1) := by
      funext y
      exact congrArg (fun L => L (EuclideanSpace.single j 1))
        (fderiv_comp_sub (𝕜 := ℝ) (f := fun w => G (TorusLift d w)) (x := y) (rep z))
    rw [hfirst, fderiv_comp_sub (𝕜 := ℝ)
      (f := fun y => fderiv ℝ (fun w => G (TorusLift d w)) y (EuclideanSpace.single j 1))]
    exact torus_second_eq G _ _ _ (by rw [lift_sub, lift_rep, lift_rep, lift_rep])

  have lap_add_const {d : ℕ} (G : UnitAddTorus (Fin d) → ℝ) (c : ℝ) (x) :
      TorusLaplacian (fun x => G x+c) x = TorusLaplacian G x := by
    unfold TorusLaplacian
    simp_rw [fderiv_add_const]

  have lap_mul {d : ℕ} (G : UnitAddTorus (Fin d) → ℝ)
      (hG : TorusSmooth G) (b : ℝ) (x) :
      TorusLaplacian (fun x => b*G x) x = b * TorusLaplacian G x := by
    change (∑ j : Fin d, second (fun y => b*G (TorusLift d y))
      (rep x) (EuclideanSpace.single j 1)) =
      b * ∑ j : Fin d, second (fun y => G (TorusLift d y)) (rep x) (EuclideanSpace.single j 1)
    simp_rw [second_const_mul _ hG]
    exact (Finset.mul_sum _ _ _).symm

  have lap_sum {d n : ℕ} (G : Fin n → UnitAddTorus (Fin d) → ℝ)
      (hG : ∀ i, TorusSmooth (G i)) (x) :
      TorusLaplacian (fun x => ∑ i, G i x) x = ∑ i, TorusLaplacian (G i) x := by
    change (∑ j : Fin d, second (fun y => ∑ i, G i (TorusLift d y))
      (rep x) (EuclideanSpace.single j 1)) =
      ∑ i : Fin n, ∑ j : Fin d, second (fun y => G i (TorusLift d y))
        (rep x) (EuclideanSpace.single j 1)
    simp_rw [second_sum _ hG]
    exact Finset.sum_comm

  have smooth_scale {d : ℕ} (G : UnitAddTorus (Fin d) → ℝ)
      (hG : TorusSmooth G) (b : ℝ) : TorusSmooth (fun x => b*G x) :=
    contDiff_const.mul hG

  have atomic_smooth {d n : ℕ} (G : UnitAddTorus (Fin d) → ℝ)
      (hG : TorusSmooth G) (w : Fin n → ℝ) (z : Fin n → UnitAddTorus (Fin d)) :
      TorusSmooth (AtomicPotential G w z) := by
    change ContDiff ℝ ∞ (fun y => ∑ i, w i * G (TorusLift d y-z i))
    apply ContDiff.sum
    intro i _
    exact smooth_scale _ (smooth_translate G hG (z i)) (w i)

  have atomic_lap {d n : ℕ} (G : UnitAddTorus (Fin d) → ℝ)
      (hG : TorusSmooth G) (w : Fin n → ℝ) (z : Fin n → UnitAddTorus (Fin d)) (x) :
      TorusLaplacian (AtomicPotential G w z) x = ∑ i, w i * TorusLaplacian G (x-z i) := by
    unfold AtomicPotential
    rw [lap_sum _ (fun i => smooth_scale _ (smooth_translate G hG (z i)) (w i))]
    simp_rw [lap_mul _ (smooth_translate G hG _), lap_translate]

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

  have tilt_multiply {Ω : Type} [MeasurableSpace Ω]
      (μ : Measure Ω) (w b : Ω → ℝ) (l u : ℝ)
      (hw : Measurable w) (hwp : ∀ᵐ x ∂μ, 0 ≤ w x)
      (hwi : Integrable w μ) (hZ : 0 < ∫ x, w x ∂μ)
      (hb : Measurable b) (hl : 0 < l)
      (hbb : ∀ᵐ x ∂μ, l ≤ b x ∧ b x ≤ u) :
      NormalizedTilt μ (fun x => b x * w x) =
        NormalizedTilt (NormalizedTilt μ w) b := by
    have hbn : ∀ᵐ x ∂μ, 0 ≤ b x := hbb.mono fun x hx => hl.le.trans hx.1
    have hbabs : ∀ᵐ x ∂μ, ‖b x‖ ≤ max |l| |u| := by
      filter_upwards [hbb, hbn] with x hx hp
      rw [Real.norm_eq_abs, abs_of_nonneg hp]
      exact hx.2.trans ((le_abs_self u).trans (le_max_right _ _))
    have hbwi : Integrable (fun x => b x * w x) μ := hwi.bdd_mul hb.aestronglyMeasurable hbabs
    have hZbw : 0 < ∫ x, b x * w x ∂μ := by
      have hlow : l * ∫ x, w x ∂μ ≤ ∫ x, b x * w x ∂μ := by
        rw [← integral_const_mul]
        apply integral_mono_ae (hwi.const_mul l) hbwi
        filter_upwards [hbb, hwp] with x hx hp
        exact mul_le_mul_of_nonneg_right hx.1 hp
      exact (mul_pos hl hZ).trans_le hlow
    have ht := (TiltNormalization μ w hw hwp hwi hZ).2 b hb (by
      simpa only [mul_comm] using hbwi)
    simp only [NormalizedTilt] at ht ⊢
    rw [ht.2]
    rw [← withDensity_mul μ (by fun_prop) (by fun_prop)]
    apply withDensity_congr_ae
    filter_upwards [hwp, hbn] with x hx hbpos
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (div_nonneg hx hZ.le)]
    congr 1
    field_simp [ne_of_gt hZ, ne_of_gt hZbw]
    <;> ring

  have tilt_scale {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (w : Ω → ℝ)
      (t : ℝ) (ht : t ≠ 0) : NormalizedTilt μ (fun x => t*w x) = NormalizedTilt μ w := by
    unfold NormalizedTilt
    simp only [integral_const_mul]
    congr 1
    funext x
    congr 1
    exact mul_div_mul_left _ _ ht

  have atomic_shift {d n : ℕ} (G : UnitAddTorus (Fin d) → ℝ) (c : ℝ)
      (w : Fin n → ℝ) (y : Fin n → UnitAddTorus (Fin d)) :
      AtomicPotential (fun x => G x+c) w y = fun x => AtomicPotential G w y x +
        (∑ j, w j)*c := by
    funext x
    simp only [AtomicPotential, mul_add, Finset.sum_add_distrib, Finset.sum_mul]

  have hsd' : s < (d : ℝ) := by linarith
  obtain ⟨c, hc, hcf⟩ := RieszL1Foundation d hd s a hs hsd' ha
  obtain ⟨M, hM, _, _, hMf⟩ := RieszHeatSource d hd s a 1 hs hsd ha (by norm_num)
  obtain ⟨rate, hr, hrate⟩ := CompactWeightedPoincare d (by omega) (B*c) (B*M)
    (mul_nonneg hB hc) (mul_nonneg hB hM)
  refine ⟨rate, hr, ?_⟩
  intro n w y hw hmass ε hε
  let G := RieszKernel d s a ε
  let Gc := fun x => G x+c
  let U := AtomicPotential G w y
  let V := AtomicPotential Gc w y
  let ν := NormalizedTilt volume (fun x => Real.exp (-U x))
  have hGF := hcf ε hε.le
  have hGs : TorusSmooth G := (RieszLocalStructure d hd s a hs hsd' ha).2.1 ε hε
  have hGcs : TorusSmooth Gc := hGs.add contDiff_const
  have hVs : TorusSmooth V := atomic_smooth Gc hGcs w y
  have hUs : TorusSmooth U := atomic_smooth G hGs w y
  have hVp (x) : 0 ≤ V x := by
    apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg (hw j)
    have h := hGF.2.2.2.2.1 (x-y j)
    dsimp [Gc]
    linarith
  haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simpa using (inferInstance : IsProbabilityMeasure AddCircle.haarAddCircle)
  haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin d =>
      (volume : Measure (AddCircle (1 : ℝ))))))
  have hGi : Integrable G volume := hGF.2.1
  have hGci : Integrable Gc volume := hGi.add (integrable_const c)
  have hVm : (∫ x, V x) ≤ B*c := by
    have hterm (j) : Integrable (fun x => w j * Gc (x-y j)) volume :=
      ((measurePreserving_sub_right volume (y j)).integrable_comp
        (continuous hGcs).aestronglyMeasurable |>.mpr hGci).const_mul _
    change (∫ x, ∑ j, w j * Gc (x-y j)) ≤ _
    rw [integral_finsetSum _ (fun j _ => hterm j)]
    simp_rw [integral_const_mul, integral_sub_right_eq_self]
    have hmean : (∫ x, Gc x) = c := by
      rw [integral_add hGi (integrable_const c), hGF.2.2.1]
      simp
    rw [hmean, ← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right hmass hc
  have hVL (x) : TorusLaplacian V x ≤ B*M := by
    rw [atomic_lap Gc hGcs w y x]
    have hLapG (z) : TorusLaplacian Gc z ≤ M := by
      rw [lap_add_const]
      exact (hMf ε hε).2.2.2 z
    calc
      ∑ j, w j * TorusLaplacian Gc (x-y j) ≤ ∑ j, w j*M :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hLapG _) (hw j))
      _ = (∑ j,w j)*M := (Finset.sum_mul _ _ _).symm
      _ ≤ B*M := mul_le_mul_of_nonneg_right hmass hM
  have hν : NormalizedTilt volume (fun x => Real.exp (-V x)) = ν := by
    have hfun : (fun x => Real.exp (-V x)) =
        fun x => Real.exp (-((∑ j,w j)*c)) * Real.exp (-U x) := by
      funext x
      rw [show V x = U x+(∑ j,w j)*c from congrFun (atomic_shift G c w y) x]
      rw [neg_add, Real.exp_add]
      exact mul_comm _ _
    rw [hfun]
    exact tilt_scale _ _ _ (ne_of_gt (Real.exp_pos _))
  have hPI := hrate V hVs hVp hVm hVL
  rw [hν] at hPI
  have hweight : Continuous (fun x => Real.exp (-U x)) :=
    Real.continuous_exp.comp (continuous hUs).neg
  have hwi : Integrable (fun x => Real.exp (-U x)) volume :=
    hweight.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hZ : 0 < ∫ x, Real.exp (-U x) := integral_exp_pos hwi
  have ht := TiltNormalization volume (fun x => Real.exp (-U x)) hweight.measurable
    (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)) hwi hZ
  haveI : IsProbabilityMeasure ν := ht.1
  refine ⟨hPI, ?_⟩
  intro b l u hb hl hbounds f hf
  have hac : ν.AbsolutelyContinuous volume := withDensity_absolutelyContinuous _ _
  have hboundsν := hbounds.filter_mono hac.ae_le
  have cg : Continuous (TorusGradient f) :=
    (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).continuous_symm.comp
      (continuous_pi (fun j => continuous (gradient_smooth hf j)))
  have hfbound : ∃ C : ℝ, ∀ᵐ x ∂ν, |f x| ≤ C := by
    obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn (continuous hf).continuousOn
    refine ⟨C, Filter.Eventually.of_forall (fun x => ?_)⟩
    simpa only [Real.norm_eq_abs] using hC x (Set.mem_univ x)
  have hei : Integrable (fun x => ‖TorusGradient f x‖^2) ν :=
    (cg.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hc := BoundedDensityComparison ν b f (fun x => ‖TorusGradient f x‖^2)
    l u hl hb hboundsν (continuous hf).measurable hfbound (cg.norm.pow 2).measurable
      (Filter.Eventually.of_forall (fun x => sq_nonneg _)) hei
  have hw' := BoundedTiltBounds ν b l u hl hb hboundsν
  have hZb : 0 < ∫ x,b x ∂ν := hl.trans_le hw'.2.1
  have hcomp := tilt_multiply volume (fun x => Real.exp (-U x)) b l u
    hweight.measurable (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le))
    hwi hZ hb hl hbounds
  rw [hcomp]
  calc
    ProbabilityTheory.variance f (NormalizedTilt ν b) ≤
        (u / (∫ x,b x ∂ν)) * ProbabilityTheory.variance f ν := hc.1
    _ ≤ (u / (∫ x,b x ∂ν)) * (rate⁻¹ * ∫ x, ‖TorusGradient f x‖^2 ∂ν) := by
      apply mul_le_mul_of_nonneg_left (hPI f hf)
      exact div_nonneg (by
        have hlu : l ≤ u := by
          obtain ⟨x,hx⟩ := hboundsν.exists
          exact hx.1.trans hx.2
        exact hl.le.trans hlu) hZb.le
    _ ≤ (u/l)*rate⁻¹ * (∫ x, ‖TorusGradient f x‖^2 ∂NormalizedTilt ν b) := by
      have hE := hc.2.2.1
      have hlu : l ≤ u := by obtain ⟨x,hx⟩ := hboundsν.exists; exact hx.1.trans hx.2
      have hfac : 0 ≤ (u/l)*rate⁻¹ := mul_nonneg (div_nonneg (hl.le.trans hlu) hl.le)
        (inv_nonneg.mpr hr.le)
      have h := mul_le_mul_of_nonneg_left hE hfac
      have hid : (u/l)*rate⁻¹ * ((l/(∫ x,b x ∂ν))*∫ x, ‖TorusGradient f x‖^2 ∂ν) =
          (u/(∫ x,b x ∂ν))*(rate⁻¹ * ∫ x, ‖TorusGradient f x‖^2 ∂ν) := by
        field_simp [ne_of_gt hl]
        <;> ring
      rw [hid] at h
      exact h
