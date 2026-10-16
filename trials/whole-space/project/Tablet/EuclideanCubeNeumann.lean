module

public import Tablet.EuclideanGradient
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.Calculus.Gradient.Basic

@[expose] public section
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
namespace EuclideanCubeNeumann


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private def parameterDerivative (F : E × ℝ → ℝ) (p : E × ℝ) : E →L[ℝ] ℝ :=
  (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E ℝ)

omit [FiniteDimensional ℝ E] in
private theorem parameterDerivative_continuous (F : E × ℝ → ℝ) (hF : ContDiff ℝ 1 F) :
    Continuous (parameterDerivative F) :=
  (hF.continuous_fderiv (by norm_num)).clm_comp continuous_const

private theorem finite_dimensional_interval_mean_hasFDerivAt
    (F : E × ℝ → ℝ) (hF : ContDiff ℝ 1 F)
    (a b : ℝ) (hab : a ≤ b) (x₀ : E) :
    HasFDerivAt (fun x => ∫ y in a..b, F (x,y))
      (∫ y in a..b, parameterDerivative F (x₀,y)) x₀ := by
  obtain ⟨K,hKcompact,hKnhds⟩ := exists_compact_mem_nhds x₀
  have hd := parameterDerivative_continuous F hF
  obtain ⟨C,hC⟩ := (hKcompact.prod (isCompact_Icc (a := a) (b := b))).bddAbove_image
    hd.norm.continuousOn
  have hr (x : E) : Continuous (fun y => F (x,y)) :=
    hF.continuous.comp (continuous_const.prodMk continuous_id)
  have hdr (x : E) : Continuous (fun y => parameterDerivative F (x,y)) :=
    hd.comp (continuous_const.prodMk continuous_id)
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x y => F (x,y)) (F' := fun x y => parameterDerivative F (x,y))
    (bound := fun _ => C) hKnhds
    (Filter.Eventually.of_forall (fun x => (hr x).aestronglyMeasurable))
    ((hr x₀).intervalIntegrable a b) (hdr x₀).aestronglyMeasurable ?_
    (continuous_const.intervalIntegrable a b) ?_
  · filter_upwards with y hy x hx
    have hycc : y ∈ Icc a b := by
      rw [uIoc_of_le hab] at hy
      exact ⟨hy.1.le,hy.2⟩
    exact hC (mem_image_of_mem _ ⟨hx,hycc⟩)
  · filter_upwards with y _ x _
    exact (hF.differentiable (by norm_num) (x,y)).hasFDerivAt.comp x
      (hasFDerivAt_prodMk_left x y)

private theorem finite_dimensional_interval_mean_C1
    (F : E × ℝ → ℝ) (hF : ContDiff ℝ 1 F)
    (a b : ℝ) (hab : a ≤ b) :
    ContDiff ℝ 1 (fun x => ∫ y in a..b, F (x,y)) ∧
    fderiv ℝ (fun x => ∫ y in a..b, F (x,y)) =
      (fun x => ∫ y in a..b, parameterDerivative F (x,y)) := by
  have hd (x : E) := finite_dimensional_interval_mean_hasFDerivAt F hF a b hab x
  have heq : fderiv ℝ (fun x => ∫ y in a..b, F (x,y)) =
      (fun x => ∫ y in a..b, parameterDerivative F (x,y)) :=
    funext (fun x => (hd x).fderiv)
  refine ⟨contDiff_one_iff_fderiv.mpr ⟨fun x => (hd x).differentiableAt, ?_⟩,heq⟩
  rw [heq]
  have h := continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun x y => parameterDerivative F (x,y))
    (parameterDerivative_continuous F hF) (isCompact_Icc (a := a) (b := b))
  simp_rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab] at h
  exact h




private theorem finite_measure_integral_sq_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (g : α → ℝ)
    (hg : Integrable g μ) (hg2 : Integrable (fun x => g x ^ 2) μ)
    (hm : 0 < μ.real Set.univ) :
    (∫ x, g x ∂μ)^2 ≤ μ.real Set.univ * ∫ x, g x^2 ∂μ := by
  let c := (∫ x, g x ∂μ) / μ.real Set.univ
  have hnon : 0 ≤ ∫ x, (g x-c)^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have heq : (∫ x, (g x-c)^2 ∂μ) =
      (∫ x, g x^2 ∂μ) - 2*c*(∫ x, g x ∂μ) + μ.real Set.univ*c^2 := by
    simp_rw [show ∀ x, (g x-c)^2 = g x^2 - (2*c)*g x+c^2 by intro x; ring]
    rw [integral_add (f := fun x => g x^2 - (2*c)*g x)
      (g := fun _ => c^2) (hg2.sub (hg.const_mul _)) (integrable_const _),
      integral_sub (f := fun x => g x^2) (g := fun x => (2*c)*g x)
        hg2 (hg.const_mul _), integral_const_mul, integral_const]
    simp only [smul_eq_mul]
  rw [heq] at hnon
  have hmul := mul_nonneg hnon hm.le
  dsimp [c] at hmul
  field_simp at hmul
  nlinarith

private theorem interval_integral_sq_bound (a b : ℝ) (hab : a < b)
    (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ x in a..b, g x)^2 ≤ (b-a) * ∫ x in a..b, g x^2 := by
  have hgi : IntegrableOn g (Icc a b) volume := hg.integrableOn_Icc
  have hg2i : IntegrableOn (fun x => g x^2) (Icc a b) volume := (hg.pow 2).integrableOn_Icc
  have hmass : (volume.restrict (Icc a b)).real Set.univ = b-a := by
    simp [Measure.real, Real.volume_Icc, hab.le]
  have h := finite_measure_integral_sq_bound (volume.restrict (Icc a b)) g
    hgi hg2i (by rw [hmass]; linarith)
  rw [hmass, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab.le,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le] at h
  exact h

private theorem interval_anchored_pointwise (a b : ℝ) (hab : a < b)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (x : ℝ) (hx : x ∈ Icc a b) :
    (f x-f a)^2 ≤ (b-a) * ∫ t in a..b, (deriv f t)^2 := by
  have hd := hf.continuous_deriv_one
  have hE : 0 ≤ ∫ t in a..b, (deriv f t)^2 :=
    intervalIntegral.integral_nonneg hab.le (fun _ _ => sq_nonneg _)
  rcases eq_or_lt_of_le hx.1 with hax | hax
  · subst x
    simpa using mul_nonneg (sub_nonneg.mpr hab.le) hE
  have hsmall := interval_integral_sq_bound a x hax (deriv f) hd
  rw [intervalIntegral.integral_deriv_eq_sub
    (fun _ _ => hf.differentiable (by norm_num) _) (hd.intervalIntegrable a x)] at hsmall
  have hmono : (∫ t in a..x, (deriv f t)^2) ≤ ∫ t in a..b, (deriv f t)^2 :=
    intervalIntegral.integral_mono_interval (le_refl a) hx.1 hx.2
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) ((hd.pow 2).intervalIntegrable a b)
  calc
    (f x-f a)^2 ≤ (x-a) * ∫ t in a..x, (deriv f t)^2 := hsmall
    _ ≤ (x-a) * ∫ t in a..b, (deriv f t)^2 :=
      mul_le_mul_of_nonneg_left hmono (sub_nonneg.mpr hx.1)
    _ ≤ (b-a) * ∫ t in a..b, (deriv f t)^2 :=
      mul_le_mul_of_nonneg_right (by linarith [hx.2]) hE

private theorem interval_anchored_poincare (a b : ℝ) (hab : a < b)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
    (∫ x in a..b, (f x-f a)^2) ≤ (b-a)^2 * ∫ x in a..b, (deriv f x)^2 := by
  have h := intervalIntegral.integral_mono_on (μ := volume) hab.le
    (((hf.continuous.sub (continuous_const : Continuous (fun _ : ℝ => f a))).pow 2).intervalIntegrable a b)
    ((continuous_const : Continuous (fun _ : ℝ => (b-a) * ∫ x in a..b, (deriv f x)^2)).intervalIntegrable a b)
    (fun x hx => interval_anchored_pointwise a b hab f hf x hx)
  simpa [intervalIntegral.integral_const, pow_two, mul_assoc] using h

private theorem finite_measure_centered_sq_le (α : Type*) [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ)
    (hf : Integrable f μ) (hf2 : Integrable (fun x => f x^2) μ)
    (hm : 0 < μ.real Set.univ) (c : ℝ) :
    (∫ x, (f x-(∫ y, f y ∂μ)/μ.real Set.univ)^2 ∂μ) ≤
      ∫ x, (f x-c)^2 ∂μ := by
  let m := (∫ y, f y ∂μ) / μ.real Set.univ
  have hformula (t : ℝ) : (∫ x, (f x-t)^2 ∂μ) =
      (∫ x, f x^2 ∂μ) - 2*t*(∫ x, f x ∂μ) + μ.real Set.univ*t^2 := by
    simp_rw [show ∀ x, (f x-t)^2 = f x^2 - (2*t)*f x+t^2 by intro x; ring]
    rw [integral_add (f := fun x => f x^2-(2*t)*f x)
      (g := fun _ => t^2) (hf2.sub (hf.const_mul _)) (integrable_const _),
      integral_sub (f := fun x => f x^2) (g := fun x => (2*t)*f x)
        hf2 (hf.const_mul _), integral_const_mul, integral_const]
    simp only [smul_eq_mul]
  have hmG : μ.real Set.univ * m = ∫ x, f x ∂μ := by
    dsimp [m]
    field_simp
  have hnon := mul_nonneg hm.le (sq_nonneg (c-m))
  change (∫ x, (f x-m)^2 ∂μ) ≤ _
  rw [hformula m, hformula c]
  have hdiff : ((∫ x, f x^2 ∂μ) - 2*c*(∫ x, f x ∂μ) + μ.real Set.univ*c^2) -
      ((∫ x, f x^2 ∂μ) - 2*m*(∫ x, f x ∂μ) + μ.real Set.univ*m^2) =
      μ.real Set.univ*(c-m)^2 := by
    rw [← hmG]
    ring
  linarith

private theorem interval_neumann_poincare (a b : ℝ) (hab : a < b)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
    (∫ x in a..b, (f x-(∫ y in a..b, f y)/(b-a))^2) ≤
      (b-a)^2 * ∫ x in a..b, (deriv f x)^2 := by
  have hmass : (volume.restrict (Icc a b)).real Set.univ = b-a := by
    simp [Measure.real, Real.volume_Icc, hab.le]
  have hmin := finite_measure_centered_sq_le ℝ (volume.restrict (Icc a b)) f
    hf.continuous.integrableOn_Icc (hf.continuous.pow 2).integrableOn_Icc
    (by rw [hmass]; linarith) (f a)
  rw [hmass] at hmin
  simp_rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le] at hmin
  exact hmin.trans (interval_anchored_poincare a b hab f hf)




private theorem interval_row_split (a b : ℝ) (hab : a < b) (f : ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) (c : ℝ) :
    (∫ y in a..b, (f y-c)^2) ≤
      2*(b-a)^2*(∫ y in a..b, (deriv f y)^2) +
      2*(b-a)*((∫ y in a..b, f y)/(b-a)-c)^2 := by
  let m := (∫ y in a..b, f y)/(b-a)
  have hs : ∀ y, (f y-c)^2 ≤ 2*(f y-m)^2+2*(m-c)^2 := by
    intro y
    nlinarith [sq_nonneg (f y-2*m+c)]
  have h := intervalIntegral.integral_mono_on (μ := volume) hab.le
    (((hf.continuous.sub continuous_const).pow 2).intervalIntegrable a b)
    (((((hf.continuous.sub continuous_const).pow 2).const_mul 2).add
      continuous_const).intervalIntegrable a b) (fun y _ => hs y)
  change (∫ y in a..b, (f y-c)^2) ≤
    ∫ y in a..b, 2*(f y-m)^2+2*(m-c)^2 at h
  rw [intervalIntegral.integral_add (μ := volume)
    (f := fun y => 2*(f y-m)^2) (g := fun _ => 2*(m-c)^2)
    ((((hf.continuous.sub (continuous_const : Continuous (fun _ : ℝ => m))).pow 2).const_mul 2).intervalIntegrable a b)
      ((continuous_const : Continuous (fun _ : ℝ => 2*(m-c)^2)).intervalIntegrable a b)] at h
  simp only [intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at h
  have hpi := interval_neumann_poincare a b hab f hf
  dsimp [m] at h
  linarith




private def cubeIntegral (a b : ℝ) : (n : ℕ) → ((Fin n → ℝ) → ℝ) → ℝ
  | 0, f => f (fun i => Fin.elim0 i)
  | n+1, f => cubeIntegral a b n (fun q => ∫ t in a..b, f (Fin.cons t q))

private theorem finCons_C1 (n : ℕ) :
    ContDiff ℝ 1 (fun p : (Fin n → ℝ) × ℝ => (Fin.cons p.2 p.1 : Fin (n+1) → ℝ)) := by
  apply contDiff_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using (contDiff_snd : ContDiff ℝ 1 (fun p : (Fin n → ℝ) × ℝ => p.2))
  · simpa [Function.comp_def] using (contDiff_apply ℝ ℝ j).comp
      (contDiff_fst : ContDiff ℝ 1 (fun p : (Fin n → ℝ) × ℝ => p.1))

private theorem cube_integral_const (a b c : ℝ) (n : ℕ) :
    cubeIntegral a b n (fun _ => c) = (b-a)^n*c := by
  induction n generalizing c with
  | zero => simp [cubeIntegral]
  | succ n ih =>
    simp only [cubeIntegral, intervalIntegral.integral_const, smul_eq_mul]
    rw [ih]
    ring

private theorem coordinate_mean_C1 (a b : ℝ) (hab : a ≤ b) (n : ℕ)
    (f : (Fin (n+1) → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) :
    ContDiff ℝ 1 (fun q : Fin n → ℝ => ∫ t in a..b, f (Fin.cons t q)) := by
  exact (finite_dimensional_interval_mean_C1
    (fun p : (Fin n → ℝ) × ℝ => f (Fin.cons p.2 p.1))
    (hf.comp (finCons_C1 n)) a b hab).1

private theorem coordinate_mean_continuous (a b : ℝ) (hab : a ≤ b) (n : ℕ)
    (f : (Fin (n+1) → ℝ) → ℝ) (hf : Continuous f) :
    Continuous (fun q : Fin n → ℝ => ∫ t in a..b, f (Fin.cons t q)) := by
  have h := continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun q t => f (Fin.cons t q))
    (hf.comp (finCons_C1 n).continuous) (isCompact_Icc (a := a) (b := b))
  simp_rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab] at h
  exact h

private theorem cube_integral_mono (a b : ℝ) (hab : a ≤ b) (n : ℕ)
    (f g : (Fin n → ℝ) → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hle : ∀ q, f q ≤ g q) : cubeIntegral a b n f ≤ cubeIntegral a b n g := by
  induction n with
  | zero => exact hle _
  | succ n ih =>
    apply ih (fun q => ∫ t in a..b, f (Fin.cons t q))
      (fun q => ∫ t in a..b, g (Fin.cons t q))
      (coordinate_mean_continuous a b hab n f hf)
      (coordinate_mean_continuous a b hab n g hg)
    intro q
    exact intervalIntegral.integral_mono_on (μ := volume) hab
      ((hf.comp (continuous_id.finCons continuous_const)).intervalIntegrable a b)
      ((hg.comp (continuous_id.finCons continuous_const)).intervalIntegrable a b)
      (fun t _ => hle (Fin.cons t q))

private theorem cube_integral_add (a b : ℝ) (hab : a ≤ b) (n : ℕ)
    (f g : (Fin n → ℝ) → ℝ) (hf : Continuous f) (hg : Continuous g) :
    cubeIntegral a b n (fun q => f q+g q) =
      cubeIntegral a b n f+cubeIntegral a b n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [cubeIntegral]
    have heq : (fun q : Fin n → ℝ => ∫ t in a..b,
        f (Fin.cons t q)+g (Fin.cons t q)) =
        (fun q => (∫ t in a..b, f (Fin.cons t q))+(∫ t in a..b, g (Fin.cons t q))) := by
      funext q
      exact intervalIntegral.integral_add (μ := volume)
        (f := fun t => f (Fin.cons t q)) (g := fun t => g (Fin.cons t q))
        ((hf.comp (continuous_id.finCons continuous_const)).intervalIntegrable a b)
        ((hg.comp (continuous_id.finCons continuous_const)).intervalIntegrable a b)
    rw [heq]
    exact ih (fun q => ∫ t in a..b, f (Fin.cons t q))
      (fun q => ∫ t in a..b, g (Fin.cons t q))
      (coordinate_mean_continuous a b hab n f hf)
      (coordinate_mean_continuous a b hab n g hg)

private theorem cube_integral_const_mul (a b c : ℝ) (n : ℕ)
    (f : (Fin n → ℝ) → ℝ) :
    cubeIntegral a b n (fun q => c*f q) = c*cubeIntegral a b n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [cubeIntegral, intervalIntegral.integral_const_mul]
    exact ih (fun q => ∫ t in a..b, f (Fin.cons t q))

private theorem coordinate_mean_fderiv_apply (a b : ℝ) (hab : a ≤ b) (n : ℕ)
    (f : (Fin (n+1) → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (q v : Fin n → ℝ) :
    fderiv ℝ (fun q => ∫ t in a..b, f (Fin.cons t q)) q v =
      ∫ t in a..b, fderiv ℝ f (Fin.cons t q) (Fin.cons 0 v) := by
  let H : (Fin n → ℝ) × ℝ → ℝ := fun p => f (Fin.cons p.2 p.1)
  have hH : ContDiff ℝ 1 H := hf.comp (finCons_C1 n)
  have hm := finite_dimensional_interval_mean_hasFDerivAt H hH a b hab q
  rw [hm.fderiv]
  have hd : Continuous (fun t => parameterDerivative H (q,t)) :=
    (parameterDerivative_continuous H hH).comp (continuous_const.prodMk continuous_id)
  rw [ContinuousLinearMap.intervalIntegral_apply (hd.intervalIntegrable a b)]
  apply intervalIntegral.integral_congr
  intro t _
  have hc : HasFDerivAt (fun p : (Fin n → ℝ) × ℝ => (Fin.cons p.2 p.1 : Fin (n+1) → ℝ))
      ((ContinuousLinearMap.snd ℝ (Fin n → ℝ) ℝ).finCons
        (ContinuousLinearMap.fst ℝ (Fin n → ℝ) ℝ)) (q,t) :=
    (hasFDerivAt_snd (𝕜 := ℝ) (p := (q,t))).finCons (hasFDerivAt_fst (𝕜 := ℝ) (p := (q,t)))
  have hh := (hf.differentiable (by norm_num) (Fin.cons t q)).hasFDerivAt.comp (q,t) hc
  change fderiv ℝ H (q,t) (v,0) = _
  change (fderiv ℝ (f ∘ fun p : (Fin n → ℝ) × ℝ => Fin.cons p.2 p.1) (q,t)) (v,0) = _
  rw [hh.fderiv]
  rfl

private def cubeGradientSquare (n : ℕ) (f : (Fin n → ℝ) → ℝ) (q : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, (fderiv ℝ f q (Pi.single i 1))^2

private theorem cube_gradient_square_continuous (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (hf : ContDiff ℝ 1 f) : Continuous (cubeGradientSquare n f) := by
  apply continuous_finsetSum
  intro i _
  exact ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2

private theorem normalized_coordinate_mean_fderiv_apply (a b : ℝ) (hab : a < b) (n : ℕ)
    (f : (Fin (n+1) → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (q v : Fin n → ℝ) :
    fderiv ℝ (fun q => (∫ t in a..b, f (Fin.cons t q))/(b-a)) q v =
      (∫ t in a..b, fderiv ℝ f (Fin.cons t q) (Fin.cons 0 v))/(b-a) := by
  have hm := (coordinate_mean_C1 a b hab.le n f hf).differentiable (by norm_num) q
  have h := congrArg (fun z => (b-a)⁻¹*z) (coordinate_mean_fderiv_apply a b hab.le n f hf q v)
  simpa [div_eq_mul_inv, mul_comm, fderiv_const_mul hm] using h

private theorem coordinate_mean_component_energy (a b : ℝ) (hab : a < b) (n : ℕ)
    (f : (Fin (n+1) → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (q v : Fin n → ℝ) :
    (b-a)*(fderiv ℝ (fun q => (∫ t in a..b, f (Fin.cons t q))/(b-a)) q v)^2 ≤
      ∫ t in a..b, (fderiv ℝ f (Fin.cons t q) (Fin.cons 0 v))^2 := by
  have hcont : Continuous (fun t : ℝ => fderiv ℝ f (Fin.cons t q) (Fin.cons 0 v)) :=
    ((hf.continuous_fderiv (by norm_num)).comp
      (continuous_id.finCons continuous_const)).clm_apply continuous_const
  have h := interval_integral_sq_bound a b hab
    (fun t => fderiv ℝ f (Fin.cons t q) (Fin.cons 0 v)) hcont
  rw [normalized_coordinate_mean_fderiv_apply a b hab n f hf q v]
  have hL : 0 < b-a := sub_pos.mpr hab
  have hdiv : (∫ t in a..b, fderiv ℝ f (Fin.cons t q) (Fin.cons 0 v))^2/(b-a) ≤
      ∫ t in a..b, (fderiv ℝ f (Fin.cons t q) (Fin.cons 0 v))^2 :=
    (div_le_iff₀ hL).mpr (by simpa [mul_comm] using h)
  convert hdiv using 1
  field_simp

private theorem coordinate_mean_gradient_energy (a b : ℝ) (hab : a < b) (n : ℕ)
    (f : (Fin (n+1) → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) (q : Fin n → ℝ) :
    (b-a)*cubeGradientSquare n (fun q => (∫ t in a..b, f (Fin.cons t q))/(b-a)) q ≤
      (n : ℝ)*(∫ t in a..b, cubeGradientSquare (n+1) f (Fin.cons t q)) := by
  have hcomp (i : Fin n) :
      (b-a)*(fderiv ℝ (fun q => (∫ t in a..b, f (Fin.cons t q))/(b-a)) q (Pi.single i 1))^2 ≤
        ∫ t in a..b, cubeGradientSquare (n+1) f (Fin.cons t q) := by
    have h := coordinate_mean_component_energy a b hab n f hf q (Pi.single i 1)
    have hv : (Fin.cons 0 (Pi.single i 1) : Fin (n+1) → ℝ) = Pi.single i.succ 1 := by
      ext j
      refine Fin.cases ?_ (fun k => ?_) j
      · simp
      · simp [Pi.single_apply]
    rw [hv] at h
    refine h.trans (intervalIntegral.integral_mono_on (μ := volume) hab.le ?_ ?_ ?_)
    · exact (((hf.continuous_fderiv (by norm_num)).comp
        (continuous_id.finCons continuous_const)).clm_apply continuous_const).pow 2
          |>.intervalIntegrable a b
    · exact ((cube_gradient_square_continuous (n+1) f hf).comp
        (continuous_id.finCons continuous_const)).intervalIntegrable a b
    · intro t _
      change (fderiv ℝ f (Fin.cons t q) (Pi.single i.succ 1))^2 ≤
        ∑ j : Fin (n+1), (fderiv ℝ f (Fin.cons t q) (Pi.single j 1))^2
      exact Finset.single_le_sum
        (fun j _ => sq_nonneg (fderiv ℝ f (Fin.cons t q) (Pi.single j 1)))
        (Finset.mem_univ i.succ)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hcomp i)
  simpa [cubeGradientSquare, Finset.mul_sum] using hsum

private def cubeMean (a b : ℝ) (n : ℕ) (f : (Fin n → ℝ) → ℝ) : ℝ :=
  cubeIntegral a b n f/(b-a)^n

private theorem cube_mean_coordinate_recursion (a b : ℝ) (hab : a < b) (n : ℕ)
    (f : (Fin (n+1) → ℝ) → ℝ) :
    cubeMean a b (n+1) f =
      cubeMean a b n (fun q => (∫ t in a..b, f (Fin.cons t q))/(b-a)) := by
  dsimp [cubeMean,cubeIntegral]
  have heq : (fun q : Fin n → ℝ => (∫ t in a..b, f (Fin.cons t q))/(b-a)) =
      (fun q => (b-a)⁻¹*(∫ t in a..b, f (Fin.cons t q))) := by
    funext q
    simp [div_eq_mul_inv,mul_comm]
  rw [heq,cube_integral_const_mul]
  have hL : (b-a) ≠ 0 := (sub_pos.mpr hab).ne'
  field_simp [hL]
  ring

private theorem coordinate_row_deriv (n : ℕ) (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : ContDiff ℝ 1 f) (q : Fin n → ℝ) (t : ℝ) :
    deriv (fun u => f (Fin.cons u q)) t = fderiv ℝ f (Fin.cons t q) (Pi.single 0 1) := by
  have hc : HasDerivAt (fun u : ℝ => (Fin.cons u q : Fin (n+1) → ℝ))
      (Fin.cons 1 (0 : Fin n → ℝ)) t :=
    (hasDerivAt_id t).finCons (hasDerivAt_const t q)
  have hv : (Fin.cons 1 (0 : Fin n → ℝ) : Fin (n+1) → ℝ) = Pi.single 0 1 := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  simpa [hv,Function.comp_def] using ((hf.differentiable (by norm_num) (Fin.cons t q)).hasFDerivAt.comp_hasDerivAt t hc).deriv

private def cubePoincareConstant : ℕ → ℝ
  | 0 => 1
  | n+1 => 2+2*(n : ℝ)*cubePoincareConstant n

private theorem cube_poincare_constant_positive (n : ℕ) : 0 < cubePoincareConstant n := by
  induction n with
  | zero => norm_num [cubePoincareConstant]
  | succ n ih => dsimp [cubePoincareConstant]; positivity

private theorem finite_dimension_cube_neumann (a b : ℝ) (hab : a < b) (n : ℕ)
    (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) :
    cubeIntegral a b n (fun q => (f q-cubeMean a b n f)^2) ≤
      cubePoincareConstant n*(b-a)^2*cubeIntegral a b n (cubeGradientSquare n f) := by
  induction n with
  | zero => simp [cubeIntegral,cubeMean,cubeGradientSquare]
  | succ n ih =>
    let L := b-a
    let R := fun q : Fin n → ℝ => (∫ t in a..b, f (Fin.cons t q))/L
    let c := cubeMean a b n R
    let E := fun q : Fin n → ℝ => ∫ t in a..b, cubeGradientSquare (n+1) f (Fin.cons t q)
    have hL : 0 < L := sub_pos.mpr hab
    have hR : ContDiff ℝ 1 R := (coordinate_mean_C1 a b hab.le n f hf).div_const L
    have hE : Continuous E := coordinate_mean_continuous a b hab.le n
      (cubeGradientSquare (n+1) f) (cube_gradient_square_continuous (n+1) f hf)
    have hrow (q : Fin n → ℝ) :
        (∫ t in a..b, (f (Fin.cons t q)-c)^2) ≤ 2*L^2*E q+2*L*(R q-c)^2 := by
      have hrc : ContDiff ℝ 1 (fun t => f (Fin.cons t q)) := by
        simpa [Function.comp_def] using (hf.comp (finCons_C1 n)).comp
          (contDiff_const.prodMk contDiff_id)
      have h := interval_row_split a b hab (fun t => f (Fin.cons t q)) hrc c
      have hmono : (∫ t in a..b, (deriv (fun u => f (Fin.cons u q)) t)^2) ≤ E q := by
        apply intervalIntegral.integral_mono_on (μ := volume) hab.le
          ((hrc.continuous_deriv_one.pow 2).intervalIntegrable a b)
          (((cube_gradient_square_continuous (n+1) f hf).comp
            (continuous_id.finCons continuous_const)).intervalIntegrable a b)
        intro t _
        change (deriv (fun u => f (Fin.cons u q)) t)^2 ≤ cubeGradientSquare (n+1) f (Fin.cons t q)
        rw [coordinate_row_deriv n f hf q t]
        change (fderiv ℝ f (Fin.cons t q) (Pi.single 0 1))^2 ≤
          ∑ i : Fin (n+1), (fderiv ℝ f (Fin.cons t q) (Pi.single i 1))^2
        exact Finset.single_le_sum
          (fun i _ => sq_nonneg (fderiv ℝ f (Fin.cons t q) (Pi.single i 1))) (Finset.mem_univ 0)
      exact h.trans (add_le_add (mul_le_mul_of_nonneg_left hmono (by positivity)) le_rfl)
    have hmain := cube_integral_mono a b hab.le n
      (fun q => ∫ t in a..b, (f (Fin.cons t q)-c)^2)
      (fun q => 2*L^2*E q+2*L*(R q-c)^2)
      (coordinate_mean_continuous a b hab.le n (fun x => (f x-c)^2)
        ((hf.continuous.sub continuous_const).pow 2))
      ((hE.const_mul _).add (((hR.continuous.sub continuous_const).pow 2).const_mul _)) hrow
    rw [cube_integral_add a b hab.le n (fun q => 2*L^2*E q)
      (fun q => 2*L*(R q-c)^2) (hE.const_mul _)
      (((hR.continuous.sub continuous_const).pow 2).const_mul _),
      cube_integral_const_mul,cube_integral_const_mul] at hmain
    have henergy := cube_integral_mono a b hab.le n
      (fun q => L*cubeGradientSquare n R q) (fun q => (n : ℝ)*E q)
      ((cube_gradient_square_continuous n R hR).const_mul _) (hE.const_mul _)
      (fun q => coordinate_mean_gradient_energy a b hab n f hf q)
    rw [cube_integral_const_mul,cube_integral_const_mul] at henergy
    have hpi := ih R hR
    have hmean : 2*L*cubeIntegral a b n (fun q => (R q-c)^2) ≤
        2*cubePoincareConstant n*L^2*(n : ℝ)*cubeIntegral a b n E := by
      calc
        _ ≤ 2*L*(cubePoincareConstant n*L^2*cubeIntegral a b n (cubeGradientSquare n R)) :=
          mul_le_mul_of_nonneg_left hpi (by positivity)
        _ = (2*cubePoincareConstant n*L^2)*(L*cubeIntegral a b n (cubeGradientSquare n R)) := by ring
        _ ≤ (2*cubePoincareConstant n*L^2)*((n : ℝ)*cubeIntegral a b n E) :=
          mul_le_mul_of_nonneg_left henergy (by have hk := cube_poincare_constant_positive n; positivity)
        _ = _ := by ring
    rw [cube_mean_coordinate_recursion a b hab n f]
    change cubeIntegral a b n (fun q => ∫ t in a..b, (f (Fin.cons t q)-c)^2) ≤ _
    calc
      _ ≤ _ := hmain
      _ ≤ 2*L^2*cubeIntegral a b n E +
          2*cubePoincareConstant n*L^2*(n : ℝ)*cubeIntegral a b n E := add_le_add le_rfl hmean
      _ = _ := by dsimp [cubePoincareConstant,cubeIntegral,E,L]; ring




private def cubeBox (a b : ℝ) (n : ℕ) : Set (Fin n → ℝ) := Set.univ.pi (fun _ => Icc a b)
private abbrev cubeBoxMeasure (a b : ℝ) (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => volume.restrict (Icc a b))

private theorem cube_box_measure_restricted_volume (a b : ℝ) (n : ℕ) :
    cubeBoxMeasure a b n = volume.restrict (cubeBox a b n) := by
  exact (Measure.restrict_pi_pi (μ := fun _ : Fin n => (volume : Measure ℝ))
    (fun _ => Icc a b)).symm

private theorem continuous_cube_box_integrable (a b : ℝ) (n : ℕ)
    (f : (Fin n → ℝ) → ℝ) (hf : Continuous f) : Integrable f (cubeBoxMeasure a b n) := by
  rw [cube_box_measure_restricted_volume]
  exact hf.continuousOn.integrableOn_compact (isCompact_univ_pi (fun _ => isCompact_Icc))

private theorem cube_integral_product_measure_identity (a b : ℝ) (hab : a ≤ b) (n : ℕ)
    (f : (Fin n → ℝ) → ℝ) (hf : Continuous f) :
    cubeIntegral a b n f = ∫ q, f q ∂cubeBoxMeasure a b n := by
  induction n with
  | zero =>
    dsimp [cubeIntegral,cubeBoxMeasure]
    rw [Measure.pi_of_empty (fun _ : Fin 0 => volume.restrict (Icc a b))
      (fun i => Fin.elim0 i)]
    simp
  | succ n ih =>
    let ν : Measure ℝ := volume.restrict (Icc a b)
    let μ := fun _ : Fin (n+1) => ν
    have hp := (measurePreserving_piFinSuccAbove μ 0).symm
    have hfi := hp.integrable_comp_of_integrable (continuous_cube_box_integrable a b (n+1) f hf)
    have hfi' : Integrable (fun p : ℝ × (Fin n → ℝ) => f (Fin.cons p.1 p.2))
        (ν.prod (cubeBoxMeasure a b n)) := by
      simpa [Function.comp_def, cubeBoxMeasure, μ, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.zero_succAbove,
        cast_eq] using hfi
    symm
    calc
      _ = ∫ p : ℝ × (Fin n → ℝ), f (Fin.cons p.1 p.2) ∂ν.prod (cubeBoxMeasure a b n) := by
        change (∫ q, f q ∂Measure.pi μ) = _
        rw [← hp.integral_comp']
        simp [cubeBoxMeasure, μ, ν, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Equiv.coe_fn_mk, Fin.zero_succAbove]
      _ = ∫ q, ∫ t, f (Fin.cons t q) ∂ν ∂cubeBoxMeasure a b n :=
        integral_prod_symm _ hfi'
      _ = ∫ q, (∫ t in a..b, f (Fin.cons t q)) ∂cubeBoxMeasure a b n := by
        congr 1
        funext q
        change (∫ t in Icc a b, f (Fin.cons t q)) = _
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
      _ = cubeIntegral a b n (fun q => ∫ t in a..b, f (Fin.cons t q)) :=
        (ih _ (coordinate_mean_continuous a b hab n f hf)).symm
      _ = _ := rfl

private theorem restricted_volume_cube_neumann (a b : ℝ) (hab : a < b) (n : ℕ)
    (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) :
    let c := (∫ q in cubeBox a b n, f q)/(b-a)^n
    (∫ q in cubeBox a b n, (f q-c)^2) ≤
      cubePoincareConstant n*(b-a)^2*(∫ q in cubeBox a b n, cubeGradientSquare n f q) := by
  let c := (∫ q, f q ∂cubeBoxMeasure a b n)/(b-a)^n
  have hm : cubeMean a b n f = c := by
    exact congrArg (fun z => z/(b-a)^n)
      (cube_integral_product_measure_identity a b hab.le n f hf.continuous)
  have h := finite_dimension_cube_neumann a b hab n f hf
  rw [hm,cube_integral_product_measure_identity a b hab.le n (fun q => (f q-c)^2)
    ((hf.continuous.sub continuous_const).pow 2),
    cube_integral_product_measure_identity a b hab.le n (cubeGradientSquare n f)
      (cube_gradient_square_continuous n f hf)] at h
  dsimp [c] at h
  rw [cube_box_measure_restricted_volume] at h
  exact h




private def euclideanCubeBox (a b : ℝ) (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  WithLp.ofLp ⁻¹' cubeBox a b n

private theorem euclidean_cube_integral_transport (a b : ℝ) (n : ℕ)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ q in cubeBox a b n, F ((EuclideanSpace.equiv (Fin n) ℝ).symm q)) =
      ∫ x in euclideanCubeBox a b n, F x := by
  have hp := PiLp.volume_preserving_toLp (Fin n)
  have h := hp.setIntegral_preimage_emb
    (EuclideanSpace.equiv (Fin n) ℝ).symm.toHomeomorph.measurableEmbedding
    F (euclideanCubeBox a b n)
  have hset : (@WithLp.toLp 2 (Fin n → ℝ)) ⁻¹' euclideanCubeBox a b n = cubeBox a b n := by
    ext q
    rfl
  rw [hset] at h
  exact h

private theorem euclidean_cube_gradient_identity (n : ℕ)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ContDiff ℝ 1 F) (q : Fin n → ℝ) :
    cubeGradientSquare n (fun q => F ((EuclideanSpace.equiv (Fin n) ℝ).symm q)) q =
      ‖gradient F ((EuclideanSpace.equiv (Fin n) ℝ).symm q)‖^2 := by
  let e := (EuclideanSpace.equiv (Fin n) ℝ).symm
  rw [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  have hd := (hF.differentiable (by norm_num) (e q)).hasFDerivAt.comp q e.hasFDerivAt
  have hi : fderiv ℝ F (e q) (EuclideanSpace.single i 1) = gradient F (e q) i := by
    rw [← inner_gradient_left]
    rw [EuclideanSpace.inner_single_right]
    simp only [one_mul, RCLike.conj_to_real]
  change (fderiv ℝ (F ∘ e) q (Pi.single i 1))^2 = (gradient F (e q) i)^2
  rw [hd.fderiv]
  change (fderiv ℝ F (e q) (EuclideanSpace.single i 1))^2 = _
  rw [hi]

private theorem euclidean_cube_neumann (a b : ℝ) (hab : a < b) (n : ℕ)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ContDiff ℝ 1 F) :
    let c := (∫ x in euclideanCubeBox a b n, F x)/(b-a)^n
    (∫ x in euclideanCubeBox a b n, (F x-c)^2) ≤
      cubePoincareConstant n*(b-a)^2*(∫ x in euclideanCubeBox a b n, ‖gradient F x‖^2) := by
  let e := (EuclideanSpace.equiv (Fin n) ℝ).symm
  have h := restricted_volume_cube_neumann a b hab n
    (fun q => F ((EuclideanSpace.equiv (Fin n) ℝ).symm q))
    (hF.comp (EuclideanSpace.equiv (Fin n) ℝ).symm.contDiff)
  simp_rw [euclidean_cube_gradient_identity n F hF] at h
  rw [euclidean_cube_integral_transport a b n F] at h
  let c := (∫ x in euclideanCubeBox a b n, F x)/(b-a)^n
  change (∫ q in cubeBox a b n, (F (e q)-c)^2) ≤ _ at h
  rw [euclidean_cube_integral_transport a b n (fun x => (F x-c)^2),
    euclidean_cube_integral_transport a b n (fun x => ‖gradient F x‖^2)] at h
  exact h


end EuclideanCubeNeumann

-- [TABLET NODE: EuclideanCubeNeumann]
theorem EuclideanCubeNeumann (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b : ℝ), a < b →
      ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ), ContDiff ℝ 1 f →
      let Q := {x : EuclideanSpace ℝ (Fin n) | ∀ i, a ≤ x i ∧ x i ≤ b}
      let m := (∫ x in Q, f x) / (b - a)^n
      (∫ x in Q, (f x - m)^2) ≤
        C * (b - a)^2 * (∫ x in Q, ‖EuclideanGradient f x‖^2) := by
-- BODY
  refine ⟨EuclideanCubeNeumann.cubePoincareConstant n,
    EuclideanCubeNeumann.cube_poincare_constant_positive n, ?_⟩
  intro a b hab f hf
  have h := EuclideanCubeNeumann.euclidean_cube_neumann a b hab n f hf
  have hQ : EuclideanCubeNeumann.euclideanCubeBox a b n =
      {x : EuclideanSpace ℝ (Fin n) | ∀ i, a ≤ x i ∧ x i ≤ b} := by
    ext x
    simp [EuclideanCubeNeumann.euclideanCubeBox, EuclideanCubeNeumann.cubeBox,
      Set.mem_Icc, Pi.le_def, forall_and]
  simpa only [hQ, EuclideanGradient] using h
