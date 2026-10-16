module

public import Tablet.AtomicLocalRieszBounds
public import Tablet.AtomicInteractionSource
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic

@[expose] public section
set_option maxHeartbeats 1600000
open MeasureTheory Measure Set Metric Function
open scoped ContDiff NNReal
noncomputable section
namespace AtomicLocalCutoffEnergy
private def scalarBump : ContDiffBump (0 : ℝ) :=
  { rIn := 1, rOut := 2, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }


private theorem scalar_bump_smooth : ContDiff ℝ ∞ (scalarBump : ℝ → ℝ) := scalarBump.contDiff


private theorem scalar_bump_one (x : ℝ) (hx : |x| ≤ 1) : scalarBump x = 1 := by
  apply scalarBump.one_of_mem_closedBall
  simpa [scalarBump,Real.dist_eq] using hx


private theorem scalar_bump_zero (x : ℝ) (hx : 2 ≤ |x|) : scalarBump x = 0 := by
  apply scalarBump.zero_of_le_dist
  simpa [scalarBump,Real.dist_eq] using hx


private theorem scalar_bump_derivative_bound : ∃ C : ℝ, 0 < C ∧ ∀ x, |deriv scalarBump x| ≤ C := by
  have hs : HasCompactSupport (scalarBump : ℝ → ℝ) := scalarBump.hasCompactSupport
  obtain ⟨C,hC⟩ := (scalar_bump_smooth.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).continuous_deriv_one
    |>.bounded_above_of_compact_support hs.deriv
  refine ⟨max 1 C,by positivity,?_⟩
  intro x
  exact (show |deriv scalarBump x| ≤ C by simpa using hC x).trans (le_max_right _ _)


private def smoothPotentialCutoff (T x : ℝ) : ℝ := scalarBump (x/T)


private theorem smooth_potential_cutoff_smooth (T : ℝ) : ContDiff ℝ ∞ (smoothPotentialCutoff T) :=
  scalar_bump_smooth.comp (contDiff_id.div_const T)


private theorem smooth_potential_cutoff_range (T x : ℝ) :
    0 ≤ smoothPotentialCutoff T x ∧ smoothPotentialCutoff T x ≤ 1 :=
  ⟨scalarBump.nonneg,scalarBump.le_one⟩


private theorem smooth_potential_cutoff_error (T x : ℝ) (hT : 0 < T) (hx : 0 ≤ x) :
    (1-smoothPotentialCutoff T x)^2 ≤ x/T := by
  by_cases hsmall : x ≤ T
  · have hr : |x/T| ≤ 1 := by
      rw [abs_of_nonneg (div_nonneg hx hT.le)]
      exact (div_le_one hT).mpr hsmall
    rw [smoothPotentialCutoff,scalar_bump_one _ hr]
    simpa using div_nonneg hx hT.le
  · have hr := smooth_potential_cutoff_range T x
    have hsq : (1-smoothPotentialCutoff T x)^2 ≤ 1 := by nlinarith
    exact hsq.trans ((le_div_iff₀ hT).mpr (by simpa using (lt_of_not_ge hsmall).le))


private theorem smooth_potential_cutoff_deriv (T x : ℝ) :
    deriv (smoothPotentialCutoff T) x = deriv scalarBump (x/T)/T := by
  have h := (scalar_bump_smooth.differentiable (by simp) (x/T)).hasDerivAt.comp x
    ((hasDerivAt_id x).div_const T)
  have heq : ((scalarBump : ℝ → ℝ) ∘ fun u => id u/T) = smoothPotentialCutoff T := rfl
  rw [heq] at h
  simpa [div_eq_mul_inv] using h.deriv


private theorem smooth_potential_cutoff_derivative_bound (C : ℝ) (_hC : 0 < C)
    (hd : ∀ x, |deriv scalarBump x| ≤ C) (T x : ℝ) (hT : 0 < T) :
    |deriv (smoothPotentialCutoff T) x| ≤ C/T := by
  rw [smooth_potential_cutoff_deriv,abs_div,abs_of_pos hT]
  exact div_le_div_of_nonneg_right (hd _) hT.le


private theorem gradient_norm_eq_fderiv_norm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (F : E → ℝ) (x : E) :
    ‖gradient F x‖ = ‖fderiv ℝ F x‖ :=
  (InnerProductSpace.toDual ℝ E).symm.norm_map _


private def cutoffPrimitive (T x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, (deriv (smoothPotentialCutoff T) t)^2


private theorem cutoff_primitive_deriv (T x : ℝ) :
    deriv (cutoffPrimitive T) x = (deriv (smoothPotentialCutoff T) x)^2 := by
  have hc : Continuous (fun x => (deriv (smoothPotentialCutoff T) x)^2) :=
    ((smooth_potential_cutoff_smooth T).of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).continuous_deriv_one.pow 2
  exact (hc.integral_hasStrictDerivAt 0 x).hasDerivAt.deriv


private theorem cutoff_primitive_C1 (T : ℝ) : ContDiff ℝ 1 (cutoffPrimitive T) := by
  have hc : Continuous (fun x => (deriv (smoothPotentialCutoff T) x)^2) :=
    ((smooth_potential_cutoff_smooth T).of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).continuous_deriv_one.pow 2
  refine contDiff_one_iff_deriv.mpr ⟨fun x => (hc.integral_hasStrictDerivAt 0 x).hasDerivAt.differentiableAt,?_⟩
  have heq : deriv (cutoffPrimitive T) = (fun x => (deriv (smoothPotentialCutoff T) x)^2) :=
    funext (cutoff_primitive_deriv T)
  rw [heq]
  exact hc


private theorem smooth_potential_cutoff_derivative_zero (T x : ℝ) (hT : 0 < T) (hx : 2*T < x) :
    deriv (smoothPotentialCutoff T) x = 0 := by
  have hratio : 2 < x/T := (lt_div_iff₀ hT).mpr hx
  have hn : x/T ∉ tsupport (scalarBump : ℝ → ℝ) := by
    rw [scalarBump.tsupport_eq]
    simp only [Metric.mem_closedBall,Real.dist_eq,sub_zero,scalarBump]
    exact not_le.mpr (hratio.trans_le (le_abs_self _))
  rw [smooth_potential_cutoff_deriv,deriv_of_notMem_tsupport hn,zero_div]


private theorem cutoff_primitive_bound (C : ℝ) (hC : 0 < C) (hd : ∀ x, |deriv scalarBump x| ≤ C)
    (T x : ℝ) (hT : 0 < T) (hx : 0 ≤ x) :
    0 ≤ cutoffPrimitive T x ∧ cutoffPrimitive T x ≤ 2*C^2/T := by
  have hc : Continuous (fun x => (deriv (smoothPotentialCutoff T) x)^2) :=
    ((smooth_potential_cutoff_smooth T).of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).continuous_deriv_one.pow 2
  have hsmall (y : ℝ) (hy : 0 ≤ y) (hy2 : y ≤ 2*T) : cutoffPrimitive T y ≤ 2*C^2/T := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hy
      (hc.intervalIntegrable 0 y) (continuous_const.intervalIntegrable 0 y) (fun t _ => by
        simpa [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (div_nonneg hC.le hT.le)).mpr
          (smooth_potential_cutoff_derivative_bound C hC hd T t hT))
    rw [intervalIntegral.integral_const] at h
    simp only [sub_zero,smul_eq_mul] at h
    refine h.trans ((mul_le_mul_of_nonneg_right hy2 (sq_nonneg _)).trans_eq ?_)
    field_simp
  refine ⟨intervalIntegral.integral_nonneg hx (fun _ _ => sq_nonneg _),?_⟩
  by_cases hx2 : x ≤ 2*T
  · exact hsmall x hx hx2
  · have hzero : (∫ t in (2*T)..x, (deriv (smoothPotentialCutoff T) t)^2) = 0 := by
      rw [intervalIntegral.integral_of_le (le_of_not_ge hx2)]
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro t ht
      rw [smooth_potential_cutoff_derivative_zero T t hT ht.1,zero_pow (by decide : 2 ≠ 0)]
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hc.intervalIntegrable 0 (2*T)) (hc.intervalIntegrable (2*T) x)
    change (∫ t in (0 : ℝ)..x, (deriv (smoothPotentialCutoff T) t)^2) ≤ _
    rw [← hadd,hzero,add_zero]
    exact hsmall (2*T) (by positivity) le_rfl



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι]
  [CompleteSpace E]
variable (μ : Measure E) [IsAddHaarMeasure μ]
private def D (u : E → ℝ) (v : E) (x : E) : ℝ := fderiv ℝ u x v


private theorem continuous_D {u : E → ℝ} (hu : ContDiff ℝ 1 u) (v : E) :
    Continuous (D u v) := by
  exact (hu.continuous_fderiv_apply (by norm_num)).comp
    (continuous_id.prodMk continuous_const)


private theorem contDiff_D {u : E → ℝ} (hu : ContDiff ℝ 2 u) (v : E) :
    ContDiff ℝ 1 (D u v) := by
  exact (hu.contDiff_fderiv_apply (m := 1) (by norm_num)).comp
    (contDiff_id.prodMk contDiff_const)


private theorem compact_D {u : E → ℝ} (hu : HasCompactSupport u) (v : E) :
    HasCompactSupport (D u v) := by
  exact hu.fderiv_apply ℝ v


private theorem integrable_product_compact (a b : E → ℝ) (ha : Continuous a)
    (hb : Continuous b) (hcb : HasCompactSupport b) :
    Integrable (fun x => a x * b x) μ := by
  exact (ha.mul hb).integrable_of_hasCompactSupport hcb.mul_left


private theorem sum_D_sq_eq_gradient_norm (b : OrthonormalBasis ι ℝ E) (u : E → ℝ) (x : E) :
    ∑ i, (D u (b i) x)^2 = ‖gradient u x‖^2 := by
  have hi (i : ι) : D u (b i) x = inner ℝ (gradient u x) (b i) := by
    dsimp [D]
    have h := congrArg (fun L : E →L[ℝ] ℝ => L (b i))
      (toDual_gradient (𝕜 := ℝ) (f := u) (x := x))
    simpa [InnerProductSpace.toDual_apply_apply] using h.symm
  calc
    _ = ∑ i, ‖inner ℝ (gradient u x) (b i)‖^2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hi, Real.norm_eq_abs, sq_abs]
    _ = _ := b.sum_sq_norm_inner_left (gradient u x)


private def basisLaplacian (b : OrthonormalBasis ι ℝ E) (H : E → ℝ) (x : E) : ℝ :=
  ∑ i, D (D H (b i)) (b i) x

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem D_mul (f g : E → ℝ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (v x : E) :
    D (fun x => f x*g x) v x = D f v x*g x+f x*D g v x := by
  have h := (hf.differentiable (by norm_num) x).hasFDerivAt.mul
    (hg.differentiable (by norm_num) x).hasFDerivAt
  have heq := congrArg (fun L : E →L[ℝ] ℝ => L v) h.fderiv
  change fderiv ℝ (fun x => f x*g x) x v = _ at heq
  simpa [D,_root_.add_apply,_root_.smul_apply,smul_eq_mul,mul_comm,add_comm] using heq

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem D_comp_scalar (U : E → ℝ) (hU : ContDiff ℝ 1 U) (Φ : ℝ → ℝ)
    (hΦ : ContDiff ℝ 1 Φ) (v x : E) :
    D (fun x => Φ (U x)) v x = deriv Φ (U x)*D U v x := by
  have h := (hΦ.differentiable (by norm_num) (U x)).hasDerivAt.comp_hasFDerivAt x
    (hU.differentiable (by norm_num) x).hasFDerivAt
  have heq := congrArg (fun L : E →L[ℝ] ℝ => L v) h.fderiv
  simpa [D,Function.comp_def,_root_.smul_apply,smul_eq_mul] using heq

omit [MeasurableSpace E] [BorelSpace E] in
private theorem sum_D_mul_eq_inner (b : OrthonormalBasis ι ℝ E) (f g : E → ℝ) (x : E) :
    (∑ i, D f (b i) x*D g (b i) x) = inner ℝ (gradient f x) (gradient g x) := by
  have hd (u : E → ℝ) (i : ι) : D u (b i) x = inner ℝ (gradient u x) (b i) := by
    dsimp [D]
    exact (inner_gradient_left (𝕜 := ℝ) (f := u) (x := x) (y := b i)).symm
  simp_rw [hd]
  have h := b.sum_inner_mul_inner (gradient f x) (gradient g x)
  simpa only [real_inner_comm] using h

private theorem compact_green_identity (μ : Measure E) [IsAddHaarMeasure μ]
    (b : OrthonormalBasis ι ℝ E) (U w : E → ℝ)
    (hU : ContDiff ℝ 2 U) (hw : ContDiff ℝ 1 w) (hcw : HasCompactSupport w) :
    (∫ x, inner ℝ (gradient U x) (gradient w x) ∂μ) =
      -(∫ x, basisLaplacian b U x*w x ∂μ) := by
  have hUw (i : ι) : Integrable (fun x => D U (b i) x*D w (b i) x) μ :=
    integrable_product_compact μ _ _ (continuous_D (hU.of_le (by norm_num)) _)
      (continuous_D hw _) (compact_D hcw _)
  have hDDw (i : ι) : Integrable (fun x => D (D U (b i)) (b i) x*w x) μ :=
    integrable_product_compact μ _ _ (continuous_D (contDiff_D hU _) _)
      hw.continuous hcw
  have hi (i : ι) : (∫ x, D U (b i) x*D w (b i) x ∂μ) =
      -(∫ x, D (D U (b i)) (b i) x*w x ∂μ) := by
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := μ) (f := D U (b i)) (g := w) (v := b i)
      (hDDw i) (hUw i)
      (integrable_product_compact μ _ _ (continuous_D (hU.of_le (by norm_num)) _) hw.continuous hcw)
      (fun x _ => (contDiff_D hU _).differentiable (by norm_num) x)
      (fun x _ => hw.differentiable (by norm_num) x)
  calc
    _ = ∫ x, ∑ i, D U (b i) x*D w (b i) x ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => (sum_D_mul_eq_inner b U w x).symm)
    _ = ∑ i, ∫ x, D U (b i) x*D w (b i) x ∂μ := integral_finsetSum _ (fun i _ => hUw i)
    _ = -(∑ i, ∫ x, D (D U (b i)) (b i) x*w x ∂μ) := by simp_rw [hi]; rw [Finset.sum_neg_distrib]
    _ = -(∫ x, ∑ i, D (D U (b i)) (b i) x*w x ∂μ) := by rw [integral_finsetSum _ (fun i _ => hDDw i)]
    _ = _ := by simp only [basisLaplacian,Finset.sum_mul]

omit [MeasurableSpace E] [BorelSpace E] in
private theorem continuous_gradient_C1 (U : E → ℝ) (hU : ContDiff ℝ 1 U) : Continuous (gradient U) :=
  (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hU.continuous_fderiv (by norm_num))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem D_pow_two (ζ : E → ℝ) (hζ : ContDiff ℝ 1 ζ) (v x : E) :
    D (fun x => ζ x^2) v x = 2*ζ x*D ζ v x := by
  have h := D_mul ζ ζ hζ hζ v x
  simpa only [pow_two] using h.trans (by ring)

private theorem compact_source_primitive_identity (μ : Measure E) [IsAddHaarMeasure μ]
    (b : OrthonormalBasis ι ℝ E) (U ζ : E → ℝ) (hU : ContDiff ℝ 2 U)
    (hζ : ContDiff ℝ 1 ζ) (hcζ : HasCompactSupport ζ) (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ 1 Φ) :
    (∫ x, ζ x^2*deriv Φ (U x)*‖gradient U x‖^2 ∂μ) =
      (∫ x, ζ x^2*Φ (U x)*(-basisLaplacian b U x) ∂μ) -
        2*(∫ x, ζ x*Φ (U x)*inner ℝ (gradient U x) (gradient ζ x) ∂μ) := by
  let w := fun x => ζ x^2*Φ (U x)
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by norm_num)
  have hw : ContDiff ℝ 1 w := (hζ.pow 2).mul (hΦ.comp hU1)
  have hcζ2 : HasCompactSupport (fun x => ζ x^2) := by
    simpa only [Function.comp_def] using hcζ.comp_left (g := fun z : ℝ => z^2) (by simp)
  have hcw : HasCompactSupport w := hcζ2.mul_right
  have hdw (i : ι) (x : E) : D w (b i) x =
      2*ζ x*D ζ (b i) x*Φ (U x)+ζ x^2*deriv Φ (U x)*D U (b i) x := by
    rw [D_mul (fun x => ζ x^2) (fun x => Φ (U x)) (hζ.pow 2) (hΦ.comp hU1),
      D_pow_two ζ hζ,D_comp_scalar U hU1 Φ hΦ]
    ring
  have hinner (x : E) : inner ℝ (gradient U x) (gradient w x) =
      2*ζ x*Φ (U x)*inner ℝ (gradient U x) (gradient ζ x)+
        ζ x^2*deriv Φ (U x)*‖gradient U x‖^2 := by
    rw [← sum_D_mul_eq_inner b U w x]
    have heq (i : ι) : D U (b i) x*D w (b i) x =
        (2*ζ x*Φ (U x))*(D U (b i) x*D ζ (b i) x)+
          (ζ x^2*deriv Φ (U x))*(D U (b i) x)^2 := by rw [hdw]; ring
    simp_rw [heq]
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,
      sum_D_mul_eq_inner b U ζ x,sum_D_sq_eq_gradient_norm b U x]
  have hgU := continuous_gradient_C1 U hU1
  have hgζ := continuous_gradient_C1 ζ hζ
  have hcros : Integrable (fun x => ζ x*Φ (U x)*inner ℝ (gradient U x) (gradient ζ x)) μ := by
    have hf : Continuous (fun x => Φ (U x)*inner ℝ (gradient U x) (gradient ζ x)) :=
      (hΦ.continuous.comp hU.continuous).mul (hgU.inner hgζ)
    convert integrable_product_compact μ _ _ hf hζ.continuous hcζ using 1
    funext x
    ring
  have henergy : Integrable (fun x => ζ x^2*deriv Φ (U x)*‖gradient U x‖^2) μ := by
    have hf : Continuous (fun x => deriv Φ (U x)*‖gradient U x‖^2) :=
      (hΦ.continuous_deriv_one.comp hU.continuous).mul (hgU.norm.pow 2)
    convert integrable_product_compact μ (fun x => deriv Φ (U x)*‖gradient U x‖^2)
      (fun x => ζ x^2) hf (hζ.continuous.pow 2) hcζ2 using 1
    funext x
    ring
  have h := compact_green_identity μ b U w hU hw hcw
  have heq : (fun x => inner ℝ (gradient U x) (gradient w x)) =
      (fun x => 2*(ζ x*Φ (U x)*inner ℝ (gradient U x) (gradient ζ x))+
        ζ x^2*deriv Φ (U x)*‖gradient U x‖^2) := by
    funext x
    rw [hinner]
    ring
  have hsource : -(∫ x, basisLaplacian b U x*w x ∂μ) =
      ∫ x, ζ x^2*Φ (U x)*(-basisLaplacian b U x) ∂μ := by
    rw [← integral_neg]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by dsimp [w]; ring)
  rw [heq,integral_add (hcros.const_mul 2) henergy,integral_const_mul,hsource] at h
  linarith

omit [MeasurableSpace E] [BorelSpace E] in
private theorem gradient_scalar_comp_norm_sq (U : E → ℝ) (hU : ContDiff ℝ 1 U)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 1 χ) (x : E) :
    ‖gradient (fun y => χ (U y)) x‖^2 = (deriv χ (U x))^2*‖gradient U x‖^2 := by
  have h := (hχ.differentiable (by norm_num) (U x)).hasDerivAt.comp_hasFDerivAt x
    (hU.differentiable (by norm_num) x).hasFDerivAt
  rw [gradient_norm_eq_fderiv_norm,gradient_norm_eq_fderiv_norm]
  change ‖fderiv ℝ (χ ∘ U) x‖^2 = _
  rw [h.fderiv,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]

private theorem compact_potential_cutoff_source_identity (μ : Measure E) [IsAddHaarMeasure μ]
    (b : OrthonormalBasis ι ℝ E) (U ζ : E → ℝ) (hU : ContDiff ℝ 2 U)
    (hζ : ContDiff ℝ 1 ζ) (hcζ : HasCompactSupport ζ) (T : ℝ) :
    (∫ x, ζ x^2*‖gradient (fun y => smoothPotentialCutoff T (U y)) x‖^2 ∂μ) =
      (∫ x, ζ x^2*cutoffPrimitive T (U x)*(-basisLaplacian b U x) ∂μ) -
        2*(∫ x, ζ x*cutoffPrimitive T (U x)*inner ℝ (gradient U x) (gradient ζ x) ∂μ) := by
  have h := compact_source_primitive_identity μ b U ζ hU hζ hcζ
    (cutoffPrimitive T) (cutoff_primitive_C1 T)
  simp_rw [cutoff_primitive_deriv] at h
  have heq : (fun x => ζ x^2*‖gradient (fun y => smoothPotentialCutoff T (U y)) x‖^2) =
      (fun x => ζ x^2*(deriv (smoothPotentialCutoff T) (U x))^2*‖gradient U x‖^2) := by
    funext x
    rw [gradient_scalar_comp_norm_sq U (hU.of_le (by norm_num)) _
      ((smooth_potential_cutoff_smooth T).of_le (by simp : (1 : ℕ∞ω) ≤ ∞))]
    ring
  rw [heq]
  exact h

private theorem source_cutoff_scalar_upper (z φ a s c Z r : ℝ)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hφ0 : 0 ≤ φ) (hφa : φ ≤ a)
    (hs : 0 ≤ s) (hZ : 0 ≤ Z) (hr : 0 ≤ r) (hc : |c| ≤ Z*r) :
    z^2*φ*s-2*z*φ*c ≤ a*(s+2*Z*r) := by
  have hz2 : z^2 ≤ 1 := by nlinarith
  have hzφ : z*φ ≤ a := (mul_le_of_le_one_left hφ0 hz1).trans hφa
  have hz2φ : z^2*φ ≤ a := (mul_le_of_le_one_left hφ0 hz2).trans hφa
  have hcLow : -(Z*r) ≤ c := (neg_le_neg hc).trans (neg_abs_le c)
  have hw := mul_le_mul_of_nonneg_left hcLow (show 0 ≤ 2*z*φ by positivity)
  have hFirst := mul_le_mul_of_nonneg_right hz2φ hs
  have hSecond := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzφ
    (show (0 : ℝ) ≤ 2 by norm_num)) (mul_nonneg hZ hr)
  have hcErr : -2*z*φ*c ≤ 2*z*φ*(Z*r) := by nlinarith [hw]
  calc
    _ ≤ z^2*φ*s+(2*z*φ)*(Z*r) := by linarith
    _ ≤ a*s+(2*a)*(Z*r) := by simpa only [mul_assoc] using add_le_add hFirst hSecond
    _ = _ := by ring

private theorem compact_potential_cutoff_energy_integrable (μ : Measure E) [IsAddHaarMeasure μ]
    (U ζ : E → ℝ) (hU : ContDiff ℝ 1 U) (hζ : ContDiff ℝ 1 ζ)
    (hcζ : HasCompactSupport ζ) (T : ℝ) :
    Integrable (fun x => ζ x^2*‖gradient (fun y => smoothPotentialCutoff T (U y)) x‖^2) μ := by
  have hcζ2 : HasCompactSupport (fun x => ζ x^2) := by
    simpa only [Function.comp_def] using hcζ.comp_left (g := fun z : ℝ => z^2) (by simp)
  have hg : Continuous (gradient (fun y => smoothPotentialCutoff T (U y))) :=
    continuous_gradient_C1 _ (((smooth_potential_cutoff_smooth T).of_le
      (by simp : (1 : ℕ∞ω) ≤ ∞)).comp hU)
  have h := integrable_product_compact μ (fun x => ‖gradient (fun y => smoothPotentialCutoff T (U y)) x‖^2)
    (fun x => ζ x^2) (hg.norm.pow 2) (hζ.continuous.pow 2) hcζ2
  convert h using 1
  funext x
  ring

private theorem compact_source_cutoff_energy_bound (μ : Measure E) [IsAddHaarMeasure μ]
    (b : OrthonormalBasis ι ℝ E) (U ζ : E → ℝ) (hU : ContDiff ℝ 2 U)
    (hUn : ∀ x, 0 ≤ U x) (hSource : ∀ x, 0 ≤ -basisLaplacian b U x)
    (hζ : ContDiff ℝ 1 ζ) (hcζ : HasCompactSupport ζ)
    (hζrange : ∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1)
    (K : Set E) (hK : MeasurableSet K) (hSupp : support ζ ⊆ K)
    (hSi : IntegrableOn (fun x => -basisLaplacian b U x) K μ)
    (hFi : IntegrableOn (fun x => ‖gradient U x‖) K μ)
    (Z C T : ℝ) (hZ : 0 ≤ Z) (hC : 0 < C) (hT : 0 < T)
    (hGradζ : ∀ x, ‖gradient ζ x‖ ≤ Z) (hd : ∀ x, |deriv scalarBump x| ≤ C) :
    (∫ x, ζ x^2*‖gradient (fun y => smoothPotentialCutoff T (U y)) x‖^2 ∂μ) ≤
      (2*C^2/T)*((∫ x in K, -basisLaplacian b U x ∂μ)+2*Z*(∫ x in K, ‖gradient U x‖ ∂μ)) := by
  let Φ := cutoffPrimitive T
  let A := 2*C^2/T
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by norm_num)
  have hΦ : ContDiff ℝ 1 Φ := cutoff_primitive_C1 T
  have hgU := continuous_gradient_C1 U hU1
  have hgζ := continuous_gradient_C1 ζ hζ
  have hLap : Continuous (basisLaplacian b U) := by
    exact continuous_finsetSum _ (fun i _ => continuous_D (contDiff_D hU _) _)
  have hcζ2 : HasCompactSupport (fun x => ζ x^2) := by
    simpa only [Function.comp_def] using hcζ.comp_left (g := fun z : ℝ => z^2) (by simp)
  have hiS : Integrable (fun x => ζ x^2*Φ (U x)*(-basisLaplacian b U x)) μ := by
    have hc : Continuous (fun x => Φ (U x)*(-basisLaplacian b U x)) :=
      (hΦ.continuous.comp hU.continuous).mul hLap.neg
    convert integrable_product_compact μ _ (fun x => ζ x^2) hc (hζ.continuous.pow 2) hcζ2 using 1
    funext x
    ring
  have hiC : Integrable (fun x => ζ x*Φ (U x)*inner ℝ (gradient U x) (gradient ζ x)) μ := by
    have hc : Continuous (fun x => Φ (U x)*inner ℝ (gradient U x) (gradient ζ x)) :=
      (hΦ.continuous.comp hU.continuous).mul (hgU.inner hgζ)
    convert integrable_product_compact μ _ _ hc hζ.continuous hcζ using 1
    funext x
    ring
  have hiL := hiS.sub (hiC.const_mul 2)
  have hiR : Integrable
      (fun x => A*K.indicator (fun x => -basisLaplacian b U x+2*Z*‖gradient U x‖) x) μ :=
    ((integrable_indicator_iff hK).mpr (hSi.add (hFi.const_mul (2*Z)))).const_mul A
  have hpoint (x : E) :
      ζ x^2*Φ (U x)*(-basisLaplacian b U x)-2*(ζ x*Φ (U x)*inner ℝ (gradient U x) (gradient ζ x)) ≤
        A*K.indicator (fun x => -basisLaplacian b U x+2*Z*‖gradient U x‖) x := by
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
      have hφ := cutoff_primitive_bound C hC hd T (U x) hT (hUn x)
      have hinner : |inner ℝ (gradient U x) (gradient ζ x)| ≤ Z*‖gradient U x‖ := by
        calc
          _ ≤ ‖gradient U x‖*‖gradient ζ x‖ := abs_real_inner_le_norm _ _
          _ ≤ ‖gradient U x‖*Z := mul_le_mul_of_nonneg_left (hGradζ x) (norm_nonneg _)
          _ = _ := mul_comm _ _
      have h := source_cutoff_scalar_upper (ζ x) (Φ (U x)) A (-basisLaplacian b U x)
        (inner ℝ (gradient U x) (gradient ζ x)) Z ‖gradient U x‖
        (hζrange x).1 (hζrange x).2 hφ.1 hφ.2 (hSource x) hZ (norm_nonneg _) hinner
      simpa only [mul_assoc] using h
    · have hz : ζ x = 0 := notMem_support.mp (fun hs => hx (hSupp hs))
      rw [hz,Set.indicator_of_notMem hx]
      simp
  have h := integral_mono hiL hiR hpoint
  change (∫ x, ζ x^2*Φ (U x)*(-basisLaplacian b U x)-
      2*(ζ x*Φ (U x)*inner ℝ (gradient U x) (gradient ζ x)) ∂μ) ≤ _ at h
  rw [integral_sub (f := fun x => ζ x^2*Φ (U x)*(-basisLaplacian b U x))
      (g := fun x => 2*(ζ x*Φ (U x)*inner ℝ (gradient U x) (gradient ζ x))) hiS (hiC.const_mul 2),
    integral_const_mul,integral_const_mul,integral_indicator hK,
    integral_add (f := fun x => -basisLaplacian b U x) (g := fun x => 2*Z*‖gradient U x‖)
      hSi (hFi.const_mul (2*Z)),integral_const_mul] at h
  exact (compact_potential_cutoff_source_identity μ b U ζ hU hζ hcζ T).trans_le h


private theorem inner_source_cutoff_energy_bound (μ : Measure E) [IsAddHaarMeasure μ]
    (b : OrthonormalBasis ι ℝ E) (U ζ : E → ℝ) (hU : ContDiff ℝ 2 U)
    (hUn : ∀ x, 0 ≤ U x) (hSource : ∀ x, 0 ≤ -basisLaplacian b U x)
    (hζ : ContDiff ℝ 1 ζ) (hcζ : HasCompactSupport ζ)
    (hζrange : ∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1)
    (K S : Set E) (hK : MeasurableSet K) (hS : MeasurableSet S)
    (hSupp : support ζ ⊆ K) (hOne : ∀ x ∈ S, ζ x = 1)
    (hSi : IntegrableOn (fun x => -basisLaplacian b U x) K μ)
    (hFi : IntegrableOn (fun x => ‖gradient U x‖) K μ)
    (Z C T : ℝ) (hZ : 0 ≤ Z) (hC : 0 < C) (hT : 0 < T)
    (hGradζ : ∀ x, ‖gradient ζ x‖ ≤ Z) (hd : ∀ x, |deriv scalarBump x| ≤ C) :
    (∫ x in S, ‖gradient (fun y => smoothPotentialCutoff T (U y)) x‖^2 ∂μ) ≤
      (2*C^2/T)*((∫ x in K, -basisLaplacian b U x ∂μ)+2*Z*(∫ x in K, ‖gradient U x‖ ∂μ)) := by
  have hi := compact_potential_cutoff_energy_integrable μ U ζ (hU.of_le (by norm_num)) hζ hcζ T
  have heq : (∫ x in S, ‖gradient (fun y => smoothPotentialCutoff T (U y)) x‖^2 ∂μ) =
      ∫ x in S, ζ x^2*‖gradient (fun y => smoothPotentialCutoff T (U y)) x‖^2 ∂μ := by
    apply setIntegral_congr_fun hS
    intro x hx
    dsimp only
    rw [hOne x hx]; simp
  rw [heq]
  exact (setIntegral_le_integral hi (Filter.Eventually.of_forall (fun x => by positivity))).trans
    (compact_source_cutoff_energy_bound μ b U ζ hU hUn hSource hζ hcζ hζrange K hK hSupp
      hSi hFi Z C T hZ hC hT hGradζ hd)


private theorem basis_eq_actual {d : ℕ} (U : OneParticle d → ℝ)
    (hU : ContDiff ℝ 2 U) (x : OneParticle d) :
    basisLaplacian (EuclideanSpace.basisFun (Fin d) ℝ) U x =
      EuclideanLaplacian U x := by
  rw [(EuclideanDerivativeCoordinates U x).2]
  apply Finset.sum_congr rfl
  intro k hk
  dsimp [D, basisLaplacian, EuclideanHessian]
  change (fderiv ℝ (fun z => fderiv ℝ U z ((EuclideanSpace.basisFun (Fin d) ℝ) k)) x)
    ((EuclideanSpace.basisFun (Fin d) ℝ) k) = _
  have hU' : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) U := by
    convert hU using 1 <;> norm_num
  have hfd := (contDiff_succ_iff_fderiv.mp hU').2.2
  rw [fderiv_clm_apply ((hfd.differentiable (by norm_num)) x)
    (differentiableAt_const _)]
  simp

private def cubeSet (d : ℕ) (R : ℝ) : Set (OneParticle d) :=
  {x | ∀ i, -R ≤ x i ∧ x i ≤ R}

private theorem cube_norm_bound (d : ℕ) (R : ℝ) (hR : 0 < R)
    (x : OneParticle d) (hx : x ∈ cubeSet d R) : ‖x‖ ≤ (d : ℝ)*R+1 := by
  have hs : ‖x‖^2 ≤ (d : ℝ)*R^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ i : Fin d, R^2 := Finset.sum_le_sum (fun i hi => by
        have h := hx i
        nlinarith [sq_nonneg (x i+R), sq_nonneg (x i-R)])
      _ = _ := by simp
  have hd : (d : ℝ) ≤ (d : ℝ)^2 := by
    simpa [pow_two] using
      (show (d : ℝ) ≤ (d : ℝ)*(d : ℝ) by exact_mod_cast Nat.le_mul_self d)
  have hh := mul_le_mul_of_nonneg_right hd (sq_nonneg R)
  have hn : ‖x‖ ≤ (d : ℝ)*R :=
    (sq_le_sq₀ (norm_nonneg x) (by positivity)).mp (by
      simpa [mul_pow] using hs.trans hh)
  linarith

private noncomputable def cubeSpatialBump (d : ℕ) (R : ℝ) (hR : 0 < R) :
    ContDiffBump (0 : OneParticle d) :=
  ⟨(d : ℝ)*R+1, 2*((d : ℝ)*R+1), by positivity,
    by nlinarith [Nat.cast_nonneg (α := ℝ) d]⟩

private theorem cubeSpatialBump_properties (d : ℕ) (R : ℝ) (hR : 0 < R) :
    let ζ : OneParticle d → ℝ := cubeSpatialBump d R hR
    let K := closedBall (0 : OneParticle d) (2*((d : ℝ)*R+1))
    ContDiff ℝ ∞ ζ ∧ HasCompactSupport ζ ∧
    (∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) ∧ support ζ ⊆ K ∧
    (∀ x ∈ cubeSet d R, ζ x = 1) ∧
    ∃ Z : ℝ, 0 ≤ Z ∧ ∀ x, ‖gradient ζ x‖ ≤ Z := by
  let ζ : OneParticle d → ℝ := cubeSpatialBump d R hR
  have hs : ContDiff ℝ ∞ ζ := (cubeSpatialBump d R hR).contDiff
  have hc : HasCompactSupport ζ := (cubeSpatialBump d R hR).hasCompactSupport
  refine ⟨hs, hc, (fun x => ⟨(cubeSpatialBump d R hR).nonneg,
    (cubeSpatialBump d R hR).le_one⟩), ?_, ?_, ?_⟩
  · rw [(cubeSpatialBump d R hR).support_eq]
    exact ball_subset_closedBall
  · intro x hx
    apply (cubeSpatialBump d R hR).one_of_mem_closedBall
    simpa [cubeSpatialBump, mem_closedBall, dist_zero_right] using cube_norm_bound d R hR x hx
  · have hgf : HasCompactSupport (fun x => ‖fderiv ℝ ζ x‖) :=
      (hc.fderiv ℝ).comp_left (g := fun L => ‖L‖) (by simp)
    obtain ⟨Z, hZ⟩ := hgf.exists_bound_of_continuous ((hs.continuous_fderiv (by simp)).norm)
    have hz : 0 ≤ Z := by simpa using (norm_nonneg (‖fderiv ℝ ζ 0‖)).trans (hZ 0)
    refine ⟨Z, hz, ?_⟩
    intro x
    rw [gradient_norm_eq_fderiv_norm]
    simpa using hZ x

end AtomicLocalCutoffEnergy

open AtomicLocalCutoffEnergy

-- [TABLET NODE: AtomicLocalCutoffEnergy]
theorem AtomicLocalCutoffEnergy (d : ℕ) (hd : 3 ≤ d) (s A : ℝ)
    (hs : 0 < s) (hsd : s ≤ (d : ℝ) - 2) (hA : 0 ≤ A) :
    ∃ (χ : ℝ → ℝ → ℝ) (D : ℝ), 0 < D ∧
      (∀ T : ℝ, 0 < T → ContDiff ℝ ∞ (χ T) ∧
        ∀ u : ℝ, 0 ≤ χ T u ∧ χ T u ≤ 1 ∧
          (|u| ≤ T → χ T u = 1) ∧
          (2*T ≤ u → χ T u = 0) ∧
          |deriv (χ T) u| ≤ D/T ∧
          (0 ≤ u → (1-χ T u)^2 ≤ u/T)) ∧
      ∀ R : ℝ, 0 < R → ∃ V S : ℝ, 0 ≤ V ∧ 0 ≤ S ∧
        ∀ {ι : Type*} (J : Finset ι) (a : ι → ℝ) (y : ι → OneParticle d)
          (ε : ℝ), 0 < ε → (∀ j ∈ J, 0 ≤ a j) → (∑ j ∈ J, a j ≤ A) →
          let U := fun x => ∑ j ∈ J, a j * RieszKernel s ε (x-y j)
          let Q := {x : OneParticle d | ∀ i, -R ≤ x i ∧ x i ≤ R}
          (∫ x in Q, U x) ≤ V ∧ ∀ T : ℝ, 0 < T →
            IntegrableOn (fun x => ‖EuclideanGradient (fun z => χ T (U z)) x‖^2) Q ∧
            IntegrableOn (fun x => (1-χ T (U x))^2) Q ∧
            (∫ x in Q, ‖EuclideanGradient (fun z => χ T (U z)) x‖^2) ≤ S/T ∧
            (∫ x in Q, (1-χ T (U x))^2) ≤ V/T := by
-- BODY
  obtain ⟨C, hC, hdC⟩ := scalar_bump_derivative_bound
  refine ⟨smoothPotentialCutoff, C, hC, ?_, ?_⟩
  · intro T hT
    refine ⟨smooth_potential_cutoff_smooth T, ?_⟩
    intro u
    refine ⟨(smooth_potential_cutoff_range T u).1,
      (smooth_potential_cutoff_range T u).2, ?_, ?_,
      smooth_potential_cutoff_derivative_bound C hC hdC T u hT,
      smooth_potential_cutoff_error T u hT⟩
    · intro hu
      apply scalar_bump_one
      rw [abs_div, abs_of_pos hT]
      exact (div_le_one hT).mpr hu
    · intro hu
      apply scalar_bump_zero
      exact ((le_div_iff₀ hT).mpr hu).trans (le_abs_self _)
  · intro R hR
    let Q := cubeSet d R
    let K := closedBall (0 : OneParticle d) (2*((d : ℝ)*R+1))
    let ζ : OneParticle d → ℝ := cubeSpatialBump d R hR
    rcases cubeSpatialBump_properties d R hR with ⟨hζ, hcζ, hRange, hSupp, hOne, Z, hZ, hGrad⟩
    have hK : MeasurableSet K := measurableSet_closedBall
    have hcK : IsCompact K := isCompact_closedBall _ _
    have hQc : IsClosed Q := by
      change IsClosed {x : OneParticle d | ∀ i, -R ≤ x i ∧ x i ≤ R}
      simp_rw [ofPred_forall]
      apply isClosed_iInter
      intro i
      exact (isClosed_le continuous_const (PiLp.continuous_apply 2 _ i)).inter
        (isClosed_le (PiLp.continuous_apply 2 _ i) continuous_const)
    have hQ : MeasurableSet Q := hQc.measurableSet
    have hQK : Q ⊆ K := by
      intro x hx
      have hh := cube_norm_bound d R hR x hx
      change dist x 0 ≤ _
      rw [dist_zero_right]
      have hp : 0 ≤ (d : ℝ)*R+1 := by positivity
      linarith
    have hcQ : IsCompact Q := hcK.of_isClosed_subset hQc hQK
    obtain ⟨P, F, B, hP, hF, hB, hlocal⟩ :=
      AtomicLocalRieszBounds d hd s hs hsd K hK hcK.measure_ne_top
    let V := A*P
    let S := 2*C^2*(A*B+2*Z*(A*F))
    refine ⟨V, S, mul_nonneg hA hP, by dsimp [S]; positivity, ?_⟩
    intro ι J a y ε hε ha hmass
    let U := fun x => ∑ j ∈ J, a j * RieszKernel s ε (x-y j)
    have hsource := AtomicInteractionSource d s ε hs hsd hε J a y ha
    have hU : ContDiff ℝ 2 U := hsource.1
    have hUn (x : OneParticle d) : 0 ≤ U x := by
      apply Finset.sum_nonneg
      intro j hj
      exact mul_nonneg (ha j hj) ((RieszKernelBounds s ε hs hε.le).1 (x-y j))
    have hlocal' := hlocal J a y ε A hε hA ha hmass
    have hV : (∫ x in Q, U x) ≤ V :=
      (setIntegral_mono_set hlocal'.1 (Filter.Eventually.of_forall hUn)
        (Filter.Eventually.of_forall (fun x hx => hQK hx))).trans hlocal'.2.2.2.1
    refine ⟨hV, ?_⟩
    intro T hT
    have hχ : ContDiff ℝ 1 (fun x => smoothPotentialCutoff T (U x)) :=
      ((smooth_potential_cutoff_smooth T).of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).comp
        (hU.of_le (by norm_num))
    have hχi : IntegrableOn
        (fun x => ‖EuclideanGradient (fun z => smoothPotentialCutoff T (U z)) x‖^2) Q :=
      (((continuous_gradient_C1 _ hχ).norm.pow 2).continuousOn).integrableOn_compact hcQ
    have hei : IntegrableOn (fun x => (1-smoothPotentialCutoff T (U x))^2) Q :=
      ((continuous_const.sub hχ.continuous).pow 2).continuousOn.integrableOn_compact hcQ
    have hSi : IntegrableOn
        (fun x => -basisLaplacian (EuclideanSpace.basisFun (Fin d) ℝ) U x) K := by
      simpa only [basis_eq_actual U hU] using hlocal'.2.2.1
    have hSign (x : OneParticle d) :
        0 ≤ -basisLaplacian (EuclideanSpace.basisFun (Fin d) ℝ) U x := by
      rw [basis_eq_actual U hU]
      exact (hsource.2 x).2
    have he := inner_source_cutoff_energy_bound volume (EuclideanSpace.basisFun (Fin d) ℝ)
      U ζ hU hUn hSign (hζ.of_le (by simp)) hcζ hRange K Q hK hQ hSupp hOne
      hSi hlocal'.2.1 Z C T hZ hC hT hGrad hdC
    simp only [basis_eq_actual U hU] at he
    have he' : (∫ x in Q, ‖EuclideanGradient (fun z => smoothPotentialCutoff T (U z)) x‖^2) ≤ S/T := by
      refine he.trans ?_
      calc
        _ ≤ (2*C^2/T)*(A*B+2*Z*(A*F)) :=
          mul_le_mul_of_nonneg_left
            (add_le_add hlocal'.2.2.2.2.2
              (mul_le_mul_of_nonneg_left hlocal'.2.2.2.2.1 (by positivity))) (by positivity)
        _ = S/T := by dsimp [S]; ring
    have hUi : IntegrableOn U Q := hU.continuous.continuousOn.integrableOn_compact hcQ
    have herr := integral_mono_ae hei (hUi.div_const T)
      (Filter.Eventually.of_forall (fun x => smooth_potential_cutoff_error T (U x) hT (hUn x)))
    rw [integral_div] at herr
    refine ⟨hχi, hei, he', herr.trans (div_le_div_of_nonneg_right hV hT.le)⟩
