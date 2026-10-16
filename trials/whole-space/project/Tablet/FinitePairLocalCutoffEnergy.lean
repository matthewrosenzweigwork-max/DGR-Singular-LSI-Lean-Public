module

public import Tablet.FinitePairLocalRieszControl
public import Tablet.PairRelativeGradient
public import Tablet.PairInteractionSource
public import Tablet.AtomicLocalCutoffEnergy
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.InnerProductSpace.Laplacian

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
open MeasureTheory Measure Set Metric Function
open scoped ContDiff NNReal Pointwise
noncomputable section

-- [TABLET NODE: FinitePairLocalCutoffEnergy]
theorem FinitePairLocalCutoffEnergy (d N : ℕ) (hd : 3 ≤ d) (hN : 2 ≤ N)
    (s B : ℝ) (hs : 0 < s) (hsd : s ≤ (d : ℝ)-2) (hB : 0 ≤ B) :
    ∃ (χ : ℝ → ℝ → ℝ) (D : ℝ), 0 < D ∧
      (∀ T : ℝ, 0 < T → ContDiff ℝ ∞ (χ T) ∧ ∀ u : ℝ,
        0 ≤ χ T u ∧ χ T u ≤ 1 ∧ (|u| ≤ T → χ T u = 1) ∧
        (2*T ≤ u → χ T u = 0) ∧ |deriv (χ T) u| ≤ D/T ∧
        (0 ≤ u → (1-χ T u)^2 ≤ u/T)) ∧
      ∀ R : ℝ, 0 < R → ∃ V S : ℝ, 0 ≤ V ∧ 0 ≤ S ∧
        ∀ coupling ε : ℝ, 0 ≤ coupling → coupling ≤ B → 0 < ε →
          let U := PairInteraction (d := d) (N := N) s coupling ε
          let Q := closedBall (0 : ParticleConfig d N) R
          (∫ X in Q, U X) ≤ V ∧ ∀ T : ℝ, 0 < T →
            tsupport (fun X => χ T (U X)) ⊆ {X | U X ≤ 2*T} ∧
            IntegrableOn (fun X => ‖EuclideanGradient (fun Y => χ T (U Y)) X‖^2) Q ∧
            IntegrableOn (fun X => (1-χ T (U X))^2) Q ∧
            (∫ X in Q, ‖EuclideanGradient (fun Y => χ T (U Y)) X‖^2) ≤ S/T ∧
            (∫ X in Q, (1-χ T (U X))^2) ≤ V/T := by
-- BODY
  classical
  let E := ParticleConfig d N
  let D : (E → ℝ) → E → E → ℝ := fun u v x => fderiv ℝ u x v
  let basisLaplacian := fun (b : OrthonormalBasis (Fin N × Fin d) ℝ E) (H : E → ℝ) (x : E) =>
    ∑ i, D (D H (b i)) (b i) x
  have integrable_product_compact (μ : Measure E) [IsAddHaarMeasure μ]
      (a b : E → ℝ) (ha : Continuous a) (hb : Continuous b) (hcb : HasCompactSupport b) :
      Integrable (fun x => a x*b x) μ :=
    (ha.mul hb).integrable_of_hasCompactSupport hcb.mul_left
  have gradient_norm_eq_fderiv_norm (f : E → ℝ) (x : E) :
      ‖gradient f x‖ = ‖fderiv ℝ f x‖ :=
    (InnerProductSpace.toDual ℝ E).symm.norm_map _

  have continuous_D {u : E → ℝ} (hu : ContDiff ℝ 1 u) (v : E) :
      Continuous (D u v) := by
    exact (hu.continuous_fderiv_apply (by norm_num)).comp
      (continuous_id.prodMk continuous_const)

  have contDiff_D {u : E → ℝ} (hu : ContDiff ℝ 2 u) (v : E) :
      ContDiff ℝ 1 (D u v) := by
    exact (hu.contDiff_fderiv_apply (m := 1) (by norm_num)).comp
      (contDiff_id.prodMk contDiff_const)

  have compact_D {u : E → ℝ} (hu : HasCompactSupport u) (v : E) :
      HasCompactSupport (D u v) := by
    exact hu.fderiv_apply ℝ v

  have sum_D_sq_eq_gradient_norm (b : OrthonormalBasis (Fin N × Fin d) ℝ E) (u : E → ℝ) (x : E) :
      ∑ i, (D u (b i) x)^2 = ‖gradient u x‖^2 := by
    have hi (i : (Fin N × Fin d)) : D u (b i) x = inner ℝ (gradient u x) (b i) := by
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

  have D_mul (f g : E → ℝ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (v x : E) :
      D (fun x => f x*g x) v x = D f v x*g x+f x*D g v x := by
    have h := (hf.differentiable (by norm_num) x).hasFDerivAt.mul
      (hg.differentiable (by norm_num) x).hasFDerivAt
    have heq := congrArg (fun L : E →L[ℝ] ℝ => L v) h.fderiv
    change fderiv ℝ (fun x => f x*g x) x v = _ at heq
    simpa [D,_root_.add_apply,_root_.smul_apply,smul_eq_mul,mul_comm,add_comm] using heq

  have D_comp_scalar (U : E → ℝ) (hU : ContDiff ℝ 1 U) (Φ : ℝ → ℝ)
      (hΦ : ContDiff ℝ 1 Φ) (v x : E) :
      D (fun x => Φ (U x)) v x = deriv Φ (U x)*D U v x := by
    have h := (hΦ.differentiable (by norm_num) (U x)).hasDerivAt.comp_hasFDerivAt x
      (hU.differentiable (by norm_num) x).hasFDerivAt
    have heq := congrArg (fun L : E →L[ℝ] ℝ => L v) h.fderiv
    simpa [D,Function.comp_def,_root_.smul_apply,smul_eq_mul] using heq

  have sum_D_mul_eq_inner (b : OrthonormalBasis (Fin N × Fin d) ℝ E) (f g : E → ℝ) (x : E) :
      (∑ i, D f (b i) x*D g (b i) x) = inner ℝ (gradient f x) (gradient g x) := by
    have hd (u : E → ℝ) (i : (Fin N × Fin d)) : D u (b i) x = inner ℝ (gradient u x) (b i) := by
      dsimp [D]
      exact (inner_gradient_left (𝕜 := ℝ) (f := u) (x := x) (y := b i)).symm
    simp_rw [hd]
    have h := b.sum_inner_mul_inner (gradient f x) (gradient g x)
    simpa only [real_inner_comm] using h

  have compact_green_identity (μ : Measure E) [IsAddHaarMeasure μ]
      (b : OrthonormalBasis (Fin N × Fin d) ℝ E) (U w : E → ℝ)
      (hU : ContDiff ℝ 2 U) (hw : ContDiff ℝ 1 w) (hcw : HasCompactSupport w) :
      (∫ x, inner ℝ (gradient U x) (gradient w x) ∂μ) =
        -(∫ x, basisLaplacian b U x*w x ∂μ) := by
    have hUw (i : (Fin N × Fin d)) : Integrable (fun x => D U (b i) x*D w (b i) x) μ :=
      integrable_product_compact μ _ _ (continuous_D (hU.of_le (by norm_num)) _)
        (continuous_D hw _) (compact_D hcw _)
    have hDDw (i : (Fin N × Fin d)) : Integrable (fun x => D (D U (b i)) (b i) x*w x) μ :=
      integrable_product_compact μ _ _ (continuous_D (contDiff_D hU _) _)
        hw.continuous hcw
    have hIBP_undifferentiated (i : (Fin N × Fin d)) : Integrable (fun x => D U (b i) x*w x) μ :=
      integrable_product_compact μ _ _ (continuous_D (hU.of_le (by norm_num)) _) hw.continuous hcw
    have hi (i : (Fin N × Fin d)) : (∫ x, D U (b i) x*D w (b i) x ∂μ) =
        -(∫ x, D (D U (b i)) (b i) x*w x ∂μ) := by
      exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (μ := μ) (f := D U (b i)) (g := w) (v := b i)
        (hDDw i) (hUw i)
        (hIBP_undifferentiated i)
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

  have continuous_gradient_C1 (U : E → ℝ) (hU : ContDiff ℝ 1 U) : Continuous (gradient U) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hU.continuous_fderiv (by norm_num))

  have D_pow_two (ζ : E → ℝ) (hζ : ContDiff ℝ 1 ζ) (v x : E) :
      D (fun x => ζ x^2) v x = 2*ζ x*D ζ v x := by
    have h := D_mul ζ ζ hζ hζ v x
    simpa only [pow_two] using h.trans (by ring)

  have compact_source_primitive_identity (μ : Measure E) [IsAddHaarMeasure μ]
      (b : OrthonormalBasis (Fin N × Fin d) ℝ E) (U ζ : E → ℝ) (hU : ContDiff ℝ 2 U)
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
    have hdw (i : (Fin N × Fin d)) (x : E) : D w (b i) x =
        2*ζ x*D ζ (b i) x*Φ (U x)+ζ x^2*deriv Φ (U x)*D U (b i) x := by
      rw [D_mul (fun x => ζ x^2) (fun x => Φ (U x)) (hζ.pow 2) (hΦ.comp hU1),
        D_pow_two ζ hζ,D_comp_scalar U hU1 Φ hΦ]
      ring
    have hinner (x : E) : inner ℝ (gradient U x) (gradient w x) =
        2*ζ x*Φ (U x)*inner ℝ (gradient U x) (gradient ζ x)+
          ζ x^2*deriv Φ (U x)*‖gradient U x‖^2 := by
      rw [← sum_D_mul_eq_inner b U w x]
      have heq (i : (Fin N × Fin d)) : D U (b i) x*D w (b i) x =
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

  have gradient_scalar_comp_norm_sq (U : E → ℝ) (hU : ContDiff ℝ 1 U)
      (χ : ℝ → ℝ) (hχ : ContDiff ℝ 1 χ) (x : E) :
      ‖gradient (fun y => χ (U y)) x‖^2 = (deriv χ (U x))^2*‖gradient U x‖^2 := by
    have h := (hχ.differentiable (by norm_num) (U x)).hasDerivAt.comp_hasFDerivAt x
      (hU.differentiable (by norm_num) x).hasFDerivAt
    rw [gradient_norm_eq_fderiv_norm,gradient_norm_eq_fderiv_norm]
    change ‖fderiv ℝ (χ ∘ U) x‖^2 = _
    rw [h.fderiv,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]

  have source_cutoff_scalar_upper (z φ a s c Z r : ℝ)
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

  have basis_eq_actual (U : E → ℝ) (hU : ContDiff ℝ 2 U) (x : E) :
      basisLaplacian (EuclideanSpace.basisFun (Fin N × Fin d) ℝ) U x = EuclideanLaplacian U x := by
    rw [(EuclideanDerivativeCoordinates U x).2]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [D, basisLaplacian, EuclideanHessian]
    change (fderiv ℝ (fun z => fderiv ℝ U z ((EuclideanSpace.basisFun (Fin N × Fin d) ℝ) k)) x)
      ((EuclideanSpace.basisFun (Fin N × Fin d) ℝ) k) = _
    have hU' : ContDiff ℝ ((1 : WithTop ℕ∞)+1) U := by convert hU using 1 <;> norm_num
    have hfd := (contDiff_succ_iff_fderiv.mp hU').2.2
    rw [fderiv_clm_apply ((hfd.differentiable (by norm_num)) x) (differentiableAt_const _)]
    simp
  obtain ⟨χ, C, hC, hscalar, _⟩ := AtomicLocalCutoffEnergy.{0} d hd s 0 hs hsd (by norm_num)
  refine ⟨χ, C, hC, hscalar, ?_⟩
  intro R hR
  let M := 2*(R+1)
  have hM : 0 < M := by dsimp [M]; positivity
  let K := closedBall (0 : E) M
  let Q := closedBall (0 : E) R
  have hQK : Q ⊆ K := closedBall_subset_closedBall (by dsimp [M]; linarith)
  let zeta : ContDiffBump (0 : E) := ⟨R+1, M, by positivity, by dsimp [M]; linarith⟩
  let ζ : E → ℝ := zeta
  have hζs : ContDiff ℝ ∞ ζ := zeta.contDiff
  have hcζ : HasCompactSupport ζ := zeta.hasCompactSupport
  have hζ : ContDiff ℝ 1 ζ := hζs.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)
  have hζrange (x : E) : 0 ≤ ζ x ∧ ζ x ≤ 1 := ⟨zeta.nonneg, zeta.le_one⟩
  have hSupp : support ζ ⊆ K := by rw [zeta.support_eq]; exact ball_subset_closedBall
  have hOne (x : E) (hx : x ∈ Q) : ζ x = 1 := zeta.one_of_mem_closedBall (by
    change dist x 0 ≤ R+1
    have hh : dist x 0 ≤ R := hx
    linarith)
  obtain ⟨Z, hZbound⟩ := (hcζ.fderiv ℝ).exists_bound_of_continuous (hζ.continuous_fderiv (by norm_num))
  have hZ : 0 ≤ Z := (norm_nonneg _).trans (hZbound 0)
  have hGradζ (x : E) : ‖gradient ζ x‖ ≤ Z := by
    rw [gradient_norm_eq_fderiv_norm]
    exact hZbound x
  obtain ⟨P₀, F₀, S₀, hP₀, hF₀, hS₀, hrows⟩ := FinitePairLocalRieszControl d hd s hs hsd M hM
  let I := Fin N × Fin N
  let v := fun p : I => if p.1 < p.2 then
    volume.real (closedBall (0 : EuclideanSpace ℝ {q : Fin N × Fin d // q.1 ≠ p.1}) M) else 0
  let W := ∑ p : I, v p
  have hv (p : I) : 0 ≤ v p := by dsimp [v]; split_ifs <;> positivity
  have hW : 0 ≤ W := Finset.sum_nonneg (fun p _ => hv p)
  let V := (B/(N : ℝ))*P₀*W
  let S := 2*C^2*((B/(N : ℝ))*S₀*W + 2*Z*((B/(N : ℝ))*F₀*W))
  refine ⟨V, S, by dsimp [V]; positivity, by dsimp [S]; positivity, ?_⟩
  intro a ε ha haB hε
  let U : E → ℝ := PairInteraction s a ε
  have hsource := PairInteractionSource d N s a ε hs hsd ha hε
  have hU : ContDiff ℝ 2 U := hsource.1.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by norm_num)
  have hUn (X : E) : 0 ≤ U X := by
    dsimp [U, PairInteraction]
    apply mul_nonneg (div_nonneg ha (Nat.cast_nonneg _))
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    split_ifs
    · exact (RieszKernelBounds s ε hs hε.le).1 _
    · exact le_rfl
  let k : OneParticle d → ℝ := RieszKernel s ε
  have hk := AtomicInteractionSource d s ε hs hsd hε ({()} : Finset Unit)
    (fun _ => (1 : ℝ)) (fun _ => (0 : OneParticle d)) (by intro q hq; norm_num)
  simp only [Finset.sum_singleton, one_mul, sub_zero] at hk
  have hk2 : ContDiff ℝ 2 k := hk.1
  have hk1 : ContDiff ℝ 1 k := hk2.of_le (by norm_num)
  let fP := fun p : I => fun X : E => if p.1 < p.2 then
    k (ParticlePosition X p.1 - ParticlePosition X p.2) else 0
  let fF := fun p : I => fun X : E => if p.1 < p.2 then
    Real.sqrt 2*‖EuclideanGradient k (ParticlePosition X p.1 - ParticlePosition X p.2)‖ else 0
  let fS := fun p : I => fun X : E => if p.1 < p.2 then
    2*(-EuclideanLaplacian k (ParticlePosition X p.1 - ParticlePosition X p.2)) else 0
  have hPi (p : I) : IntegrableOn (fP p) K ∧ (∫ X in K, fP p X) ≤ P₀*v p := by
    by_cases hp : p.1 < p.2
    · have hh := hrows N p.1 p.2 (ne_of_lt hp) ε hε
      exact ⟨by simpa [fP, K, k, hp] using hh.1,
        by simpa [fP, K, k, hp, v] using hh.2.2.2.1⟩
    · simp [fP, hp, v]
  have hFi (p : I) : IntegrableOn (fF p) K ∧ (∫ X in K, fF p X) ≤ F₀*v p := by
    by_cases hp : p.1 < p.2
    · have hh := hrows N p.1 p.2 (ne_of_lt hp) ε hε
      exact ⟨by simpa [fF, K, k, hp] using hh.2.1,
        by simpa [fF, K, k, hp, v] using hh.2.2.2.2.1⟩
    · simp [fF, hp, v]
  have hSi (p : I) : IntegrableOn (fS p) K ∧ (∫ X in K, fS p X) ≤ S₀*v p := by
    by_cases hp : p.1 < p.2
    · have hh := hrows N p.1 p.2 (ne_of_lt hp) ε hε
      exact ⟨by simpa [fS, K, k, hp] using hh.2.2.1,
        by simpa [fS, K, k, hp, v] using hh.2.2.2.2.2⟩
    · simp [fS, hp, v]
  have hsumBound (f : I → E → ℝ) (C₀ : ℝ)
      (h : ∀ p, IntegrableOn (f p) K ∧ (∫ X in K, f p X) ≤ C₀*v p) :
      IntegrableOn (fun X => ∑ p : I, f p X) K ∧
      (∫ X in K, ∑ p : I, f p X) ≤ C₀*W := by
    refine ⟨integrable_finsetSum _ (fun p _ => (h p).1), ?_⟩
    rw [integral_finsetSum _ (fun p _ => (h p).1)]
    exact (Finset.sum_le_sum (fun p _ => (h p).2)).trans_eq (by rw [← Finset.mul_sum])
  have hPb := hsumBound fP P₀ hPi
  have hFb := hsumBound fF F₀ hFi
  have hSb := hsumBound fS S₀ hSi
  have hUp : U = fun X => (a/(N : ℝ)) * ∑ p : I, fP p X := by
    funext X
    simp only [U, PairInteraction, fP, I, k, Fintype.sum_prod_type]
  have hUi : IntegrableOn U K := by rw [hUp]; exact hPb.1.const_mul _
  have hPV : (∫ X in K, U X) ≤ V := by
    rw [hUp, integral_const_mul]
    calc
      _ ≤ (a/(N : ℝ))*(P₀*W) := mul_le_mul_of_nonneg_left hPb.2 (by positivity)
      _ ≤ (B/(N : ℝ))*(P₀*W) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right haB (Nat.cast_nonneg _)) (by positivity)
      _ = V := by dsimp [V]; ring
  have hfPs (p : I) : ContDiff ℝ 1 (fP p) := by
    by_cases hp : p.1 < p.2
    · have hr : ContDiff ℝ 1 (fun X : E => ParticlePosition X p.1 - ParticlePosition X p.2) := by
        change ContDiff ℝ 1 (fun X : EuclideanSpace ℝ (Fin N × Fin d) =>
          WithLp.toLp 2 (fun k => X (p.1,k)) - WithLp.toLp 2 (fun k => X (p.2,k)))
        fun_prop
      simpa only [fP, if_pos hp, Function.comp_def] using hk1.comp hr
    · simpa only [fP, if_neg hp] using (contDiff_const : ContDiff ℝ 1 (fun _ : E => (0 : ℝ)))
  have hGradPoint (X : E) : ‖EuclideanGradient U X‖ ≤ (a/(N : ℝ))*∑ p : I, fF p X := by
    let DF := fun p : I => fderiv ℝ (fP p) X
    have hder := (HasFDerivAt.fun_sum (fun p (_ : p ∈ (Finset.univ : Finset I)) =>
      (hfPs p).differentiable (by norm_num) X |>.hasFDerivAt)).const_smul (a/(N : ℝ))
    have hdU : fderiv ℝ U X = (a/(N : ℝ)) • ∑ p : I, DF p := by
      rw [hUp]
      exact hder.fderiv
    have hn (p : I) : ‖DF p‖ = fF p X := by
      by_cases hp : p.1 < p.2
      · dsimp [DF]
        simp only [fP, if_pos hp]
        rw [← (GradientNormIdentity _ X).2, PairRelativeGradient p.1 p.2 (ne_of_lt hp) k hk1 X]
        simp only [fF, if_pos hp]
      · simp [DF, fP, hp, fF]
    rw [(GradientNormIdentity U X).2, hdU, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ a/(N : ℝ))]
    exact (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans_eq
      (by simp only [hn])
  have hgUi : IntegrableOn (fun X => ‖EuclideanGradient U X‖) K :=
    (continuous_gradient_C1 U hU1).norm.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hgUB : (∫ X in K, ‖EuclideanGradient U X‖) ≤ (B/(N : ℝ))*F₀*W := by
    have hh := integral_mono_ae hgUi (hFb.1.const_mul (a/(N : ℝ)))
      (Filter.Eventually.of_forall hGradPoint)
    rw [integral_const_mul] at hh
    calc
      _ ≤ (a/(N : ℝ))*(F₀*W) := hh.trans (mul_le_mul_of_nonneg_left hFb.2 (by positivity))
      _ ≤ (B/(N : ℝ))*(F₀*W) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right haB (Nat.cast_nonneg _)) (by positivity)
      _ = _ := by ring
  let σ := fun z : OneParticle d =>
    (((d : ℝ)-s-2)*‖z‖^2 + (d : ℝ)*ε^2) * (‖z‖^2+ε^2)^(-s/2-2)
  have hσ (z : OneParticle d) : -EuclideanLaplacian k z = σ z := (hk.2 z).1
  have hUS : (fun X => -EuclideanLaplacian U X) = fun X => (a/(N : ℝ))*∑ p : I, fS p X := by
    funext X
    have hh := (hsource.2 X).1
    have hf : (∑ p : I, fS p X) =
        2*(∑ i : Fin N, ∑ j : Fin N, if i<j then σ (ParticlePosition X i-ParticlePosition X j) else 0) := by
      simp only [fS, hσ, I, Fintype.sum_prod_type]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs <;> simp
    rw [hf]
    exact hh.trans (by dsimp [σ]; ring)
  have hsUi : IntegrableOn (fun X => -EuclideanLaplacian U X) K := by rw [hUS]; exact hSb.1.const_mul _
  have hsUB : (∫ X in K, -EuclideanLaplacian U X) ≤ (B/(N : ℝ))*S₀*W := by
    rw [hUS, integral_const_mul]
    calc
      _ ≤ (a/(N : ℝ))*(S₀*W) := mul_le_mul_of_nonneg_left hSb.2 (by positivity)
      _ ≤ (B/(N : ℝ))*(S₀*W) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right haB (Nat.cast_nonneg _)) (by positivity)
      _ = _ := by ring
  have hVQ : (∫ X in Q, U X) ≤ V :=
    (setIntegral_mono_set hUi (Filter.Eventually.of_forall hUn) (Filter.Eventually.of_forall hQK)).trans hPV
  refine ⟨hVQ, ?_⟩
  intro T hT
  obtain ⟨hχs, hχprops⟩ := hscalar T hT
  have hχ : ContDiff ℝ 1 (χ T) := hχs.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)
  let Φ := fun u : ℝ => ∫ t in (0 : ℝ)..u, (deriv (χ T) t)^2
  have hcΦ : Continuous (fun u => (deriv (χ T) u)^2) := hχ.continuous_deriv_one.pow 2
  have hΦder (u : ℝ) : deriv Φ u = (deriv (χ T) u)^2 :=
    (hcΦ.integral_hasStrictDerivAt 0 u).hasDerivAt.deriv
  have hΦ : ContDiff ℝ 1 Φ := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨fun u => (hcΦ.integral_hasStrictDerivAt 0 u).hasDerivAt.differentiableAt, ?_⟩
    simpa only [funext hΦder] using hcΦ
  have hdZero (u : ℝ) (hu : 2*T<u) : deriv (χ T) u = 0 := by
    have heq : (χ T) =ᶠ[nhds u] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [eventually_gt_nhds hu] with t ht
      exact (hχprops t).2.2.2.1 ht.le
    rw [heq.deriv_eq, deriv_const]
  have hΦbound (u : ℝ) (hu : 0 ≤ u) : 0 ≤ Φ u ∧ Φ u ≤ 2*C^2/T := by
    have hsmall (y : ℝ) (hy : 0 ≤ y) (hy2 : y ≤ 2*T) : Φ y ≤ 2*C^2/T := by
      have hh := intervalIntegral.integral_mono_on (μ := volume) hy
        (hcΦ.intervalIntegrable 0 y) (continuous_const.intervalIntegrable 0 y) (fun t _ => by
          simpa [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (div_nonneg hC.le hT.le)).mpr
            (hχprops t).2.2.2.2.1)
      rw [intervalIntegral.integral_const] at hh
      simp only [sub_zero, smul_eq_mul] at hh
      refine hh.trans ((mul_le_mul_of_nonneg_right hy2 (sq_nonneg _)).trans_eq ?_)
      field_simp
    refine ⟨intervalIntegral.integral_nonneg hu (fun _ _ => sq_nonneg _), ?_⟩
    by_cases hu2 : u ≤ 2*T
    · exact hsmall u hu hu2
    · have hz : (∫ t in (2*T)..u, (deriv (χ T) t)^2) = 0 := by
        rw [intervalIntegral.integral_of_le (le_of_not_ge hu2)]
        apply setIntegral_eq_zero_of_forall_eq_zero
        intro t ht
        rw [hdZero t ht.1, zero_pow (by decide : 2 ≠ 0)]
      have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (hcΦ.intervalIntegrable 0 (2*T)) (hcΦ.intervalIntegrable (2*T) u)
      change (∫ t in (0 : ℝ)..u, (deriv (χ T) t)^2) ≤ _
      rw [← hadd, hz, add_zero]
      exact hsmall (2*T) (by positivity) le_rfl
  let b := EuclideanSpace.basisFun (Fin N × Fin d) ℝ
  have hGreen := compact_source_primitive_identity volume b U ζ hU hζ hcζ Φ hΦ
  simp_rw [hΦder] at hGreen
  have hComp (x : E) : ‖gradient (fun y => χ T (U y)) x‖^2 =
      (deriv (χ T) (U x))^2*‖gradient U x‖^2 := gradient_scalar_comp_norm_sq U hU1 (χ T) hχ x
  have hTrace (x : E) : basisLaplacian b U x = EuclideanLaplacian U x := basis_eq_actual U hU x
  have heqComp : (fun x : E => ζ x^2*(deriv (χ T) (U x))^2*‖gradient U x‖^2) =
      fun x => ζ x^2*‖gradient (fun y => χ T (U y)) x‖^2 := by
    funext x
    rw [hComp]
    ring
  rw [heqComp] at hGreen
  simp_rw [hTrace] at hGreen
  have hgU := continuous_gradient_C1 U hU1
  have hgζ := continuous_gradient_C1 ζ hζ
  have hLap : Continuous (EuclideanLaplacian U) := by
    have hh : Continuous (basisLaplacian b U) := continuous_finsetSum _ (fun i _ => continuous_D (contDiff_D hU _) _)
    have heq : basisLaplacian b U = EuclideanLaplacian U := funext hTrace
    rw [← heq]
    exact hh
  have hcζ2 : HasCompactSupport (fun x => ζ x^2) := by
    simpa only [Function.comp_def] using hcζ.comp_left (g := fun z : ℝ => z^2) (by simp)
  have hiSrc : Integrable (fun x => ζ x^2*Φ (U x)*(-EuclideanLaplacian U x)) volume := by
    have hh : Continuous (fun x => Φ (U x)*(-EuclideanLaplacian U x)) :=
      (hΦ.continuous.comp hU.continuous).mul hLap.neg
    exact ((hζ.continuous.pow 2).mul (hΦ.continuous.comp hU.continuous) |>.mul hLap.neg).integrable_of_hasCompactSupport (hcζ2.mul_right.mul_right)
  have hiCross : Integrable (fun x => ζ x*Φ (U x)*inner ℝ (gradient U x) (gradient ζ x)) volume := by
    have hh : Continuous (fun x => Φ (U x)*inner ℝ (gradient U x) (gradient ζ x)) :=
      (hΦ.continuous.comp hU.continuous).mul (hgU.inner hgζ)
    exact (hζ.continuous.mul (hΦ.continuous.comp hU.continuous) |>.mul (hgU.inner hgζ)).integrable_of_hasCompactSupport (hcζ.mul_right.mul_right)
  change IntegrableOn (fun X : E => ‖gradient U X‖) K at hgUi
  change (∫ X : E in K, ‖gradient U X‖) ≤ _ at hgUB
  let A := 2*C^2/T
  have hiLeft := hiSrc.sub (hiCross.const_mul 2)
  have hiRight : Integrable (fun x => A*K.indicator
      (fun x => -EuclideanLaplacian U x+2*Z*‖gradient U x‖) x) volume :=
    ((integrable_indicator_iff measurableSet_closedBall).mpr (hsUi.add (hgUi.const_mul (2*Z)))).const_mul A
  have hpoint (x : E) : ζ x^2*Φ (U x)*(-EuclideanLaplacian U x)-
      2*(ζ x*Φ (U x)*inner ℝ (gradient U x) (gradient ζ x)) ≤
      A*K.indicator (fun x => -EuclideanLaplacian U x+2*Z*‖gradient U x‖) x := by
    by_cases hx : x∈K
    · rw [Set.indicator_of_mem hx]
      have hi : |inner ℝ (gradient U x) (gradient ζ x)| ≤ Z*‖gradient U x‖ := by
        calc
          _ ≤ ‖gradient U x‖*‖gradient ζ x‖ := abs_real_inner_le_norm _ _
          _ ≤ ‖gradient U x‖*Z := mul_le_mul_of_nonneg_left (hGradζ x) (norm_nonneg _)
          _ = _ := mul_comm _ _
      have hh := source_cutoff_scalar_upper (ζ x) (Φ (U x)) A (-EuclideanLaplacian U x)
        (inner ℝ (gradient U x) (gradient ζ x)) Z ‖gradient U x‖
        (hζrange x).1 (hζrange x).2 (hΦbound (U x) (hUn x)).1 (hΦbound (U x) (hUn x)).2
        (hsource.2 x).2 hZ (norm_nonneg _) hi
      simpa only [mul_assoc] using hh
    · have hz : ζ x = 0 := notMem_support.mp (fun hs => hx (hSupp hs))
      rw [hz, Set.indicator_of_notMem hx]
      simp
  have hE := integral_mono hiLeft hiRight hpoint
  change (∫ x : E, ζ x^2*Φ (U x)*(-EuclideanLaplacian U x)-
    2*(ζ x*Φ (U x)*inner ℝ (gradient U x) (gradient ζ x))) ≤ _ at hE
  rw [integral_sub hiSrc (hiCross.const_mul 2), integral_const_mul, integral_const_mul,
    integral_indicator measurableSet_closedBall,
    ] at hE
  change _ ≤ A*(∫ x : E in K, -EuclideanLaplacian U x+2*Z*‖gradient U x‖) at hE
  rw [integral_add hsUi (hgUi.const_mul (2*Z)), integral_const_mul] at hE
  have hEnergyGlobal : (∫ x, ζ x^2*‖gradient (fun y => χ T (U y)) x‖^2) ≤
      A*((∫ x in K, -EuclideanLaplacian U x)+2*Z*(∫ x in K, ‖gradient U x‖)) := hGreen.trans_le hE
  have hχU : ContDiff ℝ 1 (fun x => χ T (U x)) := hχ.comp hU1
  have hEnergyCont : Continuous (fun x => ‖gradient (fun y => χ T (U y)) x‖^2) :=
    (continuous_gradient_C1 _ hχU).norm.pow 2
  have hEi : Integrable (fun x => ζ x^2*‖gradient (fun y => χ T (U y)) x‖^2) volume := by
    exact ((hζ.continuous.pow 2).mul hEnergyCont).integrable_of_hasCompactSupport hcζ2.mul_right
  have hEq : (∫ x in Q, ‖gradient (fun y => χ T (U y)) x‖^2) =
      ∫ x in Q, ζ x^2*‖gradient (fun y => χ T (U y)) x‖^2 := by
    apply setIntegral_congr_fun measurableSet_closedBall
    intro x hx
    change ‖gradient (fun y => χ T (U y)) x‖^2 = ζ x^2*‖gradient (fun y => χ T (U y)) x‖^2
    rw [hOne x hx]
    simp
  have hEnergyQ : (∫ x in Q, ‖gradient (fun y => χ T (U y)) x‖^2) ≤ S/T := by
    rw [hEq]
    calc
      _ ≤ ∫ x, ζ x^2*‖gradient (fun y => χ T (U y)) x‖^2 :=
        setIntegral_le_integral hEi (Filter.Eventually.of_forall (fun x => by positivity))
      _ ≤ A*((∫ x in K, -EuclideanLaplacian U x)+2*Z*(∫ x in K, ‖gradient U x‖)) := hEnergyGlobal
      _ ≤ A*((B/(N : ℝ))*S₀*W+2*Z*((B/(N : ℝ))*F₀*W)) :=
        mul_le_mul_of_nonneg_left (add_le_add hsUB (mul_le_mul_of_nonneg_left hgUB (by positivity))) (by dsimp [A]; positivity)
      _ = S/T := by dsimp [A, S]; ring
  have hei : IntegrableOn (fun x => (1-χ T (U x))^2) Q :=
    ((continuous_const.sub hχU.continuous).pow 2).continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hUiQ : IntegrableOn U Q := hU.continuous.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have herror := integral_mono_ae hei (hUiQ.div_const T)
    (Filter.Eventually.of_forall (fun x => (hχprops (U x)).2.2.2.2.2 (hUn x)))
  rw [integral_div] at herror
  have hsupp : tsupport (fun X => χ T (U X)) ⊆ {X | U X ≤ 2*T} := by
    apply closure_minimal _ (isClosed_le hU.continuous continuous_const)
    intro X hX
    by_contra hn
    exact hX ((hχprops (U X)).2.2.2.1 (le_of_not_ge hn))
  exact ⟨hsupp, hEnergyCont.continuousOn.integrableOn_compact (isCompact_closedBall _ _), hei,
    hEnergyQ, herror.trans (div_le_div_of_nonneg_right hVQ hT.le)⟩
