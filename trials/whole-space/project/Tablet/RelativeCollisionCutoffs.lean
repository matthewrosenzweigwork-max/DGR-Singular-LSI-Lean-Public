import Tablet.CompactGradientCalculus
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Basic
import Tablet.RelativePairCoordinates
open MeasureTheory Filter Set
open scoped Topology ContDiff

namespace RelativeCollisionCutoffs
private noncomputable def spatialBump (ι : Type*) [Fintype ι] : ContDiffBump (0 : EuclideanSpace ℝ ι) :=
  ⟨1, 2, by norm_num, by norm_num⟩
private noncomputable def shrinkingCollisionCutoff {ι : Type*} [Fintype ι] (n : ℕ)
    (z : EuclideanSpace ℝ ι) : ℝ := 1 - spatialBump ι (((n : ℝ)+1) • z)

private lemma shrinkingCollisionCutoff_smooth {ι : Type*} [Fintype ι] (n : ℕ) :
    ContDiff ℝ ∞ (shrinkingCollisionCutoff (ι := ι) n) := by
  have hs : ContDiff ℝ ∞ (spatialBump ι : EuclideanSpace ℝ ι → ℝ) := (spatialBump ι).contDiff
  unfold shrinkingCollisionCutoff
  fun_prop

private lemma shrinkingCollisionCutoff_unitBounds {ι : Type*} [Fintype ι] (n : ℕ) (z : EuclideanSpace ℝ ι) :
    0 ≤ shrinkingCollisionCutoff n z ∧ shrinkingCollisionCutoff n z ≤ 1 := by
  have hn := (spatialBump ι).nonneg (x := ((n:ℝ)+1) • z)
  have h1 := (spatialBump ι).le_one (x := ((n:ℝ)+1) • z)
  unfold shrinkingCollisionCutoff
  constructor <;> linarith

private lemma shrinkingCollisionCutoff_vanishes {ι : Type*} [Fintype ι] (n : ℕ)
    (z : EuclideanSpace ℝ ι) (hz : ‖z‖ ≤ 1 / ((n:ℝ)+1)) :
    shrinkingCollisionCutoff n z = 0 := by
  have hn : 0 < ((n:ℝ)+1) := by positivity
  have hnorm : ‖((n:ℝ)+1) • z‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hn]
    exact (mul_le_mul_of_nonneg_left hz hn.le).trans_eq (by field_simp)
  have hb : spatialBump ι (((n:ℝ)+1) • z) = 1 := by
    apply (spatialBump ι).one_of_mem_closedBall
    simpa [spatialBump,Metric.mem_closedBall,dist_zero_right] using hnorm
  simp [shrinkingCollisionCutoff,hb]

private lemma shrinkingCollisionCutoff_one {ι : Type*} [Fintype ι] (n : ℕ)
    (z : EuclideanSpace ℝ ι) (hz : 2 / ((n:ℝ)+1) ≤ ‖z‖) :
    shrinkingCollisionCutoff n z = 1 := by
  have hn : 0 < ((n:ℝ)+1) := by positivity
  have hnorm : 2 ≤ ‖((n:ℝ)+1) • z‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hn]
    exact (mul_le_mul_of_nonneg_left hz hn.le).trans' (by field_simp; norm_num)
  have hb : spatialBump ι (((n:ℝ)+1) • z) = 0 := by
    apply (spatialBump ι).zero_of_le_dist
    simpa [spatialBump,dist_zero_right] using hnorm
  simp [shrinkingCollisionCutoff,hb]

private lemma shrinkingCollisionCutoff_pointwiseLimit {ι : Type*} [Fintype ι]
    (z : EuclideanSpace ℝ ι) (hz : z ≠ 0) :
    Tendsto (fun n : ℕ => shrinkingCollisionCutoff n z) atTop (𝓝 (1:ℝ)) := by
  have hi : Tendsto (fun n : ℕ => 2 / ((n:ℝ)+1)) atTop (𝓝 (0:ℝ)) := by
    simpa [div_eq_mul_inv] using (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => (1:ℝ) / ((n:ℝ)+1)) atTop (𝓝 0)).const_mul (2:ℝ)
  have he : ∀ᶠ n : ℕ in atTop, 2 / ((n:ℝ)+1) < ‖z‖ :=
    hi.eventually (gt_mem_nhds (norm_pos_iff.mpr hz))
  apply tendsto_const_nhds.congr'
  filter_upwards [he] with n hn
  exact (shrinkingCollisionCutoff_one n z hn.le).symm

private lemma shrinkingCollisionCutoff_gradient {ι : Type*} [Fintype ι]
    (n : ℕ) (z : EuclideanSpace ℝ ι) :
    EuclideanGradient (shrinkingCollisionCutoff n) z =
      -(((n:ℝ)+1) • EuclideanGradient (spatialBump ι) (((n:ℝ)+1) • z)) := by
  have hs : ContDiff ℝ ∞ (spatialBump ι : EuclideanSpace ℝ ι → ℝ) := (spatialBump ι).contDiff
  have h := (CompactGradientCalculus (spatialBump ι) hs (spatialBump ι).hasCompactSupport).2.2 ((n:ℝ)+1) z
  ext k
  rw [(EuclideanDerivativeCoordinates _ z).1]
  change (fderiv ℝ (fun y => 1 - spatialBump ι (((n:ℝ)+1) • y)) z) (EuclideanSpace.basisFun ι ℝ k) = _
  rw [fderiv_const_sub]
  change -(fderiv ℝ (fun y => spatialBump ι (((n:ℝ)+1) • y)) z) (EuclideanSpace.basisFun ι ℝ k) = _
  rw [← show EuclideanGradient (fun y => spatialBump ι (((n:ℝ)+1) • y)) z k =
    (fderiv ℝ (fun y => spatialBump ι (((n:ℝ)+1) • y)) z) (EuclideanSpace.basisFun ι ℝ k) from
      congrArg (fun v => v k) (EuclideanDerivativeCoordinates _ z).1]
  rw [h]
  rfl

private lemma spatialBump_gradient_zero {ι : Type*} [Fintype ι] :
    EuclideanGradient (spatialBump ι) 0 = 0 := by
  ext k
  rw [(EuclideanDerivativeCoordinates _ 0).1]
  change (fderiv ℝ (spatialBump ι : EuclideanSpace ℝ ι → ℝ) 0) (EuclideanSpace.basisFun ι ℝ k) = 0
  rw [(spatialBump ι).eventuallyEq_one.fderiv_eq]
  change (fderiv ℝ (fun _ : EuclideanSpace ℝ ι => (1:ℝ)) 0) (EuclideanSpace.basisFun ι ℝ k) = 0
  simp

private lemma spatialBump_gradient_zero_of_large {ι : Type*} [Fintype ι]
    (z : EuclideanSpace ℝ ι) (hz : 2 < ‖z‖) :
    EuclideanGradient (spatialBump ι) z = 0 := by
  have hnot : z ∉ tsupport (spatialBump ι : EuclideanSpace ℝ ι → ℝ) := by
    rw [(spatialBump ι).tsupport_eq]
    change z ∉ Metric.closedBall 0 2
    simpa [Metric.mem_closedBall,dist_zero_right,not_le] using hz
  have hd : (fderiv ℝ (spatialBump ι : EuclideanSpace ℝ ι → ℝ)) z = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hx => hnot (tsupport_fderiv_subset ℝ hx))
  ext k
  rw [(EuclideanDerivativeCoordinates _ z).1]
  change (fderiv ℝ (spatialBump ι : EuclideanSpace ℝ ι → ℝ)) z (EuclideanSpace.basisFun ι ℝ k) = 0
  rw [hd]
  rfl

private lemma shrinkingCollisionCutoff_gradientInverseBound {ι : Type*} [Fintype ι] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (z : EuclideanSpace ℝ ι),
      ‖EuclideanGradient (shrinkingCollisionCutoff n) z‖ ≤ C / ‖z‖ := by
  have hs : ContDiff ℝ ∞ (spatialBump ι : EuclideanSpace ℝ ι → ℝ) := (spatialBump ι).contDiff
  obtain ⟨C,hC⟩ := (CompactGradientCalculus (spatialBump ι) hs
    (spatialBump ι).hasCompactSupport).2.1.exists_bound_of_continuous
      (CompactGradientCalculus (spatialBump ι) hs (spatialBump ι).hasCompactSupport).1
  have hCn : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨2*C,by positivity,?_⟩
  intro n z
  rw [shrinkingCollisionCutoff_gradient,norm_neg,norm_smul,Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < (n:ℝ)+1)]
  by_cases hz : z=0
  · subst z
    simp [spatialBump_gradient_zero]
  have hzp : 0 < ‖z‖ := norm_pos_iff.mpr hz
  by_cases hsmall : ‖((n:ℝ)+1) • z‖ ≤ 2
  · have ha : ((n:ℝ)+1) * ‖z‖ ≤ 2 := by
      simpa [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < (n:ℝ)+1)] using hsmall
    have hh : ((n:ℝ)+1) ≤ 2/‖z‖ := (le_div_iff₀ hzp).2 ha
    calc
      _ ≤ ((n:ℝ)+1) * C := mul_le_mul_of_nonneg_left (hC _) (by positivity)
      _ ≤ (2/‖z‖)*C := mul_le_mul_of_nonneg_right hh hCn
      _ = _ := by ring
  · rw [spatialBump_gradient_zero_of_large _ (lt_of_not_ge hsmall),norm_zero,mul_zero]
    positivity

private lemma shrinkingCollisionCutoff_gradient_pointwiseLimit {ι : Type*} [Fintype ι]
    (z : EuclideanSpace ℝ ι) (hz : z ≠ 0) :
    Tendsto (fun n : ℕ => EuclideanGradient (shrinkingCollisionCutoff n) z)
      atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => 2 / ((n:ℝ)+1)) atTop (𝓝 (0:ℝ)) := by
    simpa [div_eq_mul_inv] using (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => (1:ℝ) / ((n:ℝ)+1)) atTop (𝓝 0)).const_mul (2:ℝ)
  have he : ∀ᶠ n : ℕ in atTop, 2 / ((n:ℝ)+1) < ‖z‖ :=
    hi.eventually (gt_mem_nhds (norm_pos_iff.mpr hz))
  apply tendsto_const_nhds.congr'
  filter_upwards [he] with n hn
  have hs : 2 < ‖((n:ℝ)+1) • z‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < (n:ℝ)+1)]
    exact (div_lt_iff₀ (by positivity : 0 < (n:ℝ)+1)).1 hn |>.trans_eq (mul_comm _ _)
  simp [shrinkingCollisionCutoff_gradient,spatialBump_gradient_zero_of_large _ hs]

private theorem scalarCutoffs {ι : Type*} [Fintype ι] :
    ∃ (χ : ℕ → EuclideanSpace ℝ ι → ℝ) (C : ℝ), 0 ≤ C ∧
      (∀ n, ContDiff ℝ ∞ (χ n)) ∧
      (∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1) ∧
      (∀ (n : ℕ) x, ‖x‖ ≤ 1 / ((n : ℝ) + 1) → χ n x = 0) ∧
      (∀ (n : ℕ) x, 2 / ((n : ℝ) + 1) ≤ ‖x‖ → χ n x = 1) ∧
      (∀ x, x ≠ 0 → Tendsto (fun n => χ n x) atTop (𝓝 (1 : ℝ))) ∧
      (∀ n x, ‖EuclideanGradient (χ n) x‖ ≤ C / ‖x‖) ∧
      (∀ x, Tendsto (fun n => EuclideanGradient (χ n) x) atTop (𝓝 0)) := by
  obtain ⟨C, hC, hb⟩ := shrinkingCollisionCutoff_gradientInverseBound (ι := ι)
  refine ⟨shrinkingCollisionCutoff, C, hC,
    shrinkingCollisionCutoff_smooth,
    shrinkingCollisionCutoff_unitBounds,
    shrinkingCollisionCutoff_vanishes,
    shrinkingCollisionCutoff_one,
    shrinkingCollisionCutoff_pointwiseLimit, hb, ?_⟩
  intro x
  by_cases hx : x = 0
  · subst x
    simpa [shrinkingCollisionCutoff_gradient,
      spatialBump_gradient_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : EuclideanSpace ℝ ι)) atTop (𝓝 0))
  · exact shrinkingCollisionCutoff_gradient_pointwiseLimit x hx

end RelativeCollisionCutoffs

-- [TABLET NODE: RelativeCollisionCutoffs]
theorem RelativeCollisionCutoffs {d N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    ∃ (χ : ℕ → ParticleConfig d N → ℝ) (η : ℕ → OneParticle d → ℝ) (C : ℝ),
      0 ≤ C ∧
      (∀ n, ContDiff ℝ ∞ (χ n)) ∧
      (∀ n X, 0 ≤ χ n X ∧ χ n X ≤ 1) ∧
      (∀ (n : ℕ) X, ‖ParticlePosition X i - ParticlePosition X j‖ ≤
        1 / ((n : ℝ) + 1) → χ n X = 0) ∧
      (∀ (n : ℕ) X, 2 / ((n : ℝ) + 1) ≤
        ‖ParticlePosition X i - ParticlePosition X j‖ → χ n X = 1) ∧
      (∀ X, ParticlePosition X i ≠ ParticlePosition X j →
        Tendsto (fun n => χ n X) atTop (𝓝 (1 : ℝ))) ∧
      (∀ n X, ‖EuclideanGradient (χ n) X‖ ≤
        C / ‖ParticlePosition X i - ParticlePosition X j‖) ∧
      (∀ X, Tendsto (fun n => EuclideanGradient (χ n) X) atTop (𝓝 0)) ∧
      (∀ n X, χ n X = η n (ParticlePosition X i - ParticlePosition X j) ∧
        ‖EuclideanGradient (χ n) X‖^2 =
          2 * ‖EuclideanGradient (η n) (ParticlePosition X i - ParticlePosition X j)‖^2) := by
-- BODY
  obtain ⟨e, he, _, _⟩ := RelativePairCoordinates (d := d) i j hij
  let Z := EuclideanSpace ℝ {p : Fin N × Fin d // p.1 ≠ i}
  let l : OneParticle d →ₗᵢ[ℝ] WithLp 2 (OneParticle d × Z) :=
    { toFun := fun u => WithLp.toLp 2 (u, 0)
      map_add' := by intro u v; rw [← WithLp.toLp_add]; congr 1; simp
      map_smul' := by
        intro r u
        simp only [RingHom.id_apply]
        rw [← WithLp.toLp_smul]
        congr 1
        simp
      norm_map' := fun u => WithLp.norm_toLp_fst _ _ _ u }
  let p : ParticleConfig d N →L[ℝ] OneParticle d :=
    (WithLp.fstL 2 ℝ (OneParticle d) Z).comp e.toContinuousLinearEquiv.toContinuousLinearMap
  let D : ParticleConfig d N →L[ℝ] OneParticle d := Real.sqrt 2 • p
  let E := fun v : OneParticle d => Real.sqrt 2 • e.symm (l v)
  have hD (X : ParticleConfig d N) : D X = ParticlePosition X i - ParticlePosition X j := by
    ext k
    change Real.sqrt 2 * (WithLp.ofLp (e X)).1 k = X (i,k) - X (j,k)
    rw [he]
    have hs : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
  have hEn (v : OneParticle d) : ‖E v‖ = Real.sqrt 2 * ‖v‖ := by
    simp only [E, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2),
      LinearIsometryEquiv.norm_map, LinearIsometry.norm_map]
  have hEi (v : OneParticle d) (X : ParticleConfig d N) :
      inner ℝ (E v) X = inner ℝ v (D X) := by
    have hh := e.inner_map_map (e.symm (l v)) X
    rw [e.apply_symm_apply] at hh
    simp only [WithLp.prod_inner_apply, inner_zero_left, add_zero] at hh
    have hh' : inner ℝ (e.symm (l v)) X = inner ℝ v (p X) := by
      simpa [l, p] using hh.symm
    change inner ℝ (Real.sqrt 2 • e.symm (l v)) X = inner ℝ v (Real.sqrt 2 • p X)
    rw [real_inner_smul_left, real_inner_smul_right, hh']
  have hgrad (g : OneParticle d → ℝ) (hg : Differentiable ℝ g) (X : ParticleConfig d N) :
      EuclideanGradient (g ∘ D) X = E (EuclideanGradient g (D X)) := by
    change gradient (g ∘ D) X = E (gradient g (D X))
    apply (InnerProductSpace.toDual ℝ (ParticleConfig d N)).injective
    rw [toDual_gradient, fderiv_comp X (hg _) D.differentiableAt, ContinuousLinearMap.fderiv]
    ext Y
    simp only [ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply]
    rw [hEi, ← toDual_gradient]
    rfl
  obtain ⟨η, C, hC, hηs, hηu, hηv, hηo, hηl, hηb, hηg⟩ :=
    RelativeCollisionCutoffs.scalarCutoffs (ι := Fin d)
  let χ := fun n => η n ∘ D
  refine ⟨χ, η, Real.sqrt 2 * C, mul_nonneg (Real.sqrt_nonneg _) hC, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (hηs n).comp D.contDiff
  · intro n X
    exact hηu n (D X)
  · intro n X hX
    exact hηv n (D X) (by simpa only [hD] using hX)
  · intro n X hX
    exact hηo n (D X) (by simpa only [hD] using hX)
  · intro X hX
    exact hηl (D X) (by rw [hD]; exact sub_ne_zero.mpr hX)
  · intro n X
    dsimp only [χ]
    rw [hgrad _ ((hηs n).differentiable (by simp)), hEn, hD]
    exact (mul_le_mul_of_nonneg_left (hηb n _) (Real.sqrt_nonneg 2)).trans_eq (by ring)
  · intro X
    have hEc : Continuous E := e.symm.continuous.comp l.continuous |>.const_smul (Real.sqrt 2)
    have ht := hEc.continuousAt.tendsto.comp (hηg (D X))
    have hz : E 0 = 0 := by simp [E]
    simpa only [Function.comp_def, ← hgrad _ ((hηs _).differentiable (by simp)), hz, χ] using ht
  · intro n X
    refine ⟨by simp only [χ, Function.comp_def, hD], ?_⟩
    dsimp only [χ]
    rw [hgrad _ ((hηs n).differentiable (by simp)), hEn, hD, mul_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
