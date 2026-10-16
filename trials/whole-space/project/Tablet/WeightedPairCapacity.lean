import Tablet.RelativePairCoordinates
import Tablet.EuclideanHardy
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
set_option maxHeartbeats 1600000
open MeasureTheory Set

namespace WeightedPairCapacity
private abbrev Config (N d : ℕ) := ParticleConfig d N
private abbrev RowRemainder (N d : ℕ) (i : Fin N) := {p : Fin N × Fin d // p.1 ≠ i}
private noncomputable def chosenCoordinates {N d : ℕ} (i j : Fin N) (hij : i ≠ j) :
    Config N d ≃ₗᵢ[ℝ] WithLp 2
      (OneParticle d × EuclideanSpace ℝ (RowRemainder N d i)) :=
  Classical.choose (RelativePairCoordinates (d := d) i j hij)
private noncomputable def relativePairSplit {N d : ℕ} (i j : Fin N) (hij : i ≠ j) :
    Config N d ≃ᵐ (OneParticle d × EuclideanSpace ℝ (RowRemainder N d i)) :=
  (chosenCoordinates i j hij).toMeasurableEquiv.trans (MeasurableEquiv.toLp 2 _).symm
private lemma relativePairSplit_volumePreserving {N d : ℕ} (i j : Fin N) (hij : i ≠ j) :
    MeasurePreserving (relativePairSplit (d := d) i j hij) volume volume :=
  (Classical.choose_spec (RelativePairCoordinates (d := d) i j hij)).2.1
private lemma relativePairSplit_first {N d : ℕ} (i j : Fin N) (hij : i ≠ j)
    (x : Config N d) (k : Fin d) :
    (relativePairSplit i j hij x).1 k = (x (i,k)-x (j,k))/Real.sqrt 2 :=
  (Classical.choose_spec (RelativePairCoordinates (d := d) i j hij)).1 x k
private noncomputable abbrev particle {N d : ℕ} (x : Config N d) (i : Fin N) := ParticlePosition x i
private lemma ordinary_gradient_norm_eq_fderiv {N d : ℕ} (f : Config N d → ℝ)
    (x : Config N d) : ‖gradient f x‖ = ‖fderiv ℝ f x‖ :=
  (InnerProductSpace.toDual ℝ (Config N d)).symm.norm_map _
private lemma relativePair_inverse_square {N d : ℕ} (i j : Fin N) (hij : i ≠ j)
    (x : Config N d) :
    (‖particle x i - particle x j‖^2)⁻¹ =
      (1/2 : ℝ) * (‖(relativePairSplit i j hij x).1‖^2)⁻¹ := by
  have he : ‖particle x i - particle x j‖^2 =
      2 * ‖(relativePairSplit i j hij x).1‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [relativePairSplit_first]
    change (x (i,k)-x (j,k))^2 = 2*((x (i,k)-x (j,k))/Real.sqrt 2)^2
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    ring
  rw [he, mul_inv_rev]
  ring
private lemma relativePair_inverse_square_fubini {N d : ℕ} (i j : Fin N) (hij : i ≠ j)
    (ψ : Config N d → ℝ)
    (hψ : Integrable (fun x => (ψ x)^2 / ‖particle x i-particle x j‖^2) volume) :
    (∫ x, (ψ x)^2 / ‖particle x i-particle x j‖^2) =
      ∫ z, ∫ u, (1/2 : ℝ) * (ψ ((relativePairSplit i j hij).symm (u,z)))^2 / ‖u‖^2 := by
  have hh := (Classical.choose_spec (RelativePairCoordinates (d := d) i j hij)).2.2 _ hψ
  change (∫ x, (ψ x)^2 / ‖particle x i-particle x j‖^2) =
    ∫ z, ∫ u, (ψ ((relativePairSplit i j hij).symm (u,z)))^2 /
      ‖particle ((relativePairSplit i j hij).symm (u,z)) i -
        particle ((relativePairSplit i j hij).symm (u,z)) j‖^2 at hh
  rw [hh]
  apply integral_congr_ae
  filter_upwards [] with z
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [div_eq_mul_inv]
  rw [relativePair_inverse_square i j hij]
  simp only [MeasurableEquiv.apply_symm_apply]
  ring
private noncomputable def prodFirstIsometry (U V : Type*) [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] : U →ₗᵢ[ℝ] WithLp 2 (U × V) where
  toFun := fun u => WithLp.toLp 2 (u,0)
  map_add' := by intro u v; rw [← WithLp.toLp_add]; congr 1; simp
  map_smul' := by intro r u; simp only [RingHom.id_apply]; rw [← WithLp.toLp_smul]; congr 1; simp
  norm_map' := fun u => WithLp.norm_toLp_fst _ _ _ u

private noncomputable def pairFiberLinear {N d : ℕ} (i j : Fin N) (hij : i ≠ j) :
    EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ] Config N d :=
  (chosenCoordinates i j hij).symm.toLinearIsometry.comp
    (prodFirstIsometry _ _)

private noncomputable def pairFiber {N d : ℕ} (i j : Fin N) (hij : i ≠ j)
    (z : EuclideanSpace ℝ (RowRemainder N d i)) (u : EuclideanSpace ℝ (Fin d)) : Config N d :=
  pairFiberLinear i j hij u +
    (chosenCoordinates i j hij).symm (WithLp.toLp 2 (0,z))

private theorem pairFiber_eq_split {N d : ℕ} (i j : Fin N) (hij : i ≠ j)
    (z : EuclideanSpace ℝ (RowRemainder N d i)) (u : EuclideanSpace ℝ (Fin d)) :
    pairFiber i j hij z u = (relativePairSplit i j hij).symm (u,z) := by
  change (chosenCoordinates i j hij).symm (WithLp.toLp 2 (u,0)) +
    (chosenCoordinates i j hij).symm (WithLp.toLp 2 (0,z)) =
    (chosenCoordinates i j hij).symm (WithLp.toLp 2 (u,z))
  rw [← LinearIsometryEquiv.map_add]
  congr 1
  rw [← WithLp.toLp_add]
  congr 1
  simp

private theorem pairFiber_isometry {N d : ℕ} (i j : Fin N) (hij : i ≠ j)
    (z : EuclideanSpace ℝ (RowRemainder N d i)) : Isometry (pairFiber i j hij z) := by
  apply Isometry.of_dist_eq
  intro u v
  simp only [pairFiber, dist_add_right]
  exact (pairFiberLinear i j hij).isometry.dist_eq u v

private theorem pairFiber_hasFDerivAt {N d : ℕ} (i j : Fin N) (hij : i ≠ j)
    (z : EuclideanSpace ℝ (RowRemainder N d i)) (u : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (pairFiber i j hij z) (pairFiberLinear i j hij).toContinuousLinearMap u := by
  exact (pairFiberLinear i j hij).toContinuousLinearMap.hasFDerivAt.add_const _

private theorem pairFiber_contDiff {N d : ℕ} (i j : Fin N) (hij : i ≠ j)
    (z : EuclideanSpace ℝ (RowRemainder N d i)) : ContDiff ℝ 1 (pairFiber i j hij z) :=
  (pairFiberLinear i j hij).toContinuousLinearMap.contDiff.add contDiff_const

private theorem pairFiber_compactSupport {N d : ℕ} (i j : Fin N) (hij : i ≠ j)
    (z : EuclideanSpace ℝ (RowRemainder N d i)) (ψ : Config N d → ℝ)
    (hψ : HasCompactSupport ψ) : HasCompactSupport (ψ ∘ pairFiber i j hij z) := by
  have hi := pairFiber_isometry i j hij z
  exact (hi.isClosedEmbedding.isCompact_preimage hψ).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_comp_subset_preimage ψ hi.continuous)

private theorem pairFiber_gradient_bound {N d : ℕ} (i j : Fin N) (hij : i ≠ j)
    (z : EuclideanSpace ℝ (RowRemainder N d i)) (ψ : Config N d → ℝ)
    (u : EuclideanSpace ℝ (Fin d)) (hψ : DifferentiableAt ℝ ψ (pairFiber i j hij z u)) :
    ‖gradient (ψ ∘ pairFiber i j hij z) u‖ ≤ ‖gradient ψ (pairFiber i j hij z u)‖ := by
  rw [show ‖gradient (ψ ∘ pairFiber i j hij z) u‖ = ‖fderiv ℝ (ψ ∘ pairFiber i j hij z) u‖ from
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.norm_map _]
  rw [ordinary_gradient_norm_eq_fderiv]
  rw [fderiv_comp u hψ (pairFiber_hasFDerivAt i j hij z u).differentiableAt,
    (pairFiber_hasFDerivAt i j hij z u).fderiv]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
    simpa using mul_le_mul_of_nonneg_left (pairFiberLinear i j hij).norm_toContinuousLinearMap_le
      (norm_nonneg (fderiv ℝ ψ (pairFiber i j hij z u))))

private theorem pairFiber_hardy {N d : ℕ} (hd : 3 ≤ d) (i j : Fin N) (hij : i ≠ j)
    (z : EuclideanSpace ℝ (RowRemainder N d i)) (ψ : Config N d → ℝ)
    (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) :
    (((d : ℝ)-2)^2/4)*(∫ u, (ψ (pairFiber i j hij z u))^2/‖u‖^2) ≤
      ∫ u, ‖gradient (ψ ∘ pairFiber i j hij z) u‖^2 := by
  exact (EuclideanHardy hd (ψ ∘ pairFiber i j hij z)
    (hψ.comp (pairFiber_contDiff i j hij z)) (pairFiber_compactSupport i j hij z ψ hcψ)).2


private theorem ordinary_gradient_energy_integrable {ι : Type*} [Fintype ι]
    (ψ : EuclideanSpace ℝ ι → ℝ) (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) :
    Integrable (fun x => ‖gradient ψ x‖^2) volume := by
  let b := EuclideanSpace.basisFun ι ℝ
  let q := fun k x => fderiv ℝ ψ x (b k)
  have hqC (k : ι) : Continuous (q k) :=
    (hψ.continuous_fderiv_apply (by norm_num)).comp (continuous_id.prodMk continuous_const)
  have hqS (k : ι) : HasCompactSupport (q k) := hcψ.fderiv_apply ℝ (b k)
  have hqI (k : ι) : Integrable (fun x => (q k x)^2) volume := by
    have hh : Integrable (fun x => q k x*q k x) (volume : Measure (EuclideanSpace ℝ ι)) :=
      (hqC k |>.mul (hqC k)).integrable_of_hasCompactSupport (hqS k).mul_left
    simpa only [pow_two] using hh
  have heq (x : EuclideanSpace ℝ ι) : (∑ k, (q k x)^2) = ‖gradient ψ x‖^2 := by
    have hi (k : ι) : q k x = inner ℝ (gradient ψ x) (b k) := by
      have h := congrArg (fun L : EuclideanSpace ℝ ι →L[ℝ] ℝ => L (b k))
        (toDual_gradient (𝕜:=ℝ) (f:=ψ) (x:=x))
      simpa [q, InnerProductSpace.toDual_apply_apply] using h.symm
    calc
      _ = ∑ k, ‖inner ℝ (gradient ψ x) (b k)‖^2 := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hi, Real.norm_eq_abs, sq_abs]
      _ = _ := b.sum_sq_norm_inner_left (gradient ψ x)
  simpa only [heq] using integrable_finsetSum Finset.univ (fun k _ => hqI k)

private noncomputable def relativeHardyWeight {N d : ℕ} (i j : Fin N) (hij : i ≠ j)
    (ψ : Config N d → ℝ)
    (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (RowRemainder N d i)) : ℝ :=
  (ψ ((relativePairSplit i j hij).symm p))^2/‖p.1‖^2

private theorem relativeHardyWeight_integrable {N d : ℕ} (hd : 3 ≤ d) (i j : Fin N) (hij : i ≠ j)
    (ψ : Config N d → ℝ) (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) :
    Integrable (relativeHardyWeight i j hij ψ) volume := by
  let C := (((d : ℝ)-2)^2/4)
  have hC : 0 < C := by
    have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have hs : 0 < (d : ℝ)-2 := by linarith
    dsimp [C]
    positivity
  let G := fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (RowRemainder N d i) =>
    ‖gradient ψ ((relativePairSplit i j hij).symm p)‖^2
  have hG : Integrable G volume :=
    (relativePairSplit_volumePreserving i j hij).symm.integrable_comp_of_integrable
      (ordinary_gradient_energy_integrable ψ hψ hcψ)
  have hWmeas : AEStronglyMeasurable (relativeHardyWeight i j hij ψ) volume := by
    apply Measurable.aestronglyMeasurable
    exact ((hψ.continuous.measurable.comp (relativePairSplit i j hij).symm.measurable).pow_const 2).div
      ((continuous_norm.measurable.comp measurable_fst).pow_const 2)
  have hWI (z : EuclideanSpace ℝ (RowRemainder N d i)) :
      Integrable (fun u => relativeHardyWeight i j hij ψ (u,z)) volume := by
    simpa only [relativeHardyWeight, ← pairFiber_eq_split, Function.comp_apply] using
      (EuclideanHardy hd (ψ ∘ pairFiber i j hij z)
        (hψ.comp (pairFiber_contDiff i j hij z))
        (pairFiber_compactSupport i j hij z ψ hcψ)).1
  have hb : ∀ᵐ z ∂volume,
      (∫ u, relativeHardyWeight i j hij ψ (u,z)) ≤ (1/C)*(∫ u, G (u,z)) := by
    filter_upwards [hG.prod_left_ae] with z hz
    have hFI := ordinary_gradient_energy_integrable (ψ ∘ pairFiber i j hij z)
      (hψ.comp (pairFiber_contDiff i j hij z)) (pairFiber_compactSupport i j hij z ψ hcψ)
    have hg : (∫ u, ‖gradient (ψ ∘ pairFiber i j hij z) u‖^2) ≤ ∫ u, G (u,z) := by
      apply integral_mono hFI hz
      intro u
      change ‖gradient (ψ ∘ pairFiber i j hij z) u‖^2 ≤
        ‖gradient ψ ((relativePairSplit i j hij).symm (u,z))‖^2
      rw [← pairFiber_eq_split]
      exact pow_le_pow_left₀ (norm_nonneg _) (pairFiber_gradient_bound i j hij z ψ u
        (hψ.differentiable (by norm_num) _)) 2
    have hh := (pairFiber_hardy hd i j hij z ψ hψ hcψ).trans hg
    have hrr : C*(∫ u, relativeHardyWeight i j hij ψ (u,z)) ≤ ∫ u, G (u,z) := by
      simpa only [C, relativeHardyWeight, pairFiber_eq_split, Function.comp_apply] using hh
    have hres : (∫ u, relativeHardyWeight i j hij ψ (u,z)) ≤ (∫ u, G (u,z))/C :=
      (le_div_iff₀ hC).2 (by simpa only [mul_comm] using hrr)
    simpa [div_eq_mul_inv, mul_comm] using hres
  have hi : Integrable (fun z => ∫ u, ‖relativeHardyWeight i j hij ψ (u,z)‖) volume := by
    apply (hG.integral_prod_right.const_mul (1/C)).mono'
      hWmeas.norm.prod_swap.integral_prod_right'
    filter_upwards [hb] with z hz
    have hnn (u : EuclideanSpace ℝ (Fin d)) : 0 ≤ relativeHardyWeight i j hij ψ (u,z) := by
      unfold relativeHardyWeight
      positivity
    change ‖∫ u, ‖relativeHardyWeight i j hij ψ (u,z)‖‖ ≤ (1/C)*(∫ u, G (u,z))
    have heq : (∫ u, ‖relativeHardyWeight i j hij ψ (u,z)‖) =
        ∫ u, relativeHardyWeight i j hij ψ (u,z) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun u => Real.norm_of_nonneg (hnn u))
    rw [heq, Real.norm_of_nonneg (show 0 ≤ ∫ u, relativeHardyWeight i j hij ψ (u,z) from integral_nonneg hnn)]
    exact hz
  exact (integrable_prod_iff' hWmeas).2 ⟨Filter.Eventually.of_forall hWI, hi⟩


private theorem pair_inverse_square_integrable {N d : ℕ} (hd : 3 ≤ d) (i j : Fin N) (hij : i ≠ j)
    (ψ : Config N d → ℝ) (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) :
    Integrable (fun x => (ψ x)^2/‖particle x i-particle x j‖^2) volume := by
  have hh := (relativePairSplit_volumePreserving i j hij).integrable_comp_of_integrable
    ((relativeHardyWeight_integrable hd i j hij ψ hψ hcψ).const_mul (1/2 : ℝ))
  convert hh using 1
  funext x
  simp only [Function.comp_apply, relativeHardyWeight, MeasurableEquiv.symm_apply_apply, div_eq_mul_inv]
  rw [relativePair_inverse_square i j hij]
  ring

private theorem pair_inverse_square_hardy {N d : ℕ} (hd : 3 ≤ d) (i j : Fin N) (hij : i ≠ j)
    (ψ : Config N d → ℝ) (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) :
    (∫ x, (ψ x)^2/‖particle x i-particle x j‖^2) ≤
      (2/((d : ℝ)-2)^2)*(∫ x, ‖gradient ψ x‖^2) := by
  let C := (((d : ℝ)-2)^2/4)
  let G := fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (RowRemainder N d i) =>
    ‖gradient ψ ((relativePairSplit i j hij).symm p)‖^2
  have hG : Integrable G volume :=
    (relativePairSplit_volumePreserving i j hij).symm.integrable_comp_of_integrable
      (ordinary_gradient_energy_integrable ψ hψ hcψ)
  have hW := relativeHardyWeight_integrable hd i j hij ψ hψ hcψ
  have hb : ∀ᵐ z ∂volume, C*(∫ u, relativeHardyWeight i j hij ψ (u,z)) ≤ ∫ u, G (u,z) := by
    filter_upwards [hG.prod_left_ae] with z hz
    have hFI := ordinary_gradient_energy_integrable (ψ ∘ pairFiber i j hij z)
      (hψ.comp (pairFiber_contDiff i j hij z)) (pairFiber_compactSupport i j hij z ψ hcψ)
    have hg : (∫ u, ‖gradient (ψ ∘ pairFiber i j hij z) u‖^2) ≤ ∫ u, G (u,z) := by
      apply integral_mono hFI hz
      intro u
      change ‖gradient (ψ ∘ pairFiber i j hij z) u‖^2 ≤
        ‖gradient ψ ((relativePairSplit i j hij).symm (u,z))‖^2
      rw [← pairFiber_eq_split]
      exact pow_le_pow_left₀ (norm_nonneg _) (pairFiber_gradient_bound i j hij z ψ u
        (hψ.differentiable (by norm_num) _)) 2
    simpa only [C, relativeHardyWeight, pairFiber_eq_split, Function.comp_apply] using
      (pairFiber_hardy hd i j hij z ψ hψ hcψ).trans hg
  have hm := integral_mono_ae (hW.integral_prod_right.const_mul C) hG.integral_prod_right hb
  rw [integral_const_mul] at hm
  have hGE : (∫ z, ∫ u, G (u,z)) = ∫ x, ‖gradient ψ x‖^2 := by
    rw [← integral_prod_symm G hG]
    exact (relativePairSplit_volumePreserving i j hij).symm.integral_comp
      (relativePairSplit i j hij).symm.measurableEmbedding (fun x => ‖gradient ψ x‖^2)
  rw [hGE] at hm
  have hpair : (∫ x, (ψ x)^2/‖particle x i-particle x j‖^2) =
      (1/2 : ℝ)*(∫ z, ∫ u, relativeHardyWeight i j hij ψ (u,z)) := by
    rw [relativePair_inverse_square_fubini i j hij ψ (pair_inverse_square_integrable hd i j hij ψ hψ hcψ)]
    simp only [relativeHardyWeight, mul_div_assoc]
    simp_rw [integral_const_mul]
  have hcoef : (((d : ℝ)-2)^2/2)*(∫ x, (ψ x)^2/‖particle x i-particle x j‖^2) =
      C*(∫ z, ∫ u, relativeHardyWeight i j hij ψ (u,z)) := by
    rw [hpair]
    dsimp [C]
    ring
  have hf : (((d : ℝ)-2)^2/2)*(∫ x, (ψ x)^2/‖particle x i-particle x j‖^2) ≤
      ∫ x, ‖gradient ψ x‖^2 := by rw [hcoef]; exact hm
  have hD : 0 < ((d : ℝ)-2)^2 := by
    have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have hs : 0 < (d : ℝ)-2 := by linarith
    positivity
  have ht : (∫ x, (ψ x)^2/‖particle x i-particle x j‖^2) ≤
      (2*(∫ x, ‖gradient ψ x‖^2))/((d : ℝ)-2)^2 := by
    apply (le_div_iff₀ hD).2
    nlinarith [hf]
  simpa only [div_mul_eq_mul_div] using ht

end WeightedPairCapacity

-- [TABLET NODE: WeightedPairCapacity]
theorem WeightedPairCapacity {d N : ℕ} (hd : 3 ≤ d) (i j : Fin N) (hij : i ≠ j)
    (f : ParticleConfig d N → ℝ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (r : ParticleConfig d N → ℝ) (hr : Measurable r) (hrn : ∀ X, 0 ≤ r X)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ X ∈ tsupport f, r X ≤ M) :
    let P := volume.withDensity (fun X => ENNReal.ofReal (r X))
    Integrable (fun X => (f X)^2 / ‖ParticlePosition X i - ParticlePosition X j‖^2) P ∧
      (∫ X, (f X)^2 / ‖ParticlePosition X i - ParticlePosition X j‖^2 ∂P) ≤
        M * (2 / ((d : ℝ) - 2)^2) * (∫ X, ‖EuclideanGradient f X‖^2) := by
-- BODY
  dsimp only
  let q := fun X => (f X)^2 / ‖ParticlePosition X i - ParticlePosition X j‖^2
  have hq : Integrable q volume := WeightedPairCapacity.pair_inverse_square_integrable hd i j hij f hf hc
  have hqn (X : ParticleConfig d N) : 0 ≤ q X := by dsimp [q]; positivity
  have hzero (X : ParticleConfig d N) (hX : X ∉ tsupport f) : q X = 0 := by
    simp [q, image_eq_zero_of_notMem_tsupport hX]
  have hqr : Integrable (fun X => r X * q X) volume := by
    apply (hq.const_mul M).mono'
    · exact hr.aestronglyMeasurable.mul hq.aestronglyMeasurable
    · filter_upwards [] with X
      rw [Real.norm_of_nonneg (mul_nonneg (hrn X) (hqn X))]
      by_cases hX : X ∈ tsupport f
      · exact mul_le_mul_of_nonneg_right (hb X hX) (hqn X)
      · simp [hzero X hX]
  have hPw : Integrable q (volume.withDensity (fun X => ENNReal.ofReal (r X))) := by
    rw [integrable_withDensity_iff hr.ennreal_ofReal
      (Filter.Eventually.of_forall (fun X => ENNReal.ofReal_lt_top))]
    simpa only [ENNReal.toReal_ofReal (hrn _), smul_eq_mul, mul_comm] using hqr
  refine ⟨hPw, ?_⟩
  change (∫ X, q X ∂volume.withDensity (fun X => ENNReal.ofReal (r X))) ≤ _
  rw [integral_withDensity_eq_integral_toReal_smul hr.ennreal_ofReal
    (Filter.Eventually.of_forall (fun X => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hrn _), smul_eq_mul]
  have hm : (∫ X, r X * q X) ≤ ∫ X, M * q X := by
    apply integral_mono hqr (hq.const_mul M)
    intro X
    by_cases hX : X ∈ tsupport f
    · exact mul_le_mul_of_nonneg_right (hb X hX) (hqn X)
    · simp [hzero X hX]
  rw [integral_const_mul] at hm
  exact hm.trans (by
    simpa only [mul_assoc, q, WeightedPairCapacity.particle, EuclideanGradient] using
      mul_le_mul_of_nonneg_left (WeightedPairCapacity.pair_inverse_square_hardy hd i j hij f hf hc) hM)
