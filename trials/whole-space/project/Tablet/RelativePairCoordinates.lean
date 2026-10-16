import Tablet.ParticlePosition
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Tactic

set_option maxHeartbeats 1600000
open MeasureTheory
namespace RelativePairCoordinates

private abbrev Config (N d : ℕ) := EuclideanSpace ℝ (Fin N × Fin d)

private noncomputable def rotatePair {N d : ℕ} (i j : Fin N) (x : Config N d) : Config N d :=
  WithLp.toLp 2 (fun p => if p.1 = i then (x (i,p.2) - x (j,p.2)) / Real.sqrt 2
    else if p.1 = j then (x (i,p.2) + x (j,p.2)) / Real.sqrt 2 else x p)

private theorem rotatePair_first {N d : ℕ} (i j : Fin N) (x : Config N d) (k : Fin d) :
    rotatePair i j x (i,k) = (x (i,k) - x (j,k)) / Real.sqrt 2 := by
  simp [rotatePair]

private theorem rotatePair_second {N d : ℕ} (i j : Fin N) (hij : i ≠ j)
    (x : Config N d) (k : Fin d) :
    rotatePair i j x (j,k) = (x (i,k) + x (j,k)) / Real.sqrt 2 := by
  simp [rotatePair, hij.symm]

private theorem rotatePair_other {N d : ℕ} (i j : Fin N) (x : Config N d)
    (p : Fin N × Fin d) (hi : p.1 ≠ i) (hj : p.1 ≠ j) :
    rotatePair i j x p = x p := by simp [rotatePair, hi, hj]

private theorem relative_scalar_norm_identity (a b : ℝ) :
    ((a-b) / Real.sqrt 2)^2 + ((a+b) / Real.sqrt 2)^2 = a^2+b^2 := by
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  nlinarith [sq_nonneg (a+b), sq_nonneg (a-b)]

private theorem sum_two_rows {N : ℕ} (i j : Fin N) (hij : i ≠ j) (f : Fin N → ℝ) :
    (∑ a, f a) = f i + f j + ∑ a ∈ (Finset.univ.erase i).erase j, f a := by
  have hi : i ∈ (Finset.univ : Finset (Fin N)) := Finset.mem_univ i
  have hj : j ∈ (Finset.univ.erase i : Finset (Fin N)) := by simp [hij.symm]
  rw [← Finset.add_sum_erase _ _ hi, ← Finset.add_sum_erase _ _ hj]
  ring

private theorem rotatePair_norm {N d : ℕ} (i j : Fin N) (hij : i ≠ j) (x : Config N d) :
    ‖rotatePair i j x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [Fintype.sum_prod_type]
  rw [sum_two_rows i j hij, sum_two_rows i j hij]
  have hp : (∑ k, (rotatePair i j x (i,k))^2) +
      (∑ k, (rotatePair i j x (j,k))^2) =
      (∑ k, (x (i,k))^2) + (∑ k, (x (j,k))^2) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [rotatePair_first, rotatePair_second i j hij]
    exact relative_scalar_norm_identity _ _
  rw [hp]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  have hi : a ≠ i := by simpa using (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
  have hj : a ≠ j := (Finset.mem_erase.mp ha).1
  apply Finset.sum_congr rfl
  intro k hk
  rw [rotatePair_other i j x (a,k) hi hj]

private noncomputable def pairLinearMap {N d : ℕ} (i j : Fin N) : Config N d →ₗ[ℝ] Config N d where
  toFun := rotatePair i j
  map_add' := by
    intro x y
    ext p
    simp only [rotatePair, PiLp.add_apply]
    split_ifs <;> ring
  map_smul' := by
    intro r x
    ext p
    simp only [rotatePair, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

private noncomputable def pairLinearIsometry {N d : ℕ} (i j : Fin N) (hij : i ≠ j) :
    Config N d →ₗᵢ[ℝ] Config N d :=
  { pairLinearMap i j with norm_map' := rotatePair_norm i j hij }

private noncomputable def pairOrthogonalEquiv {N d : ℕ} (i j : Fin N) (hij : i ≠ j) :
    Config N d ≃ₗᵢ[ℝ] Config N d :=
  (pairLinearIsometry i j hij).toLinearIsometryEquiv rfl

private theorem pairOrthogonalEquiv_apply {N d : ℕ} (i j : Fin N) (hij : i ≠ j)
    (x : Config N d) : pairOrthogonalEquiv i j hij x = rotatePair i j x := rfl

private theorem pairOrthogonal_volumePreserving {N d : ℕ} (i j : Fin N) (hij : i ≠ j) :
    MeasurePreserving (pairOrthogonalEquiv (d:=d) i j hij) volume volume :=
  (pairOrthogonalEquiv i j hij).measurePreserving


private theorem pairOrthogonal_integral {N d : ℕ} (i j : Fin N) (hij : i ≠ j)
    (f : Config N d → ℝ) :
    (∫ x, f (pairOrthogonalEquiv i j hij x)) = ∫ x, f x := by
  exact (pairOrthogonal_volumePreserving i j hij).integral_comp
    (pairOrthogonalEquiv i j hij).toHomeomorph.measurableEmbedding f

private theorem pairOrthogonal_fderiv_norm {N d : ℕ} (i j : Fin N) (hij : i ≠ j)
    (f : Config N d → ℝ) (x : Config N d)
    (hf : DifferentiableAt ℝ f (pairOrthogonalEquiv i j hij x)) :
    ‖fderiv ℝ (f ∘ pairOrthogonalEquiv i j hij) x‖ =
      ‖fderiv ℝ f (pairOrthogonalEquiv i j hij x)‖ := by
  rw [fderiv_comp x hf (pairOrthogonalEquiv i j hij).toContinuousLinearEquiv.toContinuousLinearMap.differentiableAt]
  change ‖(fderiv ℝ f (pairOrthogonalEquiv i j hij x)).comp
    (fderiv ℝ (pairOrthogonalEquiv i j hij).toContinuousLinearEquiv.toContinuousLinearMap x)‖ = _
  rw [ContinuousLinearMap.fderiv]
  exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ _

private theorem ordinary_gradient_norm_eq_fderiv {N d : ℕ} (f : Config N d → ℝ)
    (x : Config N d) : ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  exact (InnerProductSpace.toDual ℝ (Config N d)).symm.norm_map _

private theorem pairOrthogonal_gradient_norm {N d : ℕ} (i j : Fin N) (hij : i ≠ j)
    (f : Config N d → ℝ) (x : Config N d)
    (hf : DifferentiableAt ℝ f (pairOrthogonalEquiv i j hij x)) :
    ‖gradient (f ∘ pairOrthogonalEquiv i j hij) x‖ =
      ‖gradient f (pairOrthogonalEquiv i j hij x)‖ := by
  rw [ordinary_gradient_norm_eq_fderiv, ordinary_gradient_norm_eq_fderiv]
  exact pairOrthogonal_fderiv_norm i j hij f x hf

private abbrev RowRemainder (N d : ℕ) (i : Fin N) := {p : Fin N × Fin d // p.1 ≠ i}

private noncomputable def rowIndexEquiv {N d : ℕ} (i : Fin N) :
    Fin d ⊕ RowRemainder N d i ≃ Fin N × Fin d where
  toFun := fun p => p.elim (fun k => (i,k)) Subtype.val
  invFun := fun p => if h : p.1 = i then Sum.inl p.2 else Sum.inr ⟨p,h⟩
  left_inv := by
    intro p
    cases p with
    | inl k => simp
    | inr p => simp [p.2]
  right_inv := by
    intro p
    dsimp only
    split_ifs with h
    · exact Prod.ext h.symm rfl
    · rfl

private noncomputable def rowSplitIsometry {N d : ℕ} (i : Fin N) :
    Config N d ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (RowRemainder N d i)) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (rowIndexEquiv i).symm).trans
    (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ => ℝ))

private noncomputable def relativePairSplit {N d : ℕ} (i j : Fin N) (hij : i ≠ j) :
    Config N d ≃ᵐ
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (RowRemainder N d i)) :=
  ((pairOrthogonalEquiv i j hij).trans (rowSplitIsometry i)).toMeasurableEquiv.trans
    (MeasurableEquiv.toLp 2 _).symm

private theorem relativePairSplit_volumePreserving {N d : ℕ} (i j : Fin N) (hij : i ≠ j) :
    MeasurePreserving (relativePairSplit (d:=d) i j hij) volume volume := by
  exact ((pairOrthogonalEquiv i j hij).trans (rowSplitIsometry i)).measurePreserving.trans
    (WithLp.volume_preserving_symm_measurableEquiv_toLp_prod _ _)

private theorem relativePair_fubini {N d : ℕ} (i j : Fin N) (hij : i ≠ j)
    (f : Config N d → ℝ) (hf : Integrable f volume) :
    (∫ x, f x) = ∫ z, ∫ u, f ((relativePairSplit i j hij).symm (u,z)) := by
  have hm := (relativePairSplit_volumePreserving (d:=d) i j hij).symm
  have hint : Integrable (fun p => f ((relativePairSplit i j hij).symm p)) volume :=
    (hm.integrable_comp_emb (relativePairSplit i j hij).symm.measurableEmbedding).2 hf
  rw [← hm.integral_comp (relativePairSplit i j hij).symm.measurableEmbedding f]
  exact integral_prod_symm _ hint


private noncomputable def particle {N d : ℕ} (x : Config N d) (i : Fin N) :
    EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (fun k => x (i,k))

private theorem relativePairSplit_first {N d : ℕ} (i j : Fin N) (hij : i ≠ j)
    (x : Config N d) (k : Fin d) :
    (relativePairSplit i j hij x).1 k = (x (i,k)-x (j,k))/Real.sqrt 2 := by
  change rotatePair i j x (i,k) = _
  exact rotatePair_first i j x k

private theorem relativePair_distance_square {N d : ℕ} (i j : Fin N) (hij : i ≠ j)
    (x : Config N d) :
    ‖particle x i - particle x j‖^2 = 2 * ‖(relativePairSplit i j hij x).1‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [relativePairSplit_first]
  change (x (i,k)-x (j,k))^2 = 2*((x (i,k)-x (j,k))/Real.sqrt 2)^2
  rw [div_pow, Real.sq_sqrt (by norm_num)]
  ring

private theorem relativePair_inverse_square {N d : ℕ} (i j : Fin N) (hij : i ≠ j)
    (x : Config N d) :
    (‖particle x i - particle x j‖^2)⁻¹ =
      (1/2 : ℝ) * (‖(relativePairSplit i j hij x).1‖^2)⁻¹ := by
  rw [relativePair_distance_square i j hij x, mul_inv_rev]
  ring

private theorem relativePair_inverse_square_fubini {N d : ℕ} (i j : Fin N) (hij : i ≠ j)
    (ψ : Config N d → ℝ)
    (hψ : Integrable (fun x => (ψ x)^2 / ‖particle x i-particle x j‖^2) volume) :
    (∫ x, (ψ x)^2 / ‖particle x i-particle x j‖^2) =
      ∫ z, ∫ u, (1/2 : ℝ) * (ψ ((relativePairSplit i j hij).symm (u,z)))^2 / ‖u‖^2 := by
  rw [relativePair_fubini i j hij _ hψ]
  apply integral_congr_ae
  filter_upwards [] with z
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [div_eq_mul_inv]
  rw [relativePair_inverse_square i j hij]
  simp only [MeasurableEquiv.apply_symm_apply]
  ring

end RelativePairCoordinates

-- [TABLET NODE: RelativePairCoordinates]
theorem RelativePairCoordinates {d N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    ∃ e : ParticleConfig d N ≃ₗᵢ[ℝ]
        WithLp 2 (OneParticle d ×
          EuclideanSpace ℝ {p : Fin N × Fin d // p.1 ≠ i}),
      (∀ X k, (WithLp.ofLp (e X)).1 k =
        (X (i, k) - X (j, k)) / Real.sqrt 2) ∧
      MeasurePreserving (fun X => WithLp.ofLp (e X)) volume volume ∧
      (∀ (f : ParticleConfig d N → ℝ), Integrable f volume →
        (∫ X, f X) = ∫ z, ∫ u, f (e.symm (WithLp.toLp 2 (u, z)))) := by
-- BODY
  let e := (RelativePairCoordinates.pairOrthogonalEquiv (d := d) i j hij).trans
    (RelativePairCoordinates.rowSplitIsometry i)
  refine ⟨e, ?_, ?_, ?_⟩
  · intro X k
    exact RelativePairCoordinates.relativePairSplit_first i j hij X k
  · exact RelativePairCoordinates.relativePairSplit_volumePreserving i j hij
  · intro f hf
    exact RelativePairCoordinates.relativePair_fubini i j hij f hf
