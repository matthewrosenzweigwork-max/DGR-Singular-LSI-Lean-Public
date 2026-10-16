module

public import Tablet.ParticleInsertion
public import Tablet.EuclideanDerivativeCoordinates
public import Tablet.ParticleGradientEnergyIdentity
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section
open scoped ContDiff
set_option maxHeartbeats 1500000

namespace ParticleInsertionCalculus
private noncomputable def blockInjection {d N : ℕ} (i : Fin N) :
    OneParticle d →L[ℝ] ParticleConfig d N :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 (fun jk => if jk.1 = i then z jk.2 else 0)
      map_add' := by intros; ext jk; simp only [PiLp.add_apply]; split_ifs <;> simp
      map_smul' := by intros; ext jk; simp only [PiLp.smul_apply]; split_ifs <;> simp }

private theorem affine {d N : ℕ} (X : ParticleConfig d N) (i : Fin N)
    (z : OneParticle d) : ParticleInsertion X i z = ParticleInsertion X i 0 + blockInjection i z := by
  classical
  ext jk
  simp only [ParticleInsertion, blockInjection, LinearMap.toContinuousLinearMap, PiLp.add_apply]
  split_ifs <;> simp_all

private theorem insertion_deriv {d N : ℕ} (X : ParticleConfig d N) (i : Fin N)
    (z : OneParticle d) : HasFDerivAt (ParticleInsertion X i) (blockInjection i) z := by
  have h := (blockInjection i).hasFDerivAt (x := z) |>.const_add (ParticleInsertion X i 0)
  have he : ParticleInsertion X i = fun z => ParticleInsertion X i 0 + blockInjection i z :=
    funext (affine X i)
  rw [he]
  exact h

private theorem insertion_smooth {d N : ℕ} (X : ParticleConfig d N) (i : Fin N) :
    ContDiff ℝ ∞ (ParticleInsertion X i) := by
  have he : ParticleInsertion X i = fun z => ParticleInsertion X i 0 + blockInjection i z :=
    funext (affine X i)
  rw [he]
  exact contDiff_const.add (blockInjection i).contDiff

private theorem position {d N : ℕ} (X : ParticleConfig d N) (i : Fin N)
    (z : OneParticle d) : ParticlePosition (ParticleInsertion X i z) i = z := by
  ext k
  simp [ParticleInsertion, ParticlePosition]

private theorem insertion_self {d N : ℕ} (X : ParticleConfig d N) (i : Fin N) :
    ParticleInsertion X i (ParticlePosition X i) = X := by
  classical
  ext jk
  simp only [ParticleInsertion]
  split_ifs with h
  · change X (i, jk.2) = X jk
    exact congrArg X (Prod.ext h.symm rfl)
  · rfl

private theorem closedEmbedding {d N : ℕ} (X : ParticleConfig d N) (i : Fin N) :
    Topology.IsClosedEmbedding (ParticleInsertion X i) := by
  have hp : Continuous (fun Y : ParticleConfig d N => ParticlePosition Y i) := by
    unfold ParticlePosition; fun_prop
  have hi := (insertion_smooth X i).continuous
  have hl : Function.LeftInverse (fun Y => ParticlePosition Y i) (ParticleInsertion X i) :=
    position X i
  refine ⟨hl.isEmbedding hp hi, ?_⟩
  have he : Set.range (ParticleInsertion X i) =
      {Y | ParticleInsertion X i (ParticlePosition Y i) = Y} := by
    ext Y
    constructor
    · rintro ⟨z, rfl⟩
      change ParticleInsertion X i (ParticlePosition (ParticleInsertion X i z) i) =
        ParticleInsertion X i z
      rw [position]
    · intro h
      exact ⟨ParticlePosition Y i, h⟩
  rw [he]
  exact isClosed_eq (hi.comp hp) continuous_id

private theorem injection_basis {d N : ℕ} (i : Fin N) (k : Fin d) :
    blockInjection i (EuclideanSpace.basisFun (Fin d) ℝ k) =
      EuclideanSpace.basisFun (Fin N × Fin d) ℝ (i, k) := by
  classical
  ext jk
  simp [blockInjection, EuclideanSpace.basisFun_apply, Prod.ext_iff]
  split_ifs <;> simp_all

private theorem fibre_gradient {d N : ℕ} (f : ParticleConfig d N → ℝ)
    (hf : ContDiff ℝ ∞ f) (X : ParticleConfig d N) (i : Fin N) (z : OneParticle d) :
    EuclideanGradient (fun w => f (ParticleInsertion X i w)) z =
      ParticlePosition (EuclideanGradient f (ParticleInsertion X i z)) i := by
  have hd := (hf.differentiable (by norm_num) (ParticleInsertion X i z)).hasFDerivAt
  have hc := hd.comp z (insertion_deriv X i z)
  rw [(EuclideanDerivativeCoordinates _ z).1,
    (EuclideanDerivativeCoordinates f (ParticleInsertion X i z)).1]
  ext k
  change fderiv ℝ (fun w => f (ParticleInsertion X i w)) z
      (EuclideanSpace.basisFun (Fin d) ℝ k) =
    fderiv ℝ f (ParticleInsertion X i z) (EuclideanSpace.basisFun (Fin N × Fin d) ℝ (i, k))
  change fderiv ℝ (f ∘ ParticleInsertion X i) z _ = _
  rw [hc.fderiv]
  change fderiv ℝ f _ (blockInjection i _) = _
  rw [injection_basis]
end ParticleInsertionCalculus

-- [TABLET NODE: ParticleInsertionCalculus]
theorem ParticleInsertionCalculus {d N : ℕ} :
    (∀ (X : ParticleConfig d N) (i : Fin N),
      ContDiff ℝ ∞ (ParticleInsertion X i) ∧ Topology.IsClosedEmbedding (ParticleInsertion X i)) ∧
    ∀ (f : ParticleConfig d N → ℝ), ContDiff ℝ ∞ f → HasCompactSupport f →
      (∀ (X : ParticleConfig d N) (i : Fin N),
        ContDiff ℝ ∞ (fun z => f (ParticleInsertion X i z)) ∧
        HasCompactSupport (fun z => f (ParticleInsertion X i z)) ∧
        ∀ z : OneParticle d,
          EuclideanGradient (fun w => f (ParticleInsertion X i w)) z =
            ParticlePosition (EuclideanGradient f (ParticleInsertion X i z)) i) ∧
      (∀ X : ParticleConfig d N,
        (∑ i : Fin N, ‖EuclideanGradient (fun z => f (ParticleInsertion X i z))
          (ParticlePosition X i)‖ ^ 2) = ‖EuclideanGradient f X‖ ^ 2) := by
-- BODY
  refine ⟨fun X i => ⟨ParticleInsertionCalculus.insertion_smooth X i,
    ParticleInsertionCalculus.closedEmbedding X i⟩, ?_⟩
  intro f hf hc
  refine ⟨fun X i => ⟨hf.comp (ParticleInsertionCalculus.insertion_smooth X i),
    hc.comp_isClosedEmbedding (ParticleInsertionCalculus.closedEmbedding X i),
    ParticleInsertionCalculus.fibre_gradient f hf X i⟩, ?_⟩
  intro X
  simp_rw [ParticleInsertionCalculus.fibre_gradient f hf,
    ParticleInsertionCalculus.insertion_self]
  exact ((ParticleGradientEnergyIdentity (MeasureTheory.volume : MeasureTheory.Measure
    (ParticleConfig d N)) f).1 (EuclideanGradient f X)).symm
