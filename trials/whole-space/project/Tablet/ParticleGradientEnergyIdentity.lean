module

public import Tablet.PhysicalEnergy
public import Tablet.GradientNormIdentity
public import Tablet.ParticlePosition

@[expose] public section

-- [TABLET NODE: ParticleGradientEnergyIdentity]
theorem ParticleGradientEnergyIdentity {d N : ℕ}
    (P : MeasureTheory.Measure (ParticleConfig d N)) (f : ParticleConfig d N → ℝ) :
    (∀ X : ParticleConfig d N, ‖X‖ ^ 2 = ∑ i, ‖ParticlePosition X i‖ ^ 2) ∧
    PhysicalEnergy P f =
      ∫ X, ∑ i : Fin N, ∑ k : Fin d,
        (fderiv ℝ f X (EuclideanSpace.basisFun (Fin N × Fin d) ℝ (i, k))) ^ 2 ∂P := by
-- BODY
  constructor
  · intro X
    simp only [EuclideanSpace.real_norm_sq_eq, ParticlePosition]
    rw [Fintype.sum_prod_type]
  · unfold PhysicalEnergy
    congr 1
    funext X
    rw [(GradientNormIdentity f X).1, Fintype.sum_prod_type]
