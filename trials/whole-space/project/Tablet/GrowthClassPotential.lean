module

public import Tablet.PotentialBounds
public import Tablet.ForceExponent
public import Tablet.ShiftedReference

@[expose] public section

-- [TABLET NODE: GrowthClassPotential]
structure GrowthClassPotential (d : ℕ) (s κ : ℝ) (M C : ℝ → ℝ)
    (V : OneParticle d → ℝ) : Prop extends PotentialBounds d κ V where
-- BODY
  localData : ∃ m : OneParticle d, (∀ x, V m ≤ V x) ∧
    ∀ R : ℝ, 0 < R → ∀ x : OneParticle d, ‖x‖ ≤ R →
      (ShiftedReference V (fun _ => 1) m).1 x ≤ M R
  growth : ∀ a : ℝ, 0 < a → ∀ x : OneParticle d,
    EuclideanLaplacian V x ≤ a * ‖EuclideanGradient V x‖ ^ ForceExponent s + C a
