import Tablet.CenteredPairEnergy
-- [TABLET NODE: CenteredDeletionPotential]
noncomputable def CenteredDeletionPotential {d N : ℕ} (g r : UnitAddTorus (Fin d) → ℝ)
    (β : ℝ) (i : Fin N)
    (p : (((Finset.univ : Finset (Fin N)).erase i → UnitAddTorus (Fin d)) ×
      (({i} : Finset (Fin N)) → UnitAddTorus (Fin d)))) : ℝ :=
-- BODY
  β / (N : ℝ) * ∑ j : (Finset.univ : Finset (Fin N)).erase i,
    CenteredKernel g r (p.2 ⟨i, Finset.mem_singleton_self i⟩) (p.1 j)
