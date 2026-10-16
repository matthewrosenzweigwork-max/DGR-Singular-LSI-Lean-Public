import Tablet.CenteredDeletionPotential
-- [TABLET NODE: CenteredDeletionEnergySum]
theorem CenteredDeletionEnergySum {d N : ℕ}
    (g r : UnitAddTorus (Fin d) → ℝ) (hg : ∀z,g (-z)=g z)
    (X : Configuration d N) (β : ℝ) :
    ((∑i : Fin N,β/(N : ℝ)*∑j : Fin N,if j≠i then CenteredKernel g r (X i) (X j) else 0)=
      2*β*CenteredPairEnergy g r X) ∧
    ((∑i : Fin N, CenteredDeletionPotential g r β i ((fun j => X j),(fun j => X j)))=
      2*β*CenteredPairEnergy g r X) := by
-- BODY
  classical
  have hordered : (∑i : Fin N,β/(N : ℝ)*∑j : Fin N,
      if j≠i then CenteredKernel g r (X i) (X j) else 0)=2*β*CenteredPairEnergy g r X := by
    classical
    have hK (x y : UnitAddTorus (Fin d)) : CenteredKernel g r y x=CenteredKernel g r x y := by
      have hh := hg (x-y)
      rw [neg_sub] at hh
      unfold CenteredKernel
      rw [hh]
      ring
    have hterm (i j : Fin N) :
        (if j≠i then CenteredKernel g r (X i) (X j) else 0)=
          (if i < j then CenteredKernel g r (X i) (X j) else 0)+
          (if j < i then CenteredKernel g r (X i) (X j) else 0) := by
      rcases lt_trichotomy i j with h|h|h
      · simp [h,ne_of_gt h,not_lt_of_gt h]
      · subst j;simp
      · simp [h,ne_of_lt h,not_lt_of_gt h]
    have hs : (∑i : Fin N,∑j : Fin N,if j < i then CenteredKernel g r (X i) (X j) else 0)=
        ∑i : Fin N,∑j : Fin N,if i < j then CenteredKernel g r (X i) (X j) else 0 := by
      rw [Finset.sum_comm]
      simp_rw [hK]
    simp_rw [hterm,Finset.sum_add_distrib,←Finset.mul_sum]
    rw [Finset.sum_add_distrib,hs]
    unfold CenteredPairEnergy
    ring
  refine ⟨hordered, ?_⟩
  have hs (i : Fin N) :
      (∑j : (Finset.univ : Finset (Fin N)).erase i, CenteredKernel g r (X i) (X j))=
      ∑j : Fin N,if j≠i then CenteredKernel g r (X i) (X j) else 0 := by
    rw [←Finset.sum_subtype _ (fun _ => Iff.rfl) (fun j => CenteredKernel g r (X i) (X j)),
      ←Finset.sum_filter]
    congr 1
    ext j
    simp
  unfold CenteredDeletionPotential
  simp_rw [hs]
  exact hordered
