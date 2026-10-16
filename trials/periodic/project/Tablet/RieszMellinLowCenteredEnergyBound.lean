module

public import Tablet.TorusSummableGramCenteredEnergy
public import Tablet.RieszMellinCoefficientBounds

@[expose] public section
open MeasureTheory
-- [TABLET NODE: RieszMellinLowCenteredEnergyBound]
theorem RieszMellinLowCenteredEnergyBound (d : ℕ) (s a : ℝ)
    (hsd : s < (d : ℝ)) (ha : 0 < a) (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 ≤ ε)
    (K : Finset (Fin d → ℤ)) (M : ℝ) (r : UnitAddTorus (Fin d) → ℝ) (hr : Measurable r)
    (hrb : ∀ᵐx∂volume, 0 ≤ r x ∧ r x ≤ M) (hrmass : ∫x,r x∂volume = 1) :
    let low := fun x : UnitAddTorus (Fin d) =>
      ∑k∈K, RieszMellinCoefficient d s a δ ε k * (UnitAddTorus.mFourier k x).re
    (∀N : ℕ, 1 ≤ N → ∀X : Configuration d N,
      -2 * (∑k∈K, RieszMellinCoefficient d s a δ ε k) ≤ CenteredPairEnergy low r X) ∧
    (∀N : ℕ, 1 ≤ N → ∀X : Configuration d N,
      -2 * (∑k∈K, if k=0 then 0 else a*(4*Real.pi^2*∑j,(k j:ℝ)^2)^(-((d:ℝ)-s)/2))
        ≤ CenteredPairEnergy low r X) := by
-- BODY
  classical
  haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1:ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
    infer_instance
  haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := inferInstance
  have hri : Integrable r volume := Integrable.of_bound hr.aestronglyMeasurable M
    (hrb.mono fun x hx => by simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2)
  let c := RieszMellinCoefficient d s a δ ε
  let w := fun k => if k∈K then c k else 0
  have hB := RieszMellinCoefficientBounds d s a hsd ha δ ε hδ hε
  have hw : ∀k, 0 ≤ w k := by
    intro k
    dsimp [w]
    split_ifs
    · exact (hB.2.2 k).1
    · exact le_rfl
  have hws : Summable w := by
    exact summable_of_hasFiniteSupport (show Function.HasFiniteSupport w from by
      apply Set.Finite.subset K.finite_toSet
      intro k hk
      by_contra hnk
      change k ∉ K at hnk
      exact hk (by simp [w,hnk]))
  have hsum : (∑'k,w k) = ∑k∈K,c k := by
    rw [tsum_eq_sum (s:=K) (fun k hk => by simp [w,hk])]
    apply Finset.sum_congr rfl
    intro k hk
    simp [w,hk]
  have hseries (x : UnitAddTorus (Fin d)) :
      (∑k∈K,c k*(UnitAddTorus.mFourier k x).re) =
      ∑'k,w k*(UnitAddTorus.mFourier k x).re := by
    rw [tsum_eq_sum (s:=K) (fun k hk => by simp [w,hk])]
    apply Finset.sum_congr rfl
    intro k hk
    simp [w,hk]
  have hcap := TorusSummableGramCenteredEnergy d _ r hr (hrb.mono fun _ hx => hx.1)
    hri hrmass w hw hws hseries
  rw [hsum] at hcap
  dsimp only
  refine ⟨hcap,?_⟩
  intro N hN X
  have hle : (∑k∈K,c k) ≤ ∑k∈K,if k=0 then 0 else
      a*(4*Real.pi^2*∑j,(k j:ℝ)^2)^(-((d:ℝ)-s)/2) :=
    Finset.sum_le_sum fun k _ => (hB.2.2 k).2.1
  exact (mul_le_mul_of_nonpos_left hle (by norm_num : (-2:ℝ) ≤ 0)).trans (hcap N hN X)
