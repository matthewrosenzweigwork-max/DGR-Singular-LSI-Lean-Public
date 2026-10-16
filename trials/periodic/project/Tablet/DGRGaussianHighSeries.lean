module

public import Tablet.DGRGaussianTruncationIdentification
public import Tablet.RieszMellinFourier
public import Tablet.TorusSummableGramCenteredEnergy

@[expose] public section
open MeasureTheory
open scoped BigOperators
-- [TABLET NODE: DGRGaussianHighSeries]
theorem DGRGaussianHighSeries (d : ℕ) (s a η M : ℝ)
    (hsd : s < (d:ℝ)) (ha : 0<a) (hη : 0<η)
    (K : Finset (Fin d → ℤ))
    (r : UnitAddTorus (Fin d) → ℝ) (hr : Measurable r)
    (hrb : ∀ᵐ x ∂volume, 0≤r x ∧ r x≤M) (hrmass : ∫ x, r x=1) :
    let c := RieszMellinCoefficient d s a (η^2) 0
    let w := fun k => if k∈K then 0 else c k
    let V := fun x => DGRGaussianPhysicalLong d s a η x-
      ∑ k∈K, c k*(UnitAddTorus.mFourier k x).re
    Summable w ∧ (∀ k, 0≤w k) ∧
    (∀ k, w k≤(if k∈K then 0 else
      if k=0 then 0 else a*(4*Real.pi^2*∑j,(k j:ℝ)^2)^(-((d:ℝ)-s)/2))) ∧
    (∀ x, V x=∑'k, w k*(UnitAddTorus.mFourier k x).re) ∧
    V 0=∑'k,w k ∧
    (∀ N : ℕ, 1≤N → ∀ X : Configuration d N,
      -2*V 0≤CenteredPairEnergy V r X) := by
-- BODY
  classical
  let c := RieszMellinCoefficient d s a (η^2) 0
  let w := fun k => if k∈K then 0 else c k
  let V := fun x => DGRGaussianPhysicalLong d s a η x-
    ∑ k∈K, c k*(UnitAddTorus.mFourier k x).re
  have hδ : 0<η^2 := sq_pos_of_pos hη
  have hc := RieszMellinCoefficientBounds d s a hsd ha (η^2) 0 hδ le_rfl
  have hf := RieszMellinFourier d s a hsd ha (η^2) 0 hδ le_rfl
  have hlong := (DGRGaussianTruncationIdentification d s a η hη).2.1
  have hws : Summable w := by
    convert! hc.1.indicator (↑K : Set (Fin d→ℤ))ᶜ using 1
    funext k
    simp [w,c,Set.indicator,ite_not]
  have hwn (k) : 0≤w k := by
    dsimp [w]; split_ifs <;> first | exact le_rfl | exact (hc.2.2 k).1
  have hrep (x) : V x=∑'k,w k*(UnitAddTorus.mFourier k x).re := by
    have hchar (k) : ‖UnitAddTorus.mFourier k x‖=1 := by
      simp only [UnitAddTorus.mFourier,ContinuousMap.coe_mk,fourier_apply,
        norm_prod,Circle.norm_coe,Finset.prod_const_one]
    have hsum : Summable (fun k => c k*(UnitAddTorus.mFourier k x).re) := by
      apply summable_norm_iff.mp
      apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hc.1
      intro k
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hc.2.2 k).1]
      exact mul_le_of_le_one_right (hc.2.2 k).1
        ((Complex.abs_re_le_norm _).trans_eq (hchar k))
    have he := hsum.sum_add_tsum_compl (s:=K)
    dsimp [V]
    rw [hlong,hf.2.1]
    rw [← he]
    simp only [add_sub_cancel_left]
    rw [tsum_subtype (↑K : Set (Fin d→ℤ))ᶜ (fun k => c k*(UnitAddTorus.mFourier k x).re)]
    apply tsum_congr
    intro k
    simp only [Set.indicator_apply,Set.mem_compl_iff,Finset.mem_coe,w]
    split_ifs <;> simp_all
  have hdiag : V 0=∑'k,w k := by
    rw [hrep]
    apply tsum_congr
    intro k
    simp [UnitAddTorus.mFourier,fourier_apply]
  haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1:ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp; infer_instance
  haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := inferInstance
  have hri : Integrable r volume := Integrable.of_bound hr.aestronglyMeasurable M
    (hrb.mono fun x hx => by simpa only [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2)
  change Summable w ∧ (∀ k, 0≤w k) ∧ _ ∧ (∀ x,V x=_) ∧ V 0=_ ∧ _
  refine ⟨hws,hwn,?_,hrep,hdiag,?_⟩
  · intro k
    change (if k∈K then 0 else c k) ≤ _
    by_cases hk : k∈K
    · simp [hk]
    · simpa only [if_neg hk] using (hc.2.2 k).2.1
  · change ∀ N : ℕ, 1≤N → ∀ X : Configuration d N, -2*V 0≤CenteredPairEnergy V r X
    rw [hdiag]
    exact TorusSummableGramCenteredEnergy d V r hr (hrb.mono fun _ hx => hx.1)
      hri hrmass w hwn hws hrep
