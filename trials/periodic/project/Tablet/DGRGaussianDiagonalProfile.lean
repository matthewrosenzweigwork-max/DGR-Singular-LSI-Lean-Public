import Tablet.DGRGaussianTruncationIdentification
import Tablet.RieszMellinLongBound
import Tablet.RieszMellinFourier
open MeasureTheory
open scoped BigOperators
-- [TABLET NODE: DGRGaussianDiagonalProfile]
theorem DGRGaussianDiagonalProfile (d : ℕ) (hd : 2≤d) (s a : ℝ)
    (hs : 0≤s) (hsd : s<(d:ℝ)) (ha : 0<a) :
    ∃A : ℝ,0<A ∧ ∀η : ℝ,0<η → η≤1 → ∀K : Finset (Fin d→ℤ),
      let V := fun x => DGRGaussianPhysicalLong d s a η x-
        ∑k∈K,RieszMellinCoefficient d s a (η^2) 0 k*(UnitAddTorus.mFourier k x).re
      0≤V 0 ∧ V 0≤A*(if s=0 then 1+|Real.log (η^2)| else η^(-s)) := by
-- BODY
  classical
  obtain ⟨A,hA,hbound⟩ := RieszMellinLongBound d hd s a hs hsd ha
  refine ⟨A,hA,?_⟩
  intro η hη hη1 K
  have hδ : 0<η^2 := sq_pos_of_pos hη
  have hδ1 : η^2≤1 := by nlinarith only [hη,hη1]
  let c := RieszMellinCoefficient d s a (η^2) 0
  have hc := RieszMellinCoefficientBounds d s a hsd ha (η^2) 0 hδ le_rfl
  have hf := RieszMellinFourier d s a hsd ha (η^2) 0 hδ le_rfl
  have hlong := (DGRGaussianTruncationIdentification d s a η hη).2.1
  have hlow0 : (∑k∈K,c k*(UnitAddTorus.mFourier k (0:UnitAddTorus (Fin d))).re)=∑k∈K,c k := by
    apply Finset.sum_congr rfl
    intro k hk
    simp [UnitAddTorus.mFourier,fourier_apply]
  have hsum : (∑k∈K,c k)≤∑'k,c k := hc.1.sum_le_tsum K (fun k _ => (hc.2.2 k).1)
  have hsum0 : 0≤∑k∈K,c k := Finset.sum_nonneg fun k _ => (hc.2.2 k).1
  have hpow : (η^2)^(-s/2)=η^(-s) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hη.le]
    congr 1
    norm_num only [Nat.cast_ofNat]
    ring
  dsimp only
  change 0≤DGRGaussianPhysicalLong d s a η 0-∑k∈K,c k*(UnitAddTorus.mFourier k 0).re ∧ _
  rw [hlow0,hlong]
  have hdiag : (∑'k,c k)=RieszMellinLong d s a (η^2) 0 0 := hf.2.2.1
  rw [hdiag] at hsum
  have hupper := (le_abs_self (RieszMellinLong d s a (η^2) 0 0)).trans
    ((hbound (η^2) 0 hδ hδ1 le_rfl).2 0)
  rw [hpow] at hupper
  exact ⟨sub_nonneg.mpr hsum,by linarith only [hupper,hsum0]⟩
