import Tablet.DGRGaussianTruncationIdentification
import Tablet.RieszMellinNearCap
import Tablet.RieszMellinDecomposition
import Tablet.CenteredPairEnergyAEDecomposition
import Tablet.RieszMellinLongCenteredEnergyBound
import Tablet.RieszMellinFourier
import Tablet.RieszMellinCoefficientBounds
import Tablet.RieszL1Foundation
open MeasureTheory
open scoped BigOperators
-- [TABLET NODE: DGRGaussianCenteredTruncation]
theorem DGRGaussianCenteredTruncation (d : ℕ) (hd : 2 ≤ d)
    (s a η M : ℝ) (hs : 0 ≤ s) (hsd : s < (d:ℝ)) (ha : 0 < a)
    (hη : 0 < η) (hη1 : η ≤ 1) (hM : 1 ≤ M)
    (r : UnitAddTorus (Fin d) → ℝ) (hr : Measurable r)
    (hrb : ∀ᵐ x ∂volume, 0 ≤ r x ∧ r x ≤ M) (hrmass : ∫ x, r x = 1) :
    let α := ((d:ℝ)-s)/2
    let m := (a/Real.Gamma α)*η^((d:ℝ)-s)/α
    let G := DGRGaussianPhysicalNear d s a η
    let L := DGRGaussianPhysicalLong d s a η
    let c := RieszMellinCoefficient d s a (η^2) 0
    Measurable G ∧ Integrable G volume ∧ (∀ x, 0 ≤ G x) ∧ (∫ x, G x)=m ∧
    (∀ x, 0 ≤ BackgroundPotential G r x ∧ BackgroundPotential G r x ≤ M*m) ∧
    0 ≤ BackgroundPairMean G r ∧
    Measurable L ∧ Integrable L volume ∧ (∫ x, L x)=0 ∧
    Summable c ∧ (∀ k, 0 ≤ c k) ∧
    (∀ x, L x=∑' k, c k*(UnitAddTorus.mFourier k x).re) ∧
    (RieszKernel d s a 0 =ᵐ[volume] fun x => G x+L x-m) ∧
    (∀ N : ℕ, 1 ≤ N →
      (∀ X : Configuration d N, -((N:ℝ)-1)*M*m ≤ CenteredPairEnergy G r X) ∧
      (∀ X : Configuration d N, -2*L 0 ≤ CenteredPairEnergy L r X) ∧
      (CenteredPairEnergy (N:=N) (RieszKernel d s a 0) r
        =ᵐ[Measure.pi (fun _ : Fin N => volume.withDensity (fun x => ENNReal.ofReal (r x)))]
        fun X => CenteredPairEnergy G r X+CenteredPairEnergy L r X)) := by
-- BODY
  have hδ : 0 < η^2 := sq_pos_of_pos hη
  have hδ1 : η^2 ≤ 1 := by nlinarith [sq_nonneg (1-η)]
  obtain ⟨hnear, hlong, hpower, hsqrt⟩ := DGRGaussianTruncationIdentification d s a η hη
  have hn := RieszMellinNearCap d s a hsd ha (η^2) 0 hδ le_rfl M hM r hr hrb hrmass
  have hl := RieszMellinDecomposition d hd s a hs hsd ha (η^2) 0 hδ hδ1 le_rfl
  have hc := RieszMellinCoefficientBounds d s a hsd ha (η^2) 0 hδ le_rfl
  have hf := RieszMellinFourier d s a hsd ha (η^2) 0 hδ le_rfl
  dsimp only at hn hl hf
  rw [← hnear, hpower] at hn
  rw [← hnear, ← hlong, hpower] at hl
  rw [← hlong] at hf
  rcases hn with ⟨hGm,hGi,hGn,hGmass,hGpot,hGmean,hGkernel,hGE⟩
  rcases hl with ⟨hLm,hLi,hLmass,hdecomp⟩
  dsimp only
  refine ⟨hGm,hGi,hGn,hGmass,hGpot,hGmean,hLm,hLi,hLmass,hc.1,
    (fun k => (hc.2.2 k).1),hf.2.1,hdecomp,?_⟩
  intro N hN
  obtain ⟨C,hC,hkernel⟩ := RieszL1Foundation d hd s a hs hsd ha
  have hg := hkernel 0 le_rfl
  have hdcomp := CenteredPairEnergyAEDecomposition d N (RieszKernel d s a 0)
    (DGRGaussianPhysicalNear d s a η) (DGRGaussianPhysicalLong d s a η) r
    hg.1 hGm hLm hg.2.1 hGi hLi hr M
    ((a/Real.Gamma (((d:ℝ)-s)/2))*η^((d:ℝ)-s)/(((d:ℝ)-s)/2))
    (zero_le_one.trans hM) hrb hrmass hdecomp
  refine ⟨hGE N (by omega),?_,hdcomp.2.2.2⟩
  intro X
  have hb := RieszMellinLongCenteredEnergyBound d s a hsd ha (η^2) 0 hδ le_rfl M
    r hr hrb hrmass N hN X
  rwa [← hlong] at hb
