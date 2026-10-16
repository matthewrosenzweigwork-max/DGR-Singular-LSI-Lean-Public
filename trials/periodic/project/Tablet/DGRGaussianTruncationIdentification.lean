module

public import Tablet.GaussianPhysicalScaleIntegral
public import Tablet.DGRGaussianPhysicalNear
public import Tablet.DGRGaussianPhysicalLong
public import Tablet.RieszMellinNear
public import Tablet.RieszMellinLong
public import Mathlib.Tactic

@[expose] public section
open MeasureTheory
-- [TABLET NODE: DGRGaussianTruncationIdentification]
theorem DGRGaussianTruncationIdentification (d : ℕ) (s a η : ℝ) (hη : 0 < η) :
    DGRGaussianPhysicalNear d s a η = RieszMellinNear d s a (η^2) 0 ∧
    DGRGaussianPhysicalLong d s a η = RieszMellinLong d s a (η^2) 0 ∧
    (η^2)^(((d:ℝ)-s)/2)=η^((d:ℝ)-s) ∧
    Real.sqrt (η^2)=η := by
-- BODY
  let α := ((d:ℝ)-s)/2
  have he : 2*α-1 = (d:ℝ)-s-1 := by dsimp [α]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext x
    have hh := (GaussianPhysicalScaleIntegral α η hη (fun t => HeatKernel d t x)).1
    unfold DGRGaussianPhysicalNear RieszMellinNear
    simp only [add_zero]
    change (2*a/Real.Gamma α)*(∫ ρ in Set.Ioc 0 η, ρ^((d:ℝ)-s-1)*HeatKernel d (ρ^2) x) = _
    rw [hh, he]
    ring
  · funext x
    have hh := (GaussianPhysicalScaleIntegral α η hη (fun t => HeatKernel d t x-1)).2
    unfold DGRGaussianPhysicalLong RieszMellinLong
    simp only [add_zero]
    change (2*a/Real.Gamma α)*(∫ ρ in Set.Ioi η, ρ^((d:ℝ)-s-1)*(HeatKernel d (ρ^2) x-1)) = _
    rw [hh, he]
    ring
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hη.le]
    congr 1
    norm_num
    ring
  · rw [Real.sqrt_sq_eq_abs, abs_of_pos hη]
