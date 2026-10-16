module

public import Tablet.ConfigurationFlatten
public import Tablet.EuclideanGradient
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped ContDiff ENNReal NNReal
noncomputable section
-- [TABLET NODE: ConfigurationCoordinateTransport]
theorem ConfigurationCoordinateTransport (N d : ℕ) :
    let e := ConfigurationFlatten N d
    MeasurePreserving e volume volume ∧
    (∀ (f : ParticleConfig d N → ℝ), ContDiff ℝ 1 f →
      ContDiff ℝ 1 (f ∘ e.symm) ∧
      ∀ y, ‖EuclideanGradient (f ∘ e.symm) y‖ = ‖EuclideanGradient f (e.symm y)‖) ∧
    (∀ R : ℝ, ∀ X : ParticleConfig d N,
      (∀ k : Fin N × Fin d, |X k| ≤ R) ↔
      (∀ k : Fin (N*d), -R ≤ (e X) k ∧ (e X) k ≤ R)) ∧
    (∀ R : ℝ, 0 ≤ R → ∀ X : ParticleConfig d N,
      (∀ k, |X k| ≤ R) → ‖X‖ ≤ ((N*d:ℕ)+1:ℝ)*R) ∧
    (∀ (f : ParticleConfig d N → ℝ) (S : Set (EuclideanSpace ℝ (Fin (N*d)))),
      (∫ y in S, f (e.symm y)) = ∫ X in e ⁻¹' S, f X) ∧
    (∀ ρ : ParticleConfig d N → ℝ≥0,
      (volume.withDensity (fun X => (ρ X:ℝ≥0∞))).map e =
        volume.withDensity (fun y => (ρ (e.symm y):ℝ≥0∞))) := by
-- BODY
  let e := ConfigurationFlatten N d
  have hmp : MeasurePreserving e volume volume := e.measurePreserving
  refine ⟨hmp, ?_, ?_, ?_, ?_, ?_⟩
  · intro f hf
    refine ⟨hf.comp e.symm.toContinuousLinearEquiv.contDiff,?_⟩
    intro y
    have hd := hf.differentiable (by norm_num) (e.symm y)
    have he := e.symm.toContinuousLinearEquiv.toContinuousLinearMap.differentiableAt (x:=y)
    have hn : ‖fderiv ℝ (f ∘ e.symm) y‖ = ‖fderiv ℝ f (e.symm y)‖ := by
      rw [fderiv_comp y hd he]
      change ‖(fderiv ℝ f (e.symm y)).comp
        (fderiv ℝ e.symm.toContinuousLinearEquiv.toContinuousLinearMap y)‖ = _
      rw [ContinuousLinearMap.fderiv]
      exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ _
    simpa only [EuclideanGradient,gradient,LinearIsometryEquiv.norm_map] using hn
  · intro R X
    change (∀ k : Fin N × Fin d, |X k| ≤ R) ↔
      ∀ k : Fin (N*d), -R ≤ X (finProdFinEquiv.symm k) ∧ X (finProdFinEquiv.symm k) ≤ R
    constructor
    · intro h k
      exact abs_le.mp (h _)
    · intro h k
      have hh := h (finProdFinEquiv k)
      simpa only [Equiv.symm_apply_apply] using abs_le.mpr hh
  · intro R hR X hx
    have hb : ‖X‖^2 ≤ (N*d:ℕ)*R^2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      calc
        _ ≤ ∑ _ : Fin N × Fin d, R^2 := Finset.sum_le_sum (fun k _ => by
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (X k)) hR).mpr (hx k))
        _ = (N*d:ℕ)*R^2 := by simp
    have hn : 0 ≤ (N*d:ℕ) := Nat.zero_le _
    have hc : 0 ≤ ((N*d:ℕ)+1:ℝ)*R := by positivity
    have hh : ((N*d:ℕ):ℝ)*R^2 ≤ (((N*d:ℕ)+1:ℝ)*R)^2 := by
      nlinarith [sq_nonneg (((N*d:ℕ):ℝ)*R)]
    nlinarith [norm_nonneg X]
  · intro f S
    have h := hmp.setIntegral_preimage_emb e.toHomeomorph.measurableEmbedding
      (fun y => f (e.symm y)) S
    simpa only [LinearIsometryEquiv.symm_apply_apply] using h.symm
  · intro ρ
    have hm : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
    ext S hS
    rw [Measure.map_apply hm.measurable hS, withDensity_apply _ (hm.measurable hS), withDensity_apply _ hS]
    have h := hmp.setLIntegral_comp_preimage_emb hm (fun y => (ρ (e.symm y):ℝ≥0∞)) S
    simpa only [LinearIsometryEquiv.symm_apply_apply] using h
