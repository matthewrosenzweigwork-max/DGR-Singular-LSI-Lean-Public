module

public import Tablet.ParticleConfig
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section
open MeasureTheory Set
open scoped BigOperators

-- [TABLET NODE: RowFlattenVolumePreserving]
theorem RowFlattenVolumePreserving (d N : ℕ) :
    MeasurePreserving (fun Y : Fin N → OneParticle d =>
      WithLp.toLp 2 (fun ik : Fin N × Fin d => Y ik.1 ik.2))
      (Measure.pi (fun _ : Fin N => (volume : Measure (OneParticle d))))
      (volume : Measure (ParticleConfig d N)) := by
-- BODY
  let cube := fun (ι : Type) [Fintype ι] =>
    {X : EuclideanSpace ℝ ι | ∀ k, X k ∈ Icc (0 : ℝ) 1}
  have hm (ι : Type) [Fintype ι] : MeasurableSet (cube ι) := by
    simp only [cube, ofPred_forall]
    exact MeasurableSet.iInter (fun k =>
      (PiLp.continuous_apply 2 (fun _ : ι => ℝ) k).measurable measurableSet_Icc)
  have hv (ι : Type) [Fintype ι] :
      (volume : Measure (EuclideanSpace ℝ ι)) (cube ι) = 1 := by
    let S : Set (ι → ℝ) := Set.univ.pi (fun _ => Icc (0 : ℝ) 1)
    have hS : MeasurableSet S := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
    have he : (MeasurableEquiv.toLp 2 (ι → ℝ)).symm ⁻¹' S = cube ι := by
      ext X
      simp [S, cube, Pi.le_def, forall_and]
    have h := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp ι).measure_preimage
      hS.nullMeasurableSet
    rw [he] at h
    calc
      _ = (volume : Measure (ι → ℝ)) S := h
      _ = ∏ _ : ι, (volume : Measure ℝ) (Icc (0 : ℝ) 1) := volume_pi_pi _
      _ = 1 := by simp
  let F : (Fin N → OneParticle d) ≃ₗ[ℝ] ParticleConfig d N :=
    { toFun := fun Y => WithLp.toLp 2 (fun ik => Y ik.1 ik.2)
      invFun := fun X i => WithLp.toLp 2 (fun k => X (i, k))
      left_inv := by intro Y; ext i k; rfl
      right_inv := by intro X; ext ik; rfl
      map_add' := by intro Y Z; ext ik; rfl
      map_smul' := by intro a Y; ext ik; rfl }
  let L := F.toContinuousLinearEquiv
  let ν := (volume : Measure (Fin N → OneParticle d)).map L
  let K := cube (Fin N × Fin d)
  have hν : ν K = 1 := by
    rw [Measure.map_apply L.continuous.measurable (hm _)]
    have he : L ⁻¹' K = univ.pi (fun _ : Fin N => cube (Fin d)) := by
      ext Y
      simp [L, K, cube, F]
    rw [he, volume_pi_pi]
    simp [hv]
  let : Measure.IsAddHaarMeasure ν := L.isAddHaarMeasure_map volume
  have hs : ν = Measure.addHaarScalarFactor ν volume •
      (volume : Measure (ParticleConfig d N)) := Measure.isAddLeftInvariant_eq_smul ν volume
  have hc : Measure.addHaarScalarFactor ν volume = 1 := by
    have hh := congrArg (fun m : Measure (ParticleConfig d N) => m K) hs
    rw [hν, Measure.smul_apply, hv] at hh
    simpa using hh.symm
  rw [hc, one_smul] at hs
  exact ⟨by fun_prop, hs⟩
