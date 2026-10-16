import Tablet.CenteredDeletionPotentialControls
import Tablet.GibbsConditionalKernelProbability
import Tablet.TiltPushforwardEquivalence
open MeasureTheory ProbabilityTheory

-- [TABLET NODE: CenteredGibbsKernelRowProjection]
theorem CenteredGibbsKernelRowProjection (d N : ℕ) (l u C β : ℝ)
    (r : BoundedBackground d l u) (g : UnitAddTorus (Fin d) → ℝ)
    (hg : Measurable g) (hgi : Integrable g volume) (heven : ∀ z, g (-z)=g z)
    (hC : 0 ≤ C) (hgb : ∀ z, |g z| ≤ C) :
    let μ := (volume : Measure (UnitAddTorus (Fin d))).withDensity (fun z => ENNReal.ofReal (r.density z))
    letI : IsProbabilityMeasure μ := by
      apply isProbabilityMeasure_iff.mpr
      rw [withDensity_apply _ MeasurableSet.univ]
      simp only [Measure.restrict_univ]
      rw [← ofReal_integral_eq_lintegral_ofReal (integrable_of_integral_eq_one r.mass)
        (r.bounds.mono fun _ hx => r.lower_pos.le.trans hx.1), r.mass]
      simp
    ∀ i : Fin N,
    let η := Measure.pi (fun _ : ({i} : Finset (Fin N)) => μ)
    IsMarkovKernel (GibbsConditionalKernel η (CenteredDeletionPotential g r.density β i)) ∧
    ∀ X : Configuration d N,
      (GibbsConditionalKernel η (CenteredDeletionPotential g r.density β i) (fun j => X j)).map
        (MeasurableEquiv.funUnique ({i} : Finset (Fin N)) (UnitAddTorus (Fin d))) =
      NormalizedTilt μ (fun z => Real.exp (-β/(N:ℝ)*∑ j : Fin N,
        if j=i then 0 else CenteredKernel g r.density z (X j))) := by
-- BODY
  classical
  let μ := (volume : Measure (UnitAddTorus (Fin d))).withDensity (fun z => ENNReal.ofReal (r.density z))
  obtain ⟨hp,hmU,hbU,_⟩ := CenteredDeletionPotentialControls d N l u C β r g hg hgi heven hC hgb
  haveI : IsProbabilityMeasure μ := hp
  dsimp only
  intro i
  let η := Measure.pi (fun _ : ({i} : Finset (Fin N)) => μ)
  let U := CenteredDeletionPotential g r.density β i
  let e := MeasurableEquiv.funUnique ({i} : Finset (Fin N)) (UnitAddTorus (Fin d))
  let Q := |β/(N:ℝ)| * (N:ℝ)*(C+3*(u*∫ z,|g z|∂volume))
  have hi (x) : Integrable (fun y => Real.exp (-U (x,y))) η := by
    apply (integrable_const (Real.exp Q)).mono'
      ((hmU i).comp (measurable_const.prodMk measurable_id)).neg.exp.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      change -U (x,y) ≤ Q
      have hh := (abs_le.mp (hbU i (x,y))).1
      linarith
  obtain ⟨hκ,hrow⟩ := GibbsConditionalKernelProbability η U (hmU i) hi
  refine ⟨hκ,fun X => ?_⟩
  rw [hrow]
  have hweight : Measurable (fun y => Real.exp (-U ((fun j => X j),y))) :=
    ((hmU i).comp (measurable_const.prodMk measurable_id)).neg.exp
  rw [TiltPushforwardEquivalence η e _ hweight]
  have hmap : η.map e = μ := (measurePreserving_funUnique μ ({i} : Finset (Fin N))).map_eq
  rw [hmap]
  congr 1
  funext z
  have he : e.symm z = fun _ => z := rfl
  rw [he]
  have hh : CenteredDeletionPotential g r.density β i ((fun j => X j),(fun _ => z)) = β/(N:ℝ)*∑ j : Fin N, if j=i then 0 else CenteredKernel g r.density z (X j) := by
    classical
    unfold CenteredDeletionPotential
    congr 1
    rw [← Finset.sum_subtype _ (fun _ => Iff.rfl) (fun j => CenteredKernel g r.density z (X j))]
    have he : (Finset.univ : Finset (Fin N)).erase i = Finset.univ.filter (fun j => j≠i) := by
      ext j
      simp
    rw [he,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j=i <;> simp [hj]
  change Real.exp (-CenteredDeletionPotential g r.density β i ((fun j => X j),(fun _ => z))) = _
  rw [hh]
  congr 1
  ring
