module

public import Tablet.PairAlgebra
public import Tablet.GibbsWeight
public import Tablet.BoundedBackground
public import Tablet.NormalizedTilt
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section
open MeasureTheory
-- [TABLET NODE: CanonicalTiltRowIdentity]
theorem CanonicalTiltRowIdentity (d N : ℕ) (l u β : ℝ) (q : BoundedBackground d l u)
    (g h : UnitAddTorus (Fin d) → ℝ) (hGe : ∀ x, g (-x) = g x) :
    ∀ i : Fin N, ∀ᵐ X : Configuration d N ∂volume,
      NormalizedTilt (volume : Measure (UnitAddTorus (Fin d)))
        (fun z => Real.exp (-β / (N : ℝ) * ∑ j : Fin N, h (Replacement X i z j)) *
          GibbsWeight g q.density β (Replacement X i z)) =
      NormalizedTilt volume (fun z => q.density z * Real.exp (-β * h z / (N : ℝ)) *
        Real.exp (-ConditionalPotential g β X i z)) := by
-- BODY
  classical
  haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp; infer_instance
  haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := inferInstance
  have hcoords : ∀ᵐ X : Configuration d N ∂volume, ∀ j : Fin N, 0 < q.density (X j) := by
    rw [Filter.eventually_all]
    intro j
    exact (measurePreserving_eval (fun _ : Fin N => (volume : Measure (UnitAddTorus (Fin d)))) j).quasiMeasurePreserving.tendsto_ae (q.bounds.mono fun x hx => q.lower_pos.trans_le hx.1)
  have tilt_scale {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (w : Ω → ℝ)
      (t : ℝ) (ht : t ≠ 0) : NormalizedTilt μ (fun x => t * w x) = NormalizedTilt μ w := by
    unfold NormalizedTilt
    simp only [integral_const_mul]
    congr 1; funext x; congr 1
    exact mul_div_mul_left _ _ ht
  intro i
  filter_upwards [hcoords] with X hX
  let A := ∑ j ∈ (Finset.univ : Finset (Fin N)).erase i, h (X j)
  let Q := ∏ j ∈ (Finset.univ : Finset (Fin N)).erase i, q.density (X j)
  let t := Real.exp (-β / (N : ℝ) * A - β * PairEnergy g X + ConditionalPotential g β X i (X i)) * Q
  have hQ : 0 < Q := Finset.prod_pos fun j _ => hX j
  have ht : t ≠ 0 := (mul_pos (Real.exp_pos _) hQ).ne'
  have hsum (z : UnitAddTorus (Fin d)) : (∑ j : Fin N, h (Replacement X i z j)) = h z + A := by
    have hh := Finset.add_sum_erase (Finset.univ : Finset (Fin N))
      (fun j => h (Replacement X i z j)) (Finset.mem_univ i)
    have hrest : (∑ j ∈ (Finset.univ : Finset (Fin N)).erase i, h (Replacement X i z j)) = A := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Replacement, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [hrest] at hh
    simpa only [Replacement,Function.update_self] using hh.symm
  have hprod (z : UnitAddTorus (Fin d)) : ProductDensity q.density (Replacement X i z) = q.density z * Q := by
    have hh := Finset.mul_prod_erase (Finset.univ : Finset (Fin N))
      (fun j => q.density (Replacement X i z j)) (Finset.mem_univ i)
    have hrest : (∏ j ∈ (Finset.univ : Finset (Fin N)).erase i, q.density (Replacement X i z j)) = Q := by
      apply Finset.prod_congr rfl
      intro j hj
      simp only [Replacement, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [hrest] at hh
    simpa only [ProductDensity,Replacement,Function.update_self] using hh.symm
  have hweight : (fun z => Real.exp (-β / (N : ℝ) * ∑ j : Fin N, h (Replacement X i z j)) *
      GibbsWeight g q.density β (Replacement X i z)) =
      fun z => t * (q.density z * Real.exp (-β * h z / (N : ℝ)) *
        Real.exp (-ConditionalPotential g β X i z)) := by
    funext z
    have he := (PairAlgebra g hGe β X).1 i z
    have hex : -β / (N : ℝ) * (h z + A) - β * PairEnergy g (Replacement X i z) =
        (-β / (N : ℝ) * A - β * PairEnergy g X + ConditionalPotential g β X i (X i)) +
          (-β * h z / (N : ℝ)) + (-ConditionalPotential g β X i z) := by
      have hh' : -β * PairEnergy g (Replacement X i z) =
        -β * PairEnergy g X + ConditionalPotential g β X i (X i) - ConditionalPotential g β X i z := by linarith
      linear_combination -he
    unfold GibbsWeight
    rw [hsum,hprod]
    calc
      _ = Real.exp (-β / (N : ℝ) * (h z + A) - β * PairEnergy g (Replacement X i z)) * (q.density z * Q) := by
        rw [sub_eq_add_neg,Real.exp_add]; ring
      _ = _ := by rw [hex,Real.exp_add,Real.exp_add]; dsimp [t]; ring
  rw [hweight]
  exact tilt_scale volume _ t ht
