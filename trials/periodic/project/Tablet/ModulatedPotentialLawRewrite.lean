module

public import Tablet.CanonicalLaw

@[expose] public section
open MeasureTheory
-- [TABLET NODE: ModulatedPotentialLawRewrite]
theorem ModulatedPotentialLawRewrite (d N : ℕ)
    (g r h : UnitAddTorus (Fin d) → ℝ) (β I Z : ℝ) (hZ : 0 < Z) :
    NormalizedTilt (volume : Measure (Configuration d N))
      (fun X => Real.exp (-β * (PairEnergy g X - (∑ i : Fin N, h (X i)) + (N : ℝ) * I)) *
        ProductDensity r X) =
      CanonicalLaw (N := N) g (fun x => r x * Real.exp (β * h x) / Z) β := by
-- BODY
  classical
  have hscale {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
      (w : Ω → ℝ) (t : ℝ) (ht : t ≠ 0) :
      NormalizedTilt μ (fun x => t * w x) = NormalizedTilt μ w := by
    unfold NormalizedTilt
    simp only [integral_const_mul]
    congr 1
    funext x
    congr 1
    exact mul_div_mul_left _ _ ht
  let t : ℝ := (Z ^ N)⁻¹ * Real.exp (β * (N : ℝ) * I)
  have ht : t ≠ 0 := mul_ne_zero (inv_ne_zero (pow_ne_zero _ (ne_of_gt hZ)))
    (ne_of_gt (Real.exp_pos _))
  have hweight (X : Configuration d N) :
      GibbsWeight g (fun x => r x * Real.exp (β * h x) / Z) β X =
        t * (Real.exp (-β * (PairEnergy g X - (∑ i : Fin N, h (X i)) + (N : ℝ) * I)) *
          ProductDensity r X) := by
    unfold GibbsWeight ProductDensity
    rw [Finset.prod_div_distrib, Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← Real.exp_sum, ← Finset.mul_sum]
    dsimp [t]
    rw [div_eq_mul_inv]
    have he : -β * (PairEnergy g X - (∑ i : Fin N, h (X i)) + (N : ℝ) * I) =
        -β * PairEnergy g X + β * (∑ i : Fin N, h (X i)) + -(β * (N : ℝ) * I) := by
      ring
    rw [he, Real.exp_add, Real.exp_add, Real.exp_neg]
    field_simp
    <;> ring
  unfold CanonicalLaw
  rw [show GibbsWeight (N := N) g (fun x => r x * Real.exp (β * h x) / Z) β =
      (fun X => t * (Real.exp (-β * (PairEnergy g X - (∑ i : Fin N, h (X i)) + (N : ℝ) * I)) *
        ProductDensity r X)) from funext hweight]
  exact (hscale volume _ t ht).symm
