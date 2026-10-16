import Tablet.CanonicalLaw
open MeasureTheory
-- [TABLET NODE: ExternalPotentialLawRewrite]
theorem ExternalPotentialLawRewrite (d N : ℕ)
    (g V : UnitAddTorus (Fin d) → ℝ) (β Z : ℝ) (hZ : 0 < Z) :
    NormalizedTilt (volume : Measure (Configuration d N))
      (fun X => Real.exp (-β * (∑ i : Fin N, V (X i)) - β * PairEnergy g X)) =
      CanonicalLaw (N := N) g (fun x => Real.exp (-β * V x) / Z) β := by
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
  have hweight (X : Configuration d N) :
      GibbsWeight g (fun x => Real.exp (-β * V x) / Z) β X =
        (Z ^ N)⁻¹ * Real.exp (-β * (∑ i : Fin N, V (X i)) - β * PairEnergy g X) := by
    unfold GibbsWeight ProductDensity
    rw [Finset.prod_div_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← Real.exp_sum]
    rw [← Finset.mul_sum]
    have he : -β * (∑ i : Fin N, V (X i)) - β * PairEnergy g X =
        -β * PairEnergy g X + -β * (∑ i : Fin N, V (X i)) := by ring
    rw [he, Real.exp_add, div_eq_mul_inv]
    ring
  unfold CanonicalLaw
  rw [show GibbsWeight (N := N) g (fun x => Real.exp (-β * V x) / Z) β =
      (fun X => (Z ^ N)⁻¹ * Real.exp (-β * (∑ i : Fin N, V (X i)) - β * PairEnergy g X)) from
    funext hweight]
  exact (hscale volume _ _ (inv_ne_zero (pow_ne_zero _ (ne_of_gt hZ)))).symm
