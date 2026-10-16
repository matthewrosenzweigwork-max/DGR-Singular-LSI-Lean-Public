module

public import Tablet.BoundedBackground
public import Tablet.ProductDensity

@[expose] public section
-- [TABLET NODE: ProductBackgroundFacts]
theorem ProductBackgroundFacts (d N : ℕ) (l u : ℝ)
    (q : BoundedBackground d l u) :
    Measurable (ProductDensity (N := N) q.density) ∧
    MeasureTheory.Integrable (ProductDensity q.density) (MeasureTheory.volume : MeasureTheory.Measure (Configuration d N)) ∧
    (∫ X, ProductDensity q.density X ∂(MeasureTheory.volume : MeasureTheory.Measure (Configuration d N))) = 1 ∧
    (∀ᵐ X ∂(MeasureTheory.volume : MeasureTheory.Measure (Configuration d N)),
      l ^ N ≤ ProductDensity q.density X ∧ ProductDensity q.density X ≤ u ^ N) := by
-- BODY
  have hmeas : Measurable (ProductDensity (N := N) q.density) := by
    unfold ProductDensity
    exact Finset.measurable_fun_prod _ fun i _ =>
      q.measurable.comp (measurable_pi_apply i)
  have hmass : (∫ X, ProductDensity q.density X
      ∂(MeasureTheory.volume : MeasureTheory.Measure (Configuration d N))) = 1 := by
    simpa only [ProductDensity, Fintype.card_fin, q.mass, one_pow] using
      (MeasureTheory.integral_fintype_prod_volume_eq_pow (ι := Fin N) q.density)
  refine ⟨hmeas, MeasureTheory.integrable_of_integral_eq_one hmass, hmass, ?_⟩
  have hcoord : ∀ i : Fin N,
      ∀ᵐ X ∂(MeasureTheory.volume : MeasureTheory.Measure (Configuration d N)),
        l ≤ q.density (X i) ∧ q.density (X i) ≤ u := by
    intro i
    exact (MeasureTheory.Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin N => (MeasureTheory.volume :
        MeasureTheory.Measure (UnitAddTorus (Fin d)))) (i := i)).eventually q.bounds
  filter_upwards [MeasureTheory.ae_all_iff.mpr hcoord] with X hX
  constructor
  · simpa [ProductDensity] using
      (Finset.prod_le_prod₀ (s := Finset.univ)
        (fun (_ : Fin N) _ => q.lower_pos.le) (fun i _ => (hX i).1))
  · simpa [ProductDensity] using
      (Finset.prod_le_prod₀ (s := Finset.univ)
        (fun i _ => q.lower_pos.le.trans (hX i).1) (fun i _ => (hX i).2))
