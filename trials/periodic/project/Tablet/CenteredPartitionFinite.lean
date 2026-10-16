import Tablet.CenteredProductMean
import Tablet.CenteredPartition
open MeasureTheory
-- [TABLET NODE: CenteredPartitionFinite]
theorem CenteredPartitionFinite (d N : ℕ) (hN : 2 ≤ N)
    (g r : UnitAddTorus (Fin d) → ℝ)
    (hg : Measurable g) (hgi : Integrable g volume) (hr : Measurable r)
    (M c : ℝ) (hM : 1 ≤ M) (hc : 0 ≤ c)
    (hrb : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), 0 ≤ r x ∧ r x ≤ M)
    (hrmass : ∫ x, r x ∂volume = 1) (hgl : ∀ x, -c ≤ g x) :
    ∀ t : ℝ, 0 ≤ t →
      Integrable (fun X : Configuration d N =>
        Real.exp (-t * CenteredPairEnergy g r X) * ProductDensity r X) volume ∧
      1 ≤ CenteredPartition (N := N) g r t ∧
      CenteredPartition (N := N) g r t ≤
        Real.exp (t * ((N : ℝ)-1)/2 * (c + 3*M*(∫ x, |g x| ∂volume))) := by
-- BODY
  classical
  haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
    infer_instance
  haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := by infer_instance
  haveI : IsProbabilityMeasure (volume : Measure (Configuration d N)) := by infer_instance
  obtain ⟨hem,hwm,hwi,hwmass,hwb,hei,hemean⟩ :=
    CenteredProductMean d N g r hg hgi hr M c hM hc hrb hrmass hgl
  have hcl := (CenteredKernelBounds d g r hg hgi hr M c hM hc hrb hrmass hgl).2.2.2.2.2.2
  let C := c+3*M*(∫ x, |g x| ∂volume)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hcount : (∑ i : Fin N,∑ j : Fin N,if i < j then (1:ℝ) else 0) =
      (N:ℝ)*((N:ℝ)-1)/2 := by
    have hterm (i j : Fin N) : (if j = i then (0:ℝ) else 1) =
        (if i < j then 1 else 0)+(if j < i then 1 else 0) := by
      rcases lt_trichotomy i j with h|h|h
      · simp [h,ne_of_gt h,not_lt_of_gt h]
      · subst j;simp
      · simp [h,ne_of_lt h,not_lt_of_gt h]
    have hs : (∑ i : Fin N,∑ j : Fin N,if j = i then (0:ℝ) else 1) =
        2*(∑ i : Fin N,∑ j : Fin N,if i < j then (1:ℝ) else 0) := by
      simp_rw [hterm,Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j : Fin N => if j < i then (1:ℝ) else 0)]
      ring
    have hrw (i : Fin N) : (∑ j : Fin N,if j = i then (0:ℝ) else 1) = (N:ℝ)-1 := by
      have ht (j : Fin N) : (if j = i then (0:ℝ) else 1)=1-(if j = i then 1 else 0) := by
        split_ifs <;>ring
      simp_rw [ht]
      simp [Finset.sum_sub_distrib]
    simp_rw [hrw] at hs
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
    linarith
  have hnp : (N:ℝ) ≠ 0 := by exact_mod_cast (show N≠0 by omega)
  have hlower (X : Configuration d N) : -((N:ℝ)-1)/2*C ≤ CenteredPairEnergy g r X := by
    calc
      _ = (N:ℝ)⁻¹ * ∑ i : Fin N,∑ j : Fin N,if i < j then -C else 0 := by
        have ht (i j : Fin N) : (if i < j then -C else 0)=(if i < j then (1:ℝ) else 0)*(-C) := by
          split_ifs <;>ring
        simp_rw [ht,←Finset.sum_mul]
        rw [hcount]
        field_simp
      _ ≤ _ := by
        unfold CenteredPairEnergy
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg N))
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        split_ifs
        · dsimp [C]
          linarith [hcl (X i) (X j)]
        · rfl
  intro t ht
  let U := Real.exp (t*((N:ℝ)-1)/2*C)
  have hup (X : Configuration d N) : Real.exp (-t*CenteredPairEnergy g r X) ≤ U := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left (hlower X) ht
    nlinarith
  have hfm : Measurable (fun X : Configuration d N =>
      Real.exp (-t*CenteredPairEnergy g r X)*ProductDensity r X) :=
    (Real.measurable_exp.comp (hem.const_mul (-t))).mul hwm
  have hfi : Integrable (fun X : Configuration d N =>
      Real.exp (-t*CenteredPairEnergy g r X)*ProductDensity r X) volume := by
    refine Integrable.of_bound hfm.aestronglyMeasurable (U*M^N) ?_
    filter_upwards [hwb] with X hx
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) hx.1)]
    exact mul_le_mul (hup X) hx.2 hx.1 (Real.exp_nonneg _)
  have hti : Integrable (fun X : Configuration d N =>
      (1-t*CenteredPairEnergy g r X)*ProductDensity r X) volume := by
    have hrepr (X : Configuration d N) :
        (1-t*CenteredPairEnergy g r X)*ProductDensity r X =
          ProductDensity r X-t*(CenteredPairEnergy g r X*ProductDensity r X) := by ring
    simp_rw [hrepr]
    exact hwi.sub (hei.const_mul t)
  refine ⟨hfi,?_,?_⟩
  · have heq : (∫ X : Configuration d N,
        (1-t*CenteredPairEnergy g r X)*ProductDensity r X ∂volume)=1 := by
      have hrepr (X : Configuration d N) :
          (1-t*CenteredPairEnergy g r X)*ProductDensity r X =
            ProductDensity r X-t*(CenteredPairEnergy g r X*ProductDensity r X) := by ring
      simp_rw [hrepr]
      rw [integral_sub hwi (hei.const_mul t),integral_const_mul,hwmass,hemean]
      ring
    rw [←heq]
    apply integral_mono_ae hti hfi
    filter_upwards [hwb] with X hx
    apply mul_le_mul_of_nonneg_right _ hx.1
    simpa only [sub_eq_add_neg,mul_neg,neg_mul,add_comm] using
      Real.add_one_le_exp (-t*CenteredPairEnergy g r X)
  · change (∫ X : Configuration d N,
        Real.exp (-t*CenteredPairEnergy g r X)*ProductDensity r X ∂volume) ≤ U
    calc
      _ ≤ ∫ X : Configuration d N, U*ProductDensity r X ∂volume :=
        integral_mono_ae hfi (hwi.const_mul U) (hwb.mono fun X hx =>
          mul_le_mul_of_nonneg_right (hup X) hx.1)
      _ = U := by rw [integral_const_mul,hwmass,mul_one]
