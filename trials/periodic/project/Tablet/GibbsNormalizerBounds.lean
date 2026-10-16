module

public import Tablet.CanonicalLaw
public import Tablet.PairMomentBounds
public import Tablet.TiltNormalization
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Group.Prod

@[expose] public section
open MeasureTheory ProbabilityTheory
-- [TABLET NODE: GibbsNormalizerBounds]
theorem GibbsNormalizerBounds (d N : ℕ) (hN : 2 ≤ N) (l u : ℝ)
    (q : BoundedBackground d l u) (g : UnitAddTorus (Fin d) → ℝ)
    (hg : Measurable g) (hi : MeasureTheory.Integrable g (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d))))
    (c β : ℝ) (hc : 0 ≤ c) (hβ : 0 ≤ β)
    (hlo : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d))), -c ≤ g x) :
    MeasureTheory.Integrable (GibbsWeight (N := N) g q.density β)
      (MeasureTheory.volume : MeasureTheory.Measure (Configuration d N)) ∧
    Real.exp (-β * ((N : ℝ) - 1) / 2 * u ^ 2 *
      (∫ x, |g x| ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d))))) ≤
      (∫ X, GibbsWeight g q.density β X ∂(MeasureTheory.volume : MeasureTheory.Measure (Configuration d N))) ∧
    (∫ X, GibbsWeight g q.density β X ∂(MeasureTheory.volume : MeasureTheory.Measure (Configuration d N))) ≤
      Real.exp (β * c * ((N : ℝ) - 1) / 2) ∧
    MeasureTheory.IsProbabilityMeasure (CanonicalLaw (N := N) g q.density β) := by
-- BODY
  classical
  haveI : MeasureTheory.IsProbabilityMeasure
      (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
    infer_instance
  haveI : MeasureTheory.IsProbabilityMeasure
      (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d))) := by
    infer_instance
  have hPairMP (i j : Fin N) (hij : i ≠ j) :
      MeasureTheory.MeasurePreserving (fun X : Configuration d N => (X i, X j))
        MeasureTheory.volume (MeasureTheory.volume.prod MeasureTheory.volume) := by
    have hi := (iIndepFun_pi (μ := fun _ : Fin N =>
      (volume : Measure (UnitAddTorus (Fin d)))) (X := fun _ => id)
      (fun _ => aemeasurable_id)).indepFun hij
    refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), ?_⟩
    change Measure.map (fun X : Configuration d N => (X i, X j))
      (Measure.pi (fun _ : Fin N => (volume : Measure (UnitAddTorus (Fin d))))) = _
    have h := hi.map_prod_eq_prod_map_map
      (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
    simpa only [(measurePreserving_eval (fun _ : Fin N =>
      (volume : Measure (UnitAddTorus (Fin d)))) i).map_eq,
      (measurePreserving_eval (fun _ : Fin N =>
      (volume : Measure (UnitAddTorus (Fin d)))) j).map_eq] using h
  have hDiffMP (i j : Fin N) (hij : i ≠ j) :
      MeasureTheory.MeasurePreserving (fun X : Configuration d N => X i - X j)
        MeasureTheory.volume MeasureTheory.volume := by
      have hp := hPairMP i j hij
      have hs : MeasurePreserving (fun p : UnitAddTorus (Fin d) × UnitAddTorus (Fin d) => p.1 - p.2)
          (volume.prod volume) volume :=
        measurePreserving_fst.comp (measurePreserving_sub_prod volume volume)
      exact hs.comp hp
  have hcount : (∑ i : Fin N, ∑ j : Fin N, if i < j then (1 : ℝ) else 0) =
      (N : ℝ) * ((N : ℝ) - 1) / 2 := by
    have hterm (i j : Fin N) :
        (if j = i then (0 : ℝ) else 1) =
        (if i < j then 1 else 0) + (if j < i then 1 else 0) := by
      rcases lt_trichotomy i j with h | h | h
      · simp [h, ne_of_gt h, not_lt_of_gt h]
      · subst j; simp
      · simp [h, ne_of_lt h, not_lt_of_gt h]
    have hsum : (∑ i : Fin N, ∑ j : Fin N, if j = i then (0 : ℝ) else 1) =
        2 * (∑ i : Fin N, ∑ j : Fin N, if i < j then (1 : ℝ) else 0) := by
      simp_rw [hterm, Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j : Fin N => if j < i then (1 : ℝ) else 0)]
      ring
    have hrow (i : Fin N) :
        (∑ j : Fin N, if j = i then (0 : ℝ) else 1) = (N : ℝ) - 1 := by
      have hp (j : Fin N) : (if j = i then (0 : ℝ) else 1) =
          1 - (if j = i then 1 else 0) := by split_ifs <;> ring
      simp_rw [hp]
      simp [Finset.sum_sub_distrib]
    simp_rw [hrow] at hsum
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    linarith
  have hProd := ProductBackgroundFacts d N l u q
  have hQpos : ∀ᵐ X ∂MeasureTheory.volume, 0 ≤ ProductDensity (N := N) q.density X := by
    filter_upwards [hProd.2.2.2] with X hX
    exact (pow_nonneg q.lower_pos.le N).trans hX.1
  have hterm : ∀ i j : Fin N,
      ∀ᵐ X ∂(MeasureTheory.volume : MeasureTheory.Measure (Configuration d N)),
        -c * (if i < j then 1 else 0) ≤ (if i < j then g (X i - X j) else 0) := by
    intro i j
    by_cases hij : i < j
    · have hh := (hDiffMP i j (ne_of_lt hij)).quasiMeasurePreserving.tendsto_ae.eventually hlo
      filter_upwards [hh] with X hX
      simpa [hij] using hX
    · exact MeasureTheory.ae_of_all _ fun X => by simp [hij]
  have hAlower : ∀ᵐ X ∂(MeasureTheory.volume : MeasureTheory.Measure (Configuration d N)),
      -c * ((N : ℝ) - 1) / 2 ≤ PairEnergy g X := by
    filter_upwards [MeasureTheory.ae_all_iff.mpr
      (fun i => MeasureTheory.ae_all_iff.mpr (hterm i))] with X hX
    have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
      Finset.sum_le_sum (s := Finset.univ) fun j _ => hX i j
    have hexpr : (∑ i : Fin N, ∑ j : Fin N, -c * (if i < j then 1 else 0)) =
        -c * (N : ℝ) * ((N : ℝ) - 1) / 2 := by
      simp_rw [← Finset.mul_sum]
      rw [hcount]
      ring
    rw [hexpr] at hsum
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hh := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hNpos.le)
    unfold PairEnergy
    calc
      -c * ((N : ℝ) - 1) / 2 =
          (N : ℝ)⁻¹ * (-c * (N : ℝ) * ((N : ℝ) - 1) / 2) := by field_simp
      _ ≤ _ := hh
  have hAmeas : Measurable (PairEnergy (N := N) g) := by
    unfold PairEnergy
    refine measurable_const.mul (Finset.measurable_fun_sum _ fun i _ => ?_)
    refine Finset.measurable_fun_sum _ fun j _ => ?_
    split_ifs
    · exact hg.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))
    · exact measurable_const
  have hWmeas : Measurable (GibbsWeight (N := N) g q.density β) := by
    unfold GibbsWeight
    exact (measurable_const.mul hAmeas).exp.mul hProd.1
  let U := Real.exp (β * c * ((N : ℝ) - 1) / 2)
  have hWbound : ∀ᵐ X ∂MeasureTheory.volume,
      GibbsWeight (N := N) g q.density β X ≤ U * ProductDensity q.density X := by
    filter_upwards [hQpos, hAlower] with X hQ hA
    have he : Real.exp (-β * PairEnergy g X) ≤ U := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hA hβ]
    exact mul_le_mul_of_nonneg_right he hQ
  have hWpos : ∀ᵐ X ∂MeasureTheory.volume, 0 ≤ GibbsWeight (N := N) g q.density β X := by
    filter_upwards [hQpos] with X hQ
    exact mul_nonneg (Real.exp_nonneg _) hQ
  have hWint : MeasureTheory.Integrable (GibbsWeight (N := N) g q.density β)
      MeasureTheory.volume := by
    refine (hProd.2.1.const_mul U).mono' hWmeas.aestronglyMeasurable ?_
    filter_upwards [hWpos, hWbound] with X hp hb
    simpa [Real.norm_eq_abs, abs_of_nonneg hp] using hb
  have hupper : (∫ X, GibbsWeight (N := N) g q.density β X) ≤ U := by
    have hh := MeasureTheory.integral_mono_ae hWint (hProd.2.1.const_mul U) hWbound
    simpa [MeasureTheory.integral_const_mul, hProd.2.2.1] using hh
  have hMoment := PairMomentBounds d N (by omega) l u q g hg hi
  have hAQint : MeasureTheory.Integrable
      (fun X : Configuration d N => PairEnergy g X * ProductDensity q.density X)
      MeasureTheory.volume := by
    refine hMoment.2.2.1.mono' (hAmeas.mul hProd.1).aestronglyMeasurable ?_
    filter_upwards [hQpos] with X hQ
    simp [Real.norm_eq_abs, abs_mul, abs_of_nonneg hQ]
  let b := ∫ X : Configuration d N, PairEnergy g X * ProductDensity q.density X
  have hb : b ≤ ((N : ℝ) - 1) / 2 * u ^ 2 * (∫ x, |g x|) := by
    refine (MeasureTheory.integral_mono_ae hAQint hMoment.2.2.1 ?_).trans hMoment.2.2.2
    filter_upwards [hQpos] with X hQ
    exact mul_le_mul_of_nonneg_right (le_abs_self _) hQ
  let F := fun X : Configuration d N =>
    (Real.exp (-β * b) * (1 + β * b)) * ProductDensity q.density X -
      (Real.exp (-β * b) * β) * (PairEnergy g X * ProductDensity q.density X)
  have hFint : MeasureTheory.Integrable F MeasureTheory.volume :=
    (hProd.2.1.const_mul _).sub (hAQint.const_mul _)
  have hFmass : (∫ X, F X) = Real.exp (-β * b) := by
    rw [MeasureTheory.integral_sub (hProd.2.1.const_mul _) (hAQint.const_mul _)]
    simp only [MeasureTheory.integral_const_mul, hProd.2.2.1]
    change Real.exp (-β * b) * (1 + β * b) * 1 - Real.exp (-β * b) * β * b = _
    ring
  have hFbound : ∀ᵐ X ∂MeasureTheory.volume, F X ≤ GibbsWeight g q.density β X := by
    filter_upwards [hQpos] with X hQ
    have ht : 1 - β * (PairEnergy g X - b) ≤ Real.exp (-β * (PairEnergy g X - b)) := by
      nlinarith [Real.add_one_le_exp (-β * (PairEnergy g X - b))]
    have hh := mul_le_mul_of_nonneg_left ht (Real.exp_nonneg (-β * b))
    have heq : Real.exp (-β * b) * Real.exp (-β * (PairEnergy g X - b)) =
        Real.exp (-β * PairEnergy g X) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq] at hh
    have hm := mul_le_mul_of_nonneg_right hh hQ
    dsimp [F, GibbsWeight]
    nlinarith
  have hlowerb : Real.exp (-β * b) ≤ ∫ X, GibbsWeight (N := N) g q.density β X := by
    rw [← hFmass]
    exact MeasureTheory.integral_mono_ae hFint hWint hFbound
  have hlower : Real.exp (-β * ((N : ℝ) - 1) / 2 * u ^ 2 * (∫ x, |g x|)) ≤
      ∫ X, GibbsWeight (N := N) g q.density β X := by
    refine le_trans (Real.exp_le_exp.mpr ?_) hlowerb
    nlinarith [mul_le_mul_of_nonneg_left hb hβ]
  have hZ : 0 < ∫ X, GibbsWeight (N := N) g q.density β X :=
    (Real.exp_pos _).trans_le hlowerb
  refine ⟨hWint, hlower, hupper, ?_⟩
  exact (TiltNormalization MeasureTheory.volume (GibbsWeight (N := N) g q.density β)
    hWmeas hWpos hWint hZ).1
