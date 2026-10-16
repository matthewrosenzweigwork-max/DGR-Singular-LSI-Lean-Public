module

public import Tablet.PairEnergy
public import Tablet.ProductBackgroundFacts
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Group.Prod

@[expose] public section
open MeasureTheory ProbabilityTheory
-- [TABLET NODE: PairMomentBounds]
theorem PairMomentBounds (d N : ℕ) (hN : 1 ≤ N) (l u : ℝ)
    (q : BoundedBackground d l u) (g : UnitAddTorus (Fin d) → ℝ)
    (hg : Measurable g) (hi : MeasureTheory.Integrable g (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d)))) :
    MeasureTheory.Integrable (PairEnergy (N := N) g) (MeasureTheory.volume : MeasureTheory.Measure (Configuration d N)) ∧
    (∫ X, PairEnergy g X ∂(MeasureTheory.volume : MeasureTheory.Measure (Configuration d N))) =
      ((N : ℝ) - 1) / 2 * (∫ x, g x ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d)))) ∧
    MeasureTheory.Integrable
      (fun X : Configuration d N => |PairEnergy g X| * ProductDensity q.density X)
      (MeasureTheory.volume : MeasureTheory.Measure (Configuration d N)) ∧
    (∫ X : Configuration d N, |PairEnergy g X| * ProductDensity q.density X
      ∂(MeasureTheory.volume : MeasureTheory.Measure (Configuration d N))) ≤
      ((N : ℝ) - 1) / 2 * u ^ 2 * (∫ x, |g x| ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d)))) := by
-- BODY
  have unitTorus_probability (d : ℕ) :
      IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := by
    haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
      rw [AddCircle.volume_eq_smul_haarAddCircle]
      simp
      infer_instance
    infer_instance

  have configuration_pair_measurePreserving (d N : ℕ) (i j : Fin N) (hij : i ≠ j) :
      MeasurePreserving (fun X : Configuration d N => (X i, X j))
        volume (volume.prod volume) := by
    haveI := unitTorus_probability d
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


  have configuration_difference_measurePreserving (d N : ℕ) (i j : Fin N) (hij : i ≠ j) :
      MeasurePreserving (fun X : Configuration d N => X i - X j) volume volume := by
    haveI := unitTorus_probability d
    have hp := configuration_pair_measurePreserving d N i j hij
    have hs : MeasurePreserving (fun p : UnitAddTorus (Fin d) × UnitAddTorus (Fin d) => p.1 - p.2)
        (volume.prod volume) volume :=
      measurePreserving_fst.comp (measurePreserving_sub_prod volume volume)
    exact hs.comp hp


  have configuration_difference_integral (d N : ℕ) (i j : Fin N) (hij : i ≠ j)
      (g : UnitAddTorus (Fin d) → ℝ) (hg : Measurable g) :
      (∫ X : Configuration d N, g (X i - X j)) = ∫ x, g x := by
    have hp := configuration_difference_measurePreserving d N i j hij
    rw [← hp.map_eq]
    exact (integral_map hp.measurable.aemeasurable hg.aestronglyMeasurable).symm

  have configuration_difference_integrable (d N : ℕ) (i j : Fin N) (hij : i ≠ j)
      (g : UnitAddTorus (Fin d) → ℝ) (hg : Measurable g)
      (hi : Integrable g volume) :
      Integrable (fun X : Configuration d N => g (X i - X j)) volume :=
    (configuration_difference_measurePreserving d N i j hij).integrable_comp
      hg.aestronglyMeasurable |>.mpr hi


  have pair_count_real (N : ℕ) :
      (∑ i : Fin N, ∑ j : Fin N, if i < j then (1 : ℝ) else 0) =
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


  have pairEnergy_integrable_mean (d N : ℕ) (hN : 1 ≤ N)
      (g : UnitAddTorus (Fin d) → ℝ) (hg : Measurable g) (hi : Integrable g volume) :
      Integrable (PairEnergy (N := N) g) volume ∧
        (∫ X : Configuration d N, PairEnergy g X) =
          ((N : ℝ)-1)/2 * ∫ x, g x := by
    have hp (i j : Fin N) : Integrable
        (fun X : Configuration d N => if i < j then g (X i-X j) else 0) volume := by
      split_ifs with h
      · exact configuration_difference_integrable d N i j (ne_of_lt h) g hg hi
      · exact integrable_const 0
    have hsum : Integrable
        (fun X : Configuration d N => ∑ i : Fin N, ∑ j : Fin N,
          if i < j then g (X i-X j) else 0) volume :=
      integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hp i j))
    constructor
    · exact hsum.const_mul _
    · simp only [PairEnergy, integral_const_mul]
      rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hp i j))]
      simp_rw [integral_finset_sum _ (fun j _ => hp _ j)]
      have he (i j : Fin N) :
          (∫ X : Configuration d N, if i < j then g (X i-X j) else 0) =
          (if i < j then 1 else 0) * (∫ x, g x) := by
        by_cases h : i < j
        · simp only [h, ↓reduceIte, one_mul]
          exact configuration_difference_integral d N i j (ne_of_lt h) g hg
        · simp [h]
      simp_rw [he, ← Finset.sum_mul]
      rw [pair_count_real]
      have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
      field_simp


  have weighted_pair_moment (d N : ℕ) (i j : Fin N) (hij : i ≠ j)
      (l u : ℝ) (q : BoundedBackground d l u)
      (g : UnitAddTorus (Fin d) → ℝ) (hg : Measurable g) (hi : Integrable g volume) :
      Integrable (fun X : Configuration d N => |g (X i-X j)| * ProductDensity q.density X) volume ∧
      (∫ X : Configuration d N, |g (X i-X j)| * ProductDensity q.density X) ≤
        u^2 * ∫ x, |g x| := by
    classical
    haveI := unitTorus_probability d
    let S : Finset (Fin N) := {i,j}
    let T : Finset (Fin N) := Finset.univ.erase i |>.erase j
    let a : Configuration d N → ℝ := fun X => |g (X i-X j)| * q.density (X i) * q.density (X j)
    let b : Configuration d N → ℝ := fun X => ∏ k ∈ T, q.density (X k)
    have hcoord : ∀ k : Fin N, ∀ᵐ X : Configuration d N,
        0 ≤ q.density (X k) ∧ q.density (X k) ≤ u := by
      intro k
      filter_upwards [(Measure.tendsto_eval_ae_ae (μ := fun _ : Fin N =>
        (volume : Measure (UnitAddTorus (Fin d)))) (i := k)).eventually q.bounds] with X h
      exact ⟨q.lower_pos.le.trans h.1,h.2⟩
    have hgab : Measurable (fun x => |g x|) := by
      simpa only [Real.norm_eq_abs] using hg.norm
    have hmeasa : Measurable a := by
      exact ((hgab.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))).mul
        (q.measurable.comp (measurable_pi_apply i))).mul
        (q.measurable.comp (measurable_pi_apply j))
    have hmeasb : Measurable b :=
      Finset.measurable_fun_prod _ (fun k _ => q.measurable.comp (measurable_pi_apply k))
    have hboundq (k : Fin N) : ∀ᵐ X : Configuration d N, ‖q.density (X k)‖ ≤ u := by
      filter_upwards [hcoord k] with X h
      simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2
    have hintg : Integrable (fun X : Configuration d N => |g (X i-X j)|) volume :=
      (configuration_difference_integrable d N i j hij g hg hi).abs
    have hinta : Integrable a volume :=
      (hintg.mul_bdd (q.measurable.comp (measurable_pi_apply i)).aestronglyMeasurable (hboundq i)).mul_bdd
        (q.measurable.comp (measurable_pi_apply j)).aestronglyMeasurable (hboundq j)
    have hboundb : ∀ᵐ X : Configuration d N, 0 ≤ b X ∧ b X ≤ u^T.card := by
      filter_upwards [ae_all_iff.mpr hcoord] with X h
      constructor
      · exact Finset.prod_nonneg (fun k _ => (h k).1)
      · simpa only [b, Finset.prod_const] using
          (Finset.prod_le_prod₀ (s := T) (fun k _ => (h k).1) (fun k _ => (h k).2))
    have hboundbnorm : ∀ᵐ X : Configuration d N, ‖b X‖ ≤ u^T.card := by
      filter_upwards [hboundb] with X h
      simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2
    have hmassb : (∫ X : Configuration d N, b X) = 1 := by
      have hrepr (X : Configuration d N) : b X =
          ∏ k : Fin N, if k ∈ T then q.density (X k) else 1 := by
        simp [b, Finset.prod_ite_mem]
      simp_rw [hrepr]
      have hp := integral_fintype_prod_volume_eq_prod
        (fun (k : Fin N) (x : UnitAddTorus (Fin d)) => if k ∈ T then q.density x else 1)
      rw [hp]
      have he (k : Fin N) : (∫ x : UnitAddTorus (Fin d),
          if k ∈ T then q.density x else 1) = 1 := by
        by_cases h : k ∈ T <;> simp [h, q.mass]
      simp_rw [he]; simp
    have hind : IndepFun a b (volume : Measure (Configuration d N)) := by
      have hST : Disjoint S T := by
        simp [S,T, Finset.disjoint_left]
      have hI := iIndepFun_pi (μ := fun _ : Fin N =>
        (volume : Measure (UnitAddTorus (Fin d)))) (X := fun _ => id)
        (fun _ => aemeasurable_id)
      have hR := hI.indepFun_finset S T hST (fun k => measurable_pi_apply k)
      let A : (S → UnitAddTorus (Fin d)) → ℝ := fun V =>
        |g (V ⟨i,by simp [S]⟩ - V ⟨j,by simp [S]⟩)| *
          q.density (V ⟨i,by simp [S]⟩) * q.density (V ⟨j,by simp [S]⟩)
      let B' : (T → UnitAddTorus (Fin d)) → ℝ := fun V => ∏ k, q.density (V k)
      have hA : Measurable A := by
        exact ((hgab.comp ((measurable_pi_apply (⟨i,by simp [S]⟩ : S)).sub
          (measurable_pi_apply (⟨j,by simp [S]⟩ : S)))).mul
          (q.measurable.comp (measurable_pi_apply (⟨i,by simp [S]⟩ : S)))).mul
          (q.measurable.comp (measurable_pi_apply (⟨j,by simp [S]⟩ : S)))
      have hB' : Measurable B' :=
        Finset.measurable_fun_prod _ (fun k _ => q.measurable.comp (measurable_pi_apply k))
      have h := hR.comp hA hB'
      change IndepFun a b (Measure.pi (fun _ : Fin N =>
        (volume : Measure (UnitAddTorus (Fin d)))))
      have hsame : (fun X : Configuration d N => B' (fun k : T => X k)) = b := by
        funext X
        exact Finset.prod_coe_sort T (fun k => q.density (X k))
      change IndepFun a (fun X : Configuration d N => B' (fun k : T => X k)) _ at h
      rw [hsame] at h
      exact h
    have hrepr (X : Configuration d N) :
        |g (X i-X j)| * ProductDensity q.density X = a X * b X := by
      have hprod : (∏ k : Fin N, q.density (X k)) =
          q.density (X i) * q.density (X j) * ∏ k ∈ T, q.density (X k) := by
        have hiu : i ∈ (Finset.univ : Finset (Fin N)) := Finset.mem_univ i
        have hju : j ∈ (Finset.univ.erase i : Finset (Fin N)) := by simp [hij, Ne.symm hij]
        rw [← Finset.mul_prod_erase _ _ hiu, ← Finset.mul_prod_erase _ _ hju]
        ring
      simp only [ProductDensity, hprod, a, b]
      ring
    constructor
    · simp_rw [hrepr]
      exact hinta.mul_bdd hmeasb.aestronglyMeasurable hboundbnorm
    · simp_rw [hrepr]
      rw [hind.integral_fun_mul_eq_mul_integral hmeasa.aestronglyMeasurable hmeasb.aestronglyMeasurable,
        hmassb, mul_one]
      have hpoint : ∀ᵐ X : Configuration d N, a X ≤ u^2 * |g (X i-X j)| := by
        filter_upwards [hcoord i, hcoord j] with X hxi hxj
        dsimp [a]
        calc
          _ ≤ |g (X i-X j)| * u * u := by
            exact mul_le_mul (mul_le_mul_of_nonneg_left hxi.2 (abs_nonneg _)) hxj.2
              hxj.1 (mul_nonneg (abs_nonneg _) (q.one_le_upper.trans' zero_le_one))
          _ = _ := by ring
      calc
        _ ≤ ∫ X : Configuration d N, u^2 * |g (X i-X j)| :=
          integral_mono_ae hinta (hintg.const_mul _) hpoint
        _ = _ := by
          rw [integral_const_mul, configuration_difference_integral d N i j hij
            (fun x => |g x|) hgab]

  classical
  have hbase := pairEnergy_integrable_mean d N hN g hg hi
  have hQ := ProductBackgroundFacts d N l u q
  have hQnonneg : ∀ᵐ X : Configuration d N, 0 ≤ ProductDensity q.density X := by
    filter_upwards [hQ.2.2.2] with X h
    exact (pow_nonneg q.lower_pos.le N).trans h.1
  have hQnorm : ∀ᵐ X : Configuration d N, ‖ProductDensity q.density X‖ ≤ u^N := by
    filter_upwards [hQ.2.2.2,hQnonneg] with X h hn
    simpa only [Real.norm_eq_abs,abs_of_nonneg hn] using h.2
  have hint : Integrable
      (fun X : Configuration d N => |PairEnergy g X| * ProductDensity q.density X) volume :=
    hbase.1.abs.mul_bdd hQ.1.aestronglyMeasurable hQnorm
  refine ⟨hbase.1,hbase.2,hint,?_⟩
  have hp (i j : Fin N) : Integrable
      (fun X : Configuration d N =>
        (if i < j then |g (X i-X j)| else 0) * ProductDensity q.density X) volume := by
    by_cases h : i < j
    · simpa only [h,↓reduceIte] using (weighted_pair_moment d N i j (ne_of_lt h) l u q g hg hi).1
    · simpa only [h,↓reduceIte,zero_mul] using
        (integrable_const (0 : ℝ) : Integrable (fun _ : Configuration d N => (0 : ℝ)) volume)
  have hsum : Integrable
      (fun X : Configuration d N => (N : ℝ)⁻¹ * ∑ i : Fin N, ∑ j : Fin N,
        (if i < j then |g (X i-X j)| else 0) * ProductDensity q.density X) volume :=
    (integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hp i j))).const_mul _
  have htriangle (X : Configuration d N) : |PairEnergy g X| ≤
      (N : ℝ)⁻¹ * ∑ i : Fin N, ∑ j : Fin N,
        if i < j then |g (X i-X j)| else 0 := by
    dsimp [PairEnergy]
    rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg N))
    calc
      _ ≤ ∑ i : Fin N, |∑ j : Fin N, if i < j then g (X i-X j) else 0| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin N, ∑ j : Fin N, |if i < j then g (X i-X j) else 0| :=
        Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ = _ := by simp only [apply_ite,abs_zero]
  have hpoint : ∀ᵐ X : Configuration d N,
      |PairEnergy g X| * ProductDensity q.density X ≤
        (N : ℝ)⁻¹ * ∑ i : Fin N, ∑ j : Fin N,
          (if i < j then |g (X i-X j)| else 0) * ProductDensity q.density X := by
    filter_upwards [hQnonneg] with X h
    calc
      _ ≤ ((N : ℝ)⁻¹ * ∑ i : Fin N, ∑ j : Fin N,
          if i < j then |g (X i-X j)| else 0) * ProductDensity q.density X :=
        mul_le_mul_of_nonneg_right (htriangle X) h
      _ = _ := by simp only [mul_assoc, Finset.sum_mul]
  calc
    _ ≤ ∫ X : Configuration d N, (N : ℝ)⁻¹ * ∑ i : Fin N, ∑ j : Fin N,
        (if i < j then |g (X i-X j)| else 0) * ProductDensity q.density X :=
      integral_mono_ae hint hsum hpoint
    _ = (N : ℝ)⁻¹ * ∑ i : Fin N, ∑ j : Fin N,
        ∫ X : Configuration d N,
          (if i < j then |g (X i-X j)| else 0) * ProductDensity q.density X := by
      rw [integral_const_mul,integral_finsetSum _
        (fun i _ => integrable_finsetSum _ (fun j _ => hp i j))]
      simp_rw [integral_finsetSum _ (fun j _ => hp _ j)]
    _ ≤ (N : ℝ)⁻¹ * ∑ i : Fin N, ∑ j : Fin N,
        (if i < j then (1 : ℝ) else 0) * (u^2 * ∫ x, |g x|) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg N))
      apply Finset.sum_le_sum
      intro i hi'
      apply Finset.sum_le_sum
      intro j hj'
      by_cases h : i < j
      · simpa only [h,↓reduceIte,one_mul] using
          (weighted_pair_moment d N i j (ne_of_lt h) l u q g hg hi).2
      · simp [h]
    _ = _ := by
      simp_rw [← Finset.sum_mul]
      rw [pair_count_real]
      have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
      field_simp
