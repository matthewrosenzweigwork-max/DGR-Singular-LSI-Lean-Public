module

public import Tablet.ParticleInsertion
public import Tablet.RieszKernelBounds
public import Tablet.SoftGibbsNormalization
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic

@[expose] public section
open MeasureTheory Filter Set
open scoped ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

-- [TABLET NODE: NativeGibbsReplacementBalance]
theorem NativeGibbsReplacementBalance (d N : ℕ) (μ : Measure (OneParticle d))
    [IsProbabilityMeasure μ] (s coupling ε : ℝ) (hs : 0 < s)
    (hc : 0 ≤ coupling) (hε : 0 < ε) (i : Fin N) :
    let P := GibbsLaw (N:=N) μ s coupling ε
    let U := fun (X : ParticleConfig d N) (z : OneParticle d) =>
      ∑ j ∈ Finset.univ.erase i, (coupling/(N:ℝ))*RieszKernel s ε (z-ParticlePosition X j)
    let J := (P.prod μ).withDensity (fun q => ENNReal.ofReal (Real.exp (-U q.1 q.2)))
    let S := fun q : ParticleConfig d N × OneParticle d =>
      (ParticleInsertion q.1 i q.2, ParticlePosition q.1 i)
    MeasurePreserving S J J ∧ J.map Prod.fst ≤ P ∧
      J.map (fun q => ParticleInsertion q.1 i q.2) ≤ P := by
-- BODY
  classical
  let replace {Ω : Type} {N : ℕ} (X : Fin N → Ω) (i : Fin N) (z : Ω) : Fin N → Ω := Function.update X i z
  let pairSum {Ω : Type} {N : ℕ} (K : Ω → Ω → ℝ) (X : Fin N → Ω) : ℝ :=
     ∑ k : Fin N, ∑ j : Fin N, if k < j then K (X k) (X j) else 0
  let conditionalPotential {Ω : Type} {N : ℕ} (K : Ω → Ω → ℝ) (a : ℝ)
       (X : Fin N → Ω) (i : Fin N) (z : Ω) : ℝ :=
     a * ∑ j : Fin N, if j = i then 0 else K z (X j)
  have pair_algebra {Ω : Type} {N : ℕ} (K : Ω → Ω → ℝ) (hKs : ∀ x y, K x y = K y x)
       (a : ℝ) (X : Fin N → Ω) :
       (∀ (i : Fin N) (z : Ω),
         a*pairSum K (replace X i z)-a*pairSum K X =
           conditionalPotential K a X i z-conditionalPotential K a X i (X i)) ∧
       (∑ i : Fin N, conditionalPotential K a X i (X i)) = 2*a*pairSum K X := by
    classical
    have heven (x y : Ω) : K y x = K x y := hKs y x
    have hordered (Y : Fin N → Ω) :
        (∑ k : Fin N, ∑ j : Fin N, if j = k then 0 else K (Y k) (Y j)) =
        2 * (∑ k : Fin N, ∑ j : Fin N, if k < j then K (Y k) (Y j) else 0) := by
      have hterm (k j : Fin N) :
          (if j = k then (0 : ℝ) else K (Y k) (Y j)) =
          (if k < j then K (Y k) (Y j) else 0) +
          (if j < k then K (Y j) (Y k) else 0) := by
        rcases lt_trichotomy k j with h | h | h
        · simp [h, ne_of_gt h, not_lt_of_gt h]
        · subst j; simp
        · simp [h, ne_of_lt h, not_lt_of_gt h, heven]
      simp_rw [hterm, Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun k j : Fin N => if j < k then K (Y j) (Y k) else 0)]
      ring
    constructor
    · intro i z
      let D : Fin N → ℝ := fun j => if j = i then 0 else K (z) (X j) - K (X i) (X j)
      have hterm (k j : Fin N) :
          (if j = k then (0 : ℝ) else K ((replace X i z) k) ((replace X i z) j)) -
          (if j = k then 0 else K (X k) (X j)) =
          (if k = i then D j else 0) + (if j = i then D k else 0) := by
        by_cases hk : k = i
        · subst k
          by_cases hj : j = i
          · subst j; simp [D]
          · simp [replace, hj, D]
        · by_cases hj : j = i
          · subst j
            simp [replace, hk, Ne.symm hk, D, heven]
          · simp [replace, hk, hj, D]
      have hdiff :
          (∑ k : Fin N, ∑ j : Fin N,
            if j = k then 0 else K ((replace X i z) k) ((replace X i z) j)) -
          (∑ k : Fin N, ∑ j : Fin N, if j = k then 0 else K (X k) (X j)) =
          2 * ∑ j : Fin N, D j := by
        rw [← Finset.sum_sub_distrib]
        simp_rw [← Finset.sum_sub_distrib, hterm, Finset.sum_add_distrib]
        simp [Finset.sum_ite_irrel]
        ring
      rw [hordered, hordered] at hdiff
      have hpairs :
          (∑ k : Fin N, ∑ j : Fin N,
            if k < j then K ((replace X i z) k) ((replace X i z) j) else 0) -
          (∑ k : Fin N, ∑ j : Fin N, if k < j then K (X k) (X j) else 0) =
          ∑ j : Fin N, D j := by linarith [hdiff]
      have hD : (∑ j : Fin N, D j) =
          (∑ j : Fin N, if j = i then 0 else K (z) (X j)) -
          (∑ j : Fin N, if j = i then 0 else K (X i) (X j)) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        by_cases h : j = i <;> simp [D, h]
      dsimp [pairSum, conditionalPotential]
      calc
        _ = a *
            ((∑ k : Fin N, ∑ j : Fin N,
              if k < j then K ((replace X i z) k) ((replace X i z) j) else 0) -
             (∑ k : Fin N, ∑ j : Fin N, if k < j then K (X k) (X j) else 0)) := by ring
        _ = _ := by rw [hpairs, hD]; ring
    · simp only [conditionalPotential, ← Finset.mul_sum]
      rw [hordered]
      simp only [pairSum]
      ring
  let weight {Ω : Type} {N : ℕ} (K : Ω → Ω → ℝ) (a : ℝ) (X : Fin N → Ω) : ℝ :=
     Real.exp (-a*pairSum K X)
  have conditional_replacement_same {Ω : Type} {N : ℕ} (K : Ω → Ω → ℝ)
       (a : ℝ) (X : Fin N → Ω) (i : Fin N) (z v : Ω) :
       conditionalPotential K a (replace X i z) i v = conditionalPotential K a X i v := by
     classical
     unfold conditionalPotential
     congr 1
     apply Finset.sum_congr rfl
     intro j hj
     by_cases hji : j = i
     · simp [hji]
     · simp only [hji,if_false,replace,Function.update_of_ne hji]
  have weight_exchange {Ω : Type} {N : ℕ} (K : Ω → Ω → ℝ)
       (hKs : ∀ x y, K x y = K y x) (a : ℝ) (X : Fin N → Ω) (i : Fin N) (z : Ω) :
       weight K a X * Real.exp (-conditionalPotential K a X i z) =
         weight K a (replace X i z) * Real.exp (-conditionalPotential K a (replace X i z) i (X i)) := by
     rw [conditional_replacement_same]
     dsimp [weight]
     rw [← Real.exp_add,← Real.exp_add]
     congr 1
     have h := (pair_algebra K hKs a X).1 i z
     linarith
  have replace_twice_same {Ω : Type} {N : ℕ} (X : Fin N → Ω) (i : Fin N) (z v : Ω) :
       replace (replace X i z) i v = replace X i v := by
     classical
     funext j
     by_cases hji : j = i <;> simp [replace,hji]
  have pairSum_measurable {Ω : Type} [MeasurableSpace Ω] {N : ℕ} (K : Ω → Ω → ℝ)
       (hKm : Measurable (fun p : Ω × Ω => K p.1 p.2)) : Measurable (pairSum (N := N) K) := by
     classical
     unfold pairSum
     apply Finset.measurable_fun_sum
     intro i hi
     apply Finset.measurable_fun_sum
     intro j hj
     split_ifs
     · exact hKm.comp ((measurable_pi_apply i : Measurable (fun X : Fin N → Ω => X i)).prodMk
         (measurable_pi_apply j : Measurable (fun X : Fin N → Ω => X j)))
     · exact measurable_const
  have conditionalPotential_joint_measurable {Ω : Type} [MeasurableSpace Ω] {N : ℕ}
       (K : Ω → Ω → ℝ) (hKm : Measurable (fun p : Ω × Ω => K p.1 p.2)) (a : ℝ) (i : Fin N) :
       Measurable (fun p : (Fin N → Ω) × Ω => conditionalPotential K a p.1 i p.2) := by
     classical
     unfold conditionalPotential
     apply Measurable.const_mul
     apply Finset.measurable_fun_sum
     intro j hj
     split_ifs
     · exact measurable_const
     · exact hKm.comp (measurable_snd.prodMk ((measurable_pi_apply j).comp measurable_fst))
  have conditionalPotential_nonnegative {Ω : Type} {N : ℕ} (K : Ω → Ω → ℝ)
       (hKn : ∀ x y, 0 ≤ K x y) (a : ℝ) (ha : 0 ≤ a) (X : Fin N → Ω) (i : Fin N) (z : Ω) :
       0 ≤ conditionalPotential K a X i z := by
     classical
     unfold conditionalPotential
     apply mul_nonneg ha
     exact Finset.sum_nonneg fun j hj => by split_ifs <;> simp_all
  have pairSum_nonnegative {Ω : Type} {N : ℕ} (K : Ω → Ω → ℝ)
       (hKn : ∀ x y, 0 ≤ K x y) (X : Fin N → Ω) : 0 ≤ pairSum K X := by
     classical
     unfold pairSum
     apply Finset.sum_nonneg
     intro i hi
     apply Finset.sum_nonneg
     intro j hj
     split_ifs <;> simp_all
  have replacement_product_swap {Ω : Type} [MeasurableSpace Ω] {N : ℕ}
       (μ : Measure Ω) [SigmaFinite μ] (i : Fin N) :
       let P₀ := Measure.pi (fun _ : Fin N => μ)
       let S := fun v : (Fin N → Ω) × Ω => (replace v.1 i v.2,v.1 i)
       MeasurePreserving S (P₀.prod μ) (P₀.prod μ) ∧
         ∀ F : (Fin N → Ω) × Ω → ℝ,
           (∫ v, F (S v) ∂P₀.prod μ) = ∫ v, F v ∂P₀.prod μ := by
    classical
    dsimp only
    let e := MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin N) => Ω)
    let a := MeasurableEquiv.piCongrLeft (fun _ : Option (Fin N) => Ω) (Equiv.swap none (some i))
    let s := e.symm.trans (a.trans e)
    have he : MeasureTheory.MeasurePreserving e.symm
        ((MeasureTheory.Measure.pi (fun _ : Fin N => μ)).prod μ)
        (MeasureTheory.Measure.pi (fun _ : Option (Fin N) => μ)) := by
      exact ⟨e.symm.measurable, MeasureTheory.Measure.pi_map_piOptionEquivProd (fun _ => μ)⟩
    have ha : MeasureTheory.MeasurePreserving a
        (MeasureTheory.Measure.pi (fun _ : Option (Fin N) => μ))
        (MeasureTheory.Measure.pi (fun _ : Option (Fin N) => μ)) :=
      MeasureTheory.measurePreserving_piCongrLeft (fun _ : Option (Fin N) => μ) _
    have hs : MeasureTheory.MeasurePreserving s
        ((MeasureTheory.Measure.pi (fun _ : Fin N => μ)).prod μ)
        ((MeasureTheory.Measure.pi (fun _ : Fin N => μ)).prod μ) :=
      ((MeasureTheory.MeasurePreserving.symm e.symm he).comp ha).comp he
    have hea (w : Option (Fin N) → Ω) : e w = (fun j => w (some j), w none) := rfl
    have hei0 (v : (Fin N → Ω) × Ω) : e.symm v none = v.2 := rfl
    have hei1 (v : (Fin N → Ω) × Ω) (j : Fin N) : e.symm v (some j) = v.1 j := rfl
    have haa (w : Option (Fin N) → Ω) (j : Option (Fin N)) :
        a w j = w ((Equiv.swap none (some i)) j) := by
      dsimp only [a]
      rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
      simp
    have hsa : ∀ v : (Fin N → Ω) × Ω, s v = (replace v.1 i v.2, v.1 i) := by
      intro v
      change e (a (e.symm v)) = _
      rw [hea]
      apply Prod.ext
      · funext j
        change a (e.symm v) (some j) = replace v.1 i v.2 j
        rw [haa]
        by_cases hj : j = i
        · subst j
          simp only [Equiv.swap_apply_right, hei0, replace, Function.update_self]
        · have hsome : (some j : Option (Fin N)) ≠ some i := fun h => hj (Option.some.inj h)
          rw [Equiv.swap_apply_of_ne_of_ne (Option.some_ne_none j) hsome, hei1]
          simp only [replace, Function.update_of_ne hj]
      · change a (e.symm v) none = v.1 i
        rw [haa, Equiv.swap_apply_left, hei1]
    constructor
    · convert hs using 1
      funext v
      exact (hsa v).symm
    · intro F
      simpa only [hsa] using hs.integral_comp' F
  let partition {Ω : Type} [MeasurableSpace Ω] {N : ℕ}
       (μ : Measure Ω) (K : Ω → Ω → ℝ) (a : ℝ) : ℝ :=
     ∫ X, weight K a X ∂Measure.pi (fun _ : Fin N => μ)
  let gibbsLaw {Ω : Type} [MeasurableSpace Ω] {N : ℕ}
       (μ : Measure Ω) (K : Ω → Ω → ℝ) (a : ℝ) : Measure (Fin N → Ω) :=
     (Measure.pi (fun _ : Fin N => μ)).withDensity
       (fun X => ENNReal.ofReal (weight K a X/partition (N := N) μ K a))
  let jointMeasure {Ω : Type} [MeasurableSpace Ω] {N : ℕ}
       (μ : Measure Ω) (K : Ω → Ω → ℝ) (a : ℝ) (i : Fin N) : Measure ((Fin N → Ω) × Ω) :=
     ((gibbsLaw (N := N) μ K a).prod μ).withDensity
       (fun p => ENNReal.ofReal (Real.exp (-conditionalPotential K a p.1 i p.2)))
  have weight_measurable {Ω : Type} [MeasurableSpace Ω] {N : ℕ} (K : Ω → Ω → ℝ)
       (hKm : Measurable (fun p : Ω × Ω => K p.1 p.2)) (a : ℝ) : Measurable (weight (N := N) K a) :=
     (pairSum_measurable K hKm).const_mul (-a) |>.exp
  have weight_bounds {Ω : Type} {N : ℕ} (K : Ω → Ω → ℝ) (hKn : ∀ x y, 0 ≤ K x y)
       (a : ℝ) (ha : 0 ≤ a) (X : Fin N → Ω) : 0 < weight K a X ∧ weight K a X ≤ 1 := by
     refine ⟨Real.exp_pos _, ?_⟩
     apply Real.exp_le_one_iff.mpr
     simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg ha (pairSum_nonnegative K hKn X))
  have partition_positive {Ω : Type} [MeasurableSpace Ω] {N : ℕ}
       (μ : Measure Ω) [IsProbabilityMeasure μ] (K : Ω → Ω → ℝ)
       (hKm : Measurable (fun p : Ω × Ω => K p.1 p.2)) (hKn : ∀ x y, 0 ≤ K x y)
       (a : ℝ) (ha : 0 ≤ a) :
       Integrable (weight (N := N) K a) (Measure.pi (fun _ : Fin N => μ)) ∧
         0 < partition (N := N) μ K a ∧ partition (N := N) μ K a ≤ 1 := by
     let P₀ := Measure.pi (fun _ : Fin N => μ)
     have hi : Integrable (weight (N := N) K a) P₀ :=
       (integrable_const 1).mono' (weight_measurable K hKm a).aestronglyMeasurable
         (Eventually.of_forall fun X => by
           rw [Real.norm_eq_abs,abs_of_pos (weight_bounds K hKn a ha X).1]
           exact (weight_bounds K hKn a ha X).2)
     have hz : 0 < partition (N := N) μ K a := integral_exp_pos hi
     have hu : partition (N := N) μ K a ≤ 1 := by
       have hh := integral_mono hi (integrable_const (1:ℝ))
         (fun X => (weight_bounds K hKn a ha X).2)
       simpa [partition,P₀] using hh
     exact ⟨hi,hz,hu⟩
  have gibbs_probability {Ω : Type} [MeasurableSpace Ω] {N : ℕ}
       (μ : Measure Ω) [IsProbabilityMeasure μ] (K : Ω → Ω → ℝ)
       (hKm : Measurable (fun p : Ω × Ω => K p.1 p.2)) (hKn : ∀ x y, 0 ≤ K x y)
       (a : ℝ) (ha : 0 ≤ a) : IsProbabilityMeasure (gibbsLaw (N := N) μ K a) := by
     let P₀ := Measure.pi (fun _ : Fin N => μ)
     let Z := partition (N := N) μ K a
     have hw := partition_positive (N := N) μ K hKm hKn a ha
     have hn : ∀ X : Fin N → Ω, 0 ≤ weight K a X/Z := fun X =>
       div_nonneg (weight_bounds K hKn a ha X).1.le hw.2.1.le
     have hint : Integrable (fun X : Fin N → Ω => weight K a X/Z) P₀ := hw.1.div_const Z
     apply isProbabilityMeasure_iff.mpr
     change P₀.withDensity (fun X => ENNReal.ofReal (weight K a X/Z)) univ = 1
     rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
       ← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hn),integral_div]
     change ENNReal.ofReal (Z/Z) = 1
     rw [div_self hw.2.1.ne',ENNReal.ofReal_one]
  have invariant_density_preserving {α : Type} [MeasurableSpace α]
       (ν : Measure α) (S : α → α) (hS : MeasurePreserving S ν ν)
       (ρ : α → ENNReal) (hρ : Measurable ρ) (hρS : ∀ x, ρ (S x) = ρ x) :
       MeasurePreserving S (ν.withDensity ρ) (ν.withDensity ρ) := by
     refine ⟨hS.measurable, ?_⟩
     apply Measure.ext
     intro A hA
     rw [Measure.map_apply hS.measurable hA,withDensity_apply _ (hA.preimage hS.measurable),withDensity_apply _ hA]
     rw [← lintegral_indicator (hA.preimage hS.measurable),← lintegral_indicator hA]
     calc
       _ = ∫⁻ x, A.indicator ρ (S x) ∂ν := by
         apply lintegral_congr_ae
         exact Eventually.of_forall fun x => by
           by_cases hx : S x ∈ A <;> simp [Set.indicator,hx,hρS]
       _ = _ := hS.lintegral_comp (hρ.indicator hA)
  have joint_base_density {Ω : Type} [MeasurableSpace Ω] {N : ℕ}
       (μ : Measure Ω) [IsProbabilityMeasure μ] (K : Ω → Ω → ℝ)
       (hKm : Measurable (fun p : Ω × Ω => K p.1 p.2)) (hKn : ∀ x y, 0 ≤ K x y)
       (a : ℝ) (ha : 0 ≤ a) (i : Fin N) :
       jointMeasure μ K a i = ((Measure.pi (fun _ : Fin N => μ)).prod μ).withDensity
         (fun p => ENNReal.ofReal (weight K a p.1*Real.exp (-conditionalPotential K a p.1 i p.2)/partition (N := N) μ K a)) := by
     let Z := partition (N := N) μ K a
     have hz := (partition_positive (N := N) μ K hKm hKn a ha).2.1
     have hwm := weight_measurable (N := N) K hKm a
     have hrm := (conditionalPotential_joint_measurable K hKm a i).neg.exp
     unfold jointMeasure gibbsLaw
     rw [prod_withDensity_left (hwm.div_const Z).ennreal_ofReal]
     have hd : Measurable (fun p : (Fin N → Ω) × Ω => ENNReal.ofReal (weight K a p.1/Z)) := by
       simpa only [Function.comp_apply] using ((hwm.comp measurable_fst).div_const Z).ennreal_ofReal
     have hr : Measurable (fun p : (Fin N → Ω) × Ω => ENNReal.ofReal (Real.exp (-conditionalPotential K a p.1 i p.2))) := by
       simpa only [Pi.neg_apply] using hrm.ennreal_ofReal
     rw [← withDensity_mul _ hd hr]
     apply withDensity_congr_ae
     exact Eventually.of_forall fun p => by
       change ENNReal.ofReal (weight K a p.1/Z)*ENNReal.ofReal (Real.exp (-conditionalPotential K a p.1 i p.2)) = _
       rw [← ENNReal.ofReal_mul (div_nonneg (weight_bounds K hKn a ha p.1).1.le hz.le)]
       congr 1
       ring
  have replacement_joint_balance {Ω : Type} [MeasurableSpace Ω] {N : ℕ}
       (μ : Measure Ω) [IsProbabilityMeasure μ] (K : Ω → Ω → ℝ)
       (hKm : Measurable (fun p : Ω × Ω => K p.1 p.2)) (hKn : ∀ x y, 0 ≤ K x y)
       (hKs : ∀ x y, K x y = K y x) (a : ℝ) (ha : 0 ≤ a) (i : Fin N) :
       let P := gibbsLaw (N := N) μ K a
       let J := jointMeasure μ K a i
       let S := fun p : (Fin N → Ω) × Ω => (replace p.1 i p.2,p.1 i)
       MeasurePreserving S J J ∧ J.map Prod.fst ≤ P ∧
         J.map (fun p => replace p.1 i p.2) ≤ P ∧
         ((Measure.pi (fun _ : Fin N => μ)).prod μ) ≪ J ∧
         J ≪ ((Measure.pi (fun _ : Fin N => μ)).prod μ) := by
     let P₀ := Measure.pi (fun _ : Fin N => μ)
     let P := gibbsLaw (N := N) μ K a
     let J := jointMeasure μ K a i
     let Z := partition (N := N) μ K a
     let S := fun p : (Fin N → Ω) × Ω => (replace p.1 i p.2,p.1 i)
     let ρ := fun p : (Fin N → Ω) × Ω => ENNReal.ofReal
       (weight K a p.1*Real.exp (-conditionalPotential K a p.1 i p.2)/Z)
     have hz := (partition_positive (N := N) μ K hKm hKn a ha).2.1
     have hwm := weight_measurable (N := N) K hKm a
     have hrm := (conditionalPotential_joint_measurable K hKm a i).neg.exp
     have hρm : Measurable ρ := (((hwm.comp measurable_fst).mul hrm).div_const Z).ennreal_ofReal
     have hρS : ∀ p, ρ (S p) = ρ p := by
       intro p
       dsimp only [ρ,S]
       congr 1
       rw [weight_exchange K hKs a p.1 i p.2]
     have hJ : J = (P₀.prod μ).withDensity ρ := joint_base_density μ K hKm hKn a ha i
     have hJS : MeasurePreserving S J J := by
       rw [hJ]
       exact invariant_density_preserving (P₀.prod μ) S (replacement_product_swap μ i).1 ρ hρm hρS
     haveI : IsProbabilityMeasure P := gibbs_probability μ K hKm hKn a ha
     have hJle : J ≤ P.prod μ := by
       change (P.prod μ).withDensity (fun p => ENNReal.ofReal (Real.exp (-conditionalPotential K a p.1 i p.2))) ≤ P.prod μ
       have hh : (P.prod μ).withDensity (fun p => ENNReal.ofReal (Real.exp (-conditionalPotential K a p.1 i p.2))) ≤
           (P.prod μ).withDensity (fun _ => (1:ENNReal)) := by
         apply withDensity_mono
         exact Eventually.of_forall fun p => by
           simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal
             (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (conditionalPotential_nonnegative K hKn a ha p.1 i p.2)))
       simpa only [withDensity_const,one_smul] using hh
     have hfst : J.map Prod.fst ≤ P := by
       have h := Measure.map_mono hJle measurable_fst
       simpa only [(measurePreserving_fst (μ := P) (ν := μ)).map_eq] using h
     have hnew : J.map (fun p => replace p.1 i p.2) ≤ P := by
       have h := Measure.map_map measurable_fst hJS.measurable (μ := J)
       rw [hJS.map_eq] at h
       change J.map Prod.fst = J.map (fun p => replace p.1 i p.2) at h
       rw [← h]
       exact hfst
     refine ⟨hJS,hfst,hnew,?_,?_⟩
     · change (P₀.prod μ) ≪ J
       rw [hJ]
       apply withDensity_absolutelyContinuous' hρm.aemeasurable
       exact Eventually.of_forall fun p => ne_of_gt (ENNReal.ofReal_pos.mpr
         (div_pos (mul_pos (weight_bounds K hKn a ha p.1).1 (Real.exp_pos _)) hz))
     · change J ≪ (P₀.prod μ)
       rw [hJ]
       exact withDensity_absolutelyContinuous _ _
  let rowFlatten (d N : ℕ) :
      (Fin N → OneParticle d) ≃L[ℝ] ParticleConfig d N :=
    LinearEquiv.toContinuousLinearEquiv
      { toFun := fun Y => WithLp.toLp 2 (fun ik => Y ik.1 ik.2)
        invFun := fun X i => ParticlePosition X i
        left_inv := by intro Y; ext i k; rfl
        right_inv := by intro X; ext ik; rfl
        map_add' := by intro Y Z; ext ik; rfl
        map_smul' := by intro a Y; ext ik; rfl }
  have rowFlatten_position {d N : ℕ} (Y : Fin N → OneParticle d) (i : Fin N) :
      ParticlePosition (rowFlatten d N Y) i = Y i := by ext k; rfl
  let rowFlattenMeasurableEquiv (d N : ℕ) :
      (Fin N → OneParticle d) ≃ᵐ ParticleConfig d N :=
    (rowFlatten d N).toHomeomorph.toMeasurableEquiv
  let softKernel (d : ℕ) (s ε : ℝ) (x y : OneParticle d) := RieszKernel s ε (x-y)
  have map_withDensity_equiv {A C : Type} [MeasurableSpace A] [MeasurableSpace C]
      (e : A ≃ᵐ C) (μ : Measure A) (r : C → ENNReal) (hr : Measurable r) :
      (μ.withDensity (r ∘ e)).map e = (μ.map e).withDensity r := by
    have hp : MeasurePreserving e μ (μ.map e) := ⟨e.measurable,rfl⟩
    ext S hS
    rw [Measure.map_apply e.measurable hS,withDensity_apply _ (e.measurable hS),withDensity_apply _ hS]
    exact hp.setLIntegral_comp_preimage hS hr
  have nativeReference_transport (d N : ℕ) (μ : Measure (OneParticle d)) :
      (Measure.pi (fun _ : Fin N => μ)).map (rowFlattenMeasurableEquiv d N) =
        ConfigurationReference d N μ := rfl
  have nativeKernel_positiveCutoff {d : ℕ} (s ε : ℝ) (_hε : 0 < ε) (x y : OneParticle d) : RieszKernel s ε (x-y)=softKernel d s ε x y := by rfl
  have nativeWeight_transport {d N : ℕ} (s β ε : ℝ) (hε : 0 < ε)
      (Y : Fin N → OneParticle d) :
      InteractionWeight s β ε (rowFlatten d N Y) = weight (softKernel d s ε) (β/(N:ℝ)) Y := by
    have hpair : PairInteraction s β ε (rowFlatten d N Y) =
        (β/(N:ℝ))*pairSum (softKernel d s ε) Y := by
      unfold PairInteraction pairSum
      simp only [rowFlatten_position,nativeKernel_positiveCutoff s ε hε]
    unfold InteractionWeight weight
    simp only [ne_of_gt hε,false_and,if_false,hpair]
    split_ifs with hβ
    · simp [hβ]
    · rw [neg_mul]
  have nativeWeight_measurable {d N : ℕ} (s β ε : ℝ) (hε : 0 < ε) :
      Measurable (InteractionWeight (d := d) (N := N) s β ε) := by
    have hm : Measurable (fun p : OneParticle d × OneParticle d => softKernel d s ε p.1 p.2) := by
      unfold softKernel RieszKernel
      split_ifs <;> fun_prop
    have he : InteractionWeight (d := d) (N := N) s β ε =
        weight (softKernel d s ε) (β/(N:ℝ)) ∘ (rowFlattenMeasurableEquiv d N).symm := by
      funext X
      exact (nativeWeight_transport s β ε hε ((rowFlatten d N).symm X))
    rw [he]
    exact (weight_measurable _ hm _).comp (rowFlattenMeasurableEquiv d N).symm.measurable
  have nativePartition_transport {d N : ℕ} (μ : Measure (OneParticle d))
      (s β ε : ℝ) (hε : 0 < ε) :
      GibbsPartition (N := N) μ s β ε = partition (N := N) μ (softKernel d s ε) (β/(N:ℝ)) := by
    unfold GibbsPartition partition
    rw [← nativeReference_transport d N μ,integral_map_equiv]
    apply integral_congr_ae
    exact Eventually.of_forall fun Y => nativeWeight_transport s β ε hε Y
  have nativeGibbsLaw_transport {d N : ℕ} (μ : Measure (OneParticle d))
      (s β ε : ℝ) (hε : 0 < ε) :
      (gibbsLaw (N := N) μ (softKernel d s ε) (β/(N:ℝ))).map (rowFlattenMeasurableEquiv d N) =
        GibbsLaw (N := N) μ s β ε := by
    let r := fun X : ParticleConfig d N => ENNReal.ofReal
      ((GibbsPartition (N := N) μ s β ε)⁻¹ * InteractionWeight s β ε X)
    have hr : Measurable r := ((nativeWeight_measurable s β ε hε).const_mul _).ennreal_ofReal
    have he : (fun Y : Fin N → OneParticle d => ENNReal.ofReal
        (weight (softKernel d s ε) (β/(N:ℝ)) Y / partition (N := N) μ (softKernel d s ε) (β/(N:ℝ)))) =
          r ∘ rowFlattenMeasurableEquiv d N := by
      funext Y
      change ENNReal.ofReal (_ / _) = ENNReal.ofReal
        ((GibbsPartition (N := N) μ s β ε)⁻¹ * InteractionWeight s β ε (rowFlatten d N Y))
      rw [nativePartition_transport μ s β ε hε,nativeWeight_transport s β ε hε]
      congr 1
      ring
    unfold gibbsLaw
    rw [he,map_withDensity_equiv _ _ _ hr,nativeReference_transport]
    rfl
  dsimp only
  let a := coupling/(N:ℝ)
  let K := softKernel d s ε
  let Pr := gibbsLaw (N:=N) μ K a
  let P := GibbsLaw (N:=N) μ s coupling ε
  let U := fun (X : ParticleConfig d N) (z : OneParticle d) =>
    ∑ j ∈ Finset.univ.erase i, a*RieszKernel s ε (z-ParticlePosition X j)
  let J := (P.prod μ).withDensity (fun q => ENNReal.ofReal (Real.exp (-U q.1 q.2)))
  let S := fun q : ParticleConfig d N × OneParticle d =>
    (ParticleInsertion q.1 i q.2, ParticlePosition q.1 i)
  let F := (rowFlattenMeasurableEquiv d N).prodCongr (MeasurableEquiv.refl (OneParticle d))
  have hKm : Measurable (fun q : OneParticle d × OneParticle d => K q.1 q.2) := by
    dsimp [K, softKernel]
    simp only [RieszKernel, ne_of_gt hε, if_false]
    fun_prop
  have hKn (x y : OneParticle d) : 0 ≤ K x y := (RieszKernelBounds s ε hs hε.le).1 (x-y)
  have hKs (x y : OneParticle d) : K x y=K y x := by
    dsimp [K, softKernel]; simp only [RieszKernel, ne_of_gt hε, if_false, norm_sub_rev]
  have ha : 0 ≤ a := div_nonneg hc (Nat.cast_nonneg N)
  have hUeq (Y : Fin N → OneParticle d) (z : OneParticle d) :
      U (rowFlatten d N Y) z = conditionalPotential K a Y i z := by
    have he : Finset.univ.erase i = Finset.univ.filter (fun j : Fin N => j ≠ i) := by ext j; simp
    dsimp [U,conditionalPotential]
    rw [he, Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hji : j=i
    · simp [hji]
    · simp [hji, rowFlatten_position, K, softKernel]
  have hUeqAll (q : (Fin N → OneParticle d) × OneParticle d) :
    Real.exp (-U (F q).1 (F q).2)=Real.exp (-conditionalPotential K a q.1 i q.2) := by
    exact congrArg (fun v : ℝ => Real.exp (-v)) (hUeq q.1 q.2)
  have hr : Measurable (fun q : ParticleConfig d N × OneParticle d =>
      ENNReal.ofReal (Real.exp (-U q.1 q.2))) := by
    have hm : Measurable (fun q : (Fin N → OneParticle d) × OneParticle d =>
      ENNReal.ofReal (Real.exp (-conditionalPotential K a q.1 i q.2))) :=
      (conditionalPotential_joint_measurable K hKm a i).neg.exp.ennreal_ofReal
    have he : (fun q : ParticleConfig d N × OneParticle d => ENNReal.ofReal (Real.exp (-U q.1 q.2))) =
      (fun q => ENNReal.ofReal (Real.exp (-conditionalPotential K a q.1 i q.2))) ∘ F.symm := by
      funext q
      have h := hUeqAll (F.symm q)
      simpa only [F.apply_symm_apply,Function.comp_def] using congrArg ENNReal.ofReal h
    rw [he]; exact hm.comp F.symm.measurable
  have hP : Pr.map (rowFlattenMeasurableEquiv d N)=P := nativeGibbsLaw_transport μ s coupling ε hε
  haveI : IsProbabilityMeasure Pr := gibbs_probability μ K hKm hKn a ha
  have hProd : (Pr.prod μ).map F=P.prod μ := by
    change (Pr.prod μ).map (Prod.map (rowFlattenMeasurableEquiv d N) id)=_
    rw [← Measure.map_prod_map _ _ (rowFlattenMeasurableEquiv d N).measurable measurable_id, Measure.map_id, hP]
  have hF : MeasurePreserving F (jointMeasure μ K a i) J := by
    refine ⟨F.measurable,?_⟩
    unfold jointMeasure
    have he : (fun q : (Fin N → OneParticle d) × OneParticle d => ENNReal.ofReal (Real.exp (-conditionalPotential K a q.1 i q.2))) =
        (fun q => ENNReal.ofReal (Real.exp (-U q.1 q.2))) ∘ F := by
      funext q; exact (congrArg ENNReal.ofReal (hUeqAll q)).symm
    rw [he,map_withDensity_equiv F (Pr.prod μ) _ hr,hProd]
  have hSrc := (replacement_joint_balance μ K hKm hKn hKs a ha i).1
  have hConj := (hF.comp hSrc).comp (MeasurePreserving.symm F hF)
  have hSwap : MeasurePreserving S J J := by
    convert hConj using 1
    funext q
    apply Prod.ext
    · ext jk
      change (if jk.1=i then q.2 jk.2 else q.1 jk) =
        replace ((rowFlatten d N).symm q.1) i q.2 jk.1 jk.2
      simp only [replace, Function.update_apply]
      split_ifs <;> rfl
    · ext k; rfl
  haveI : IsProbabilityMeasure P := (SoftGibbsNormalization μ s coupling ε hs hc hε).2.2
  have hle : J ≤ P.prod μ := by
    have hUn (q : ParticleConfig d N × OneParticle d) : 0 ≤ U q.1 q.2 := by
      dsimp [U]; exact Finset.sum_nonneg (fun j hj => mul_nonneg ha ((RieszKernelBounds s ε hs hε.le).1 _))
    have h := withDensity_mono (μ:=P.prod μ) (Eventually.of_forall fun q =>
      ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hUn q))))
    simpa only [ENNReal.ofReal_one,withDensity_const,one_smul] using h
  have hOld : J.map Prod.fst ≤ P := by
    have h := Measure.map_mono hle measurable_fst
    simpa only [(measurePreserving_fst (μ:=P) (ν:=μ)).map_eq] using h
  have hNew : J.map (fun q => ParticleInsertion q.1 i q.2) ≤ P := by
    have h := Measure.map_map measurable_fst hSwap.measurable (μ:=J)
    rw [hSwap.map_eq] at h
    change J.map Prod.fst=J.map (fun q => ParticleInsertion q.1 i q.2) at h
    rw [←h]; exact hOld
  exact ⟨hSwap,hOld,hNew⟩
