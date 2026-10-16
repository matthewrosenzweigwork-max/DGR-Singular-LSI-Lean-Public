module

public import Tablet.ReplacementRectangle
public import Tablet.MayerConvolutionBounds
public import Tablet.JumpL2Extension
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

@[expose] public section
open MeasureTheory Filter Set
set_option maxHeartbeats 1500000
-- [TABLET NODE: ReplacementCoercivity]
theorem ReplacementCoercivity (d N : ℕ) (hN : 2 ≤ N) (l u B β : ℝ)
    (q : BoundedBackground d l u) (hB : 0 ≤ B) (hβ : 0 ≤ β) (hβB : β ≤ B)
    (G : UnitAddTorus (Fin d) → ℝ) (hG : Measurable G)
    (hGi : MeasureTheory.Integrable G MeasureTheory.volume)
    (hGn : ∀ x, 0 ≤ G x) (hGe : ∀ x, G (-x) = G x)
    (hF : ∀ k : Fin d → ℤ,
      0 ≤ ∫ x, G x * (UnitAddTorus.mFourier k x).re)
    (f : Configuration d N → ℝ)
    (hf : MeasureTheory.MemLp f 2 (CanonicalLaw (N := N) G q.density β)) :
    let m := (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d)))
    let P := CanonicalLaw (N := N) G q.density β
    let c := ∫ x, G x ∂m
    let η := fun a : ℝ => MayerDefect m G a / a
    (Real.exp (-B * u * c) -
      2 * u * (B * c / N + B * η (B / N))) *
      (-(∫ X, f X * JumpOperator G q.density β f X ∂P)) ≤
      ∫ X, (JumpOperator G q.density β f X)^2 ∂P := by
-- BODY
  have finite_remainder {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (N : ℕ) (T : H →L[ℝ] H) (r c : ℝ) (hr : 0 ≤ r) (hc : 0 ≤ c)
      (hT : ‖T‖ ≤ c) (hlo : ∀ v, -r * ‖v‖^2 ≤ inner ℝ v (T v)) (F : Fin N → H) :
      -(N * r + c) * (∑ i, ‖F i‖ ^ 2) ≤
        (∑ i, ∑ j, if i = j then 0 else inner ℝ (F i) (T (F j))) := by
    have hnorm : ‖∑ i, F i‖ ^ 2 ≤ (N : ℝ) * ∑ i, ‖F i‖ ^ 2 := by
      calc
        _ ≤ (∑ i, ‖F i‖) ^ 2 := by gcongr; exact norm_sum_le _ _
        _ ≤ _ := by simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖F i‖)
    have hdiag (i : Fin N) : inner ℝ (F i) (T (F i)) ≤ c * ‖F i‖ ^ 2 := by
      calc
        _ ≤ ‖F i‖ * ‖T (F i)‖ := real_inner_le_norm _ _
        _ ≤ ‖F i‖ * (c * ‖F i‖) := mul_le_mul_of_nonneg_left
          ((T.le_opNorm (F i)).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))) (norm_nonneg _)
        _ = _ := by ring
    have hsum : ∑ i, inner ℝ (F i) (T (F i)) ≤ c * ∑ i, ‖F i‖ ^ 2 := by
      simpa only [Finset.mul_sum] using Finset.sum_le_sum (fun i _ => hdiag i)
    have hid : inner ℝ (∑ i, F i) (T (∑ i, F i)) =
        (∑ i, ∑ j, if i = j then 0 else inner ℝ (F i) (T (F j))) +
        ∑ i, inner ℝ (F i) (T (F i)) := by
      simp only [map_sum]
      rw [sum_inner]
      simp_rw [inner_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      have hh : (∑ j : Fin N, if i = j then inner ℝ (F i) (T (F j)) else 0) =
          inner ℝ (F i) (T (F i)) := by simp
      rw [← hh, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp_all
    have hlo' := hlo (∑ i, F i)
    have hn := mul_le_mul_of_nonpos_left hnorm (neg_nonpos.mpr hr)
    rw [hid] at hlo'
    nlinarith

  have torus_cross (d N : ℕ) (G : UnitAddTorus (Fin d) → ℝ)
      (hG : Measurable G) (hGn : ∀ x, 0 ≤ G x) (a : ℝ) (ha : 0 ≤ a)
      (T : Lp ℝ 2 (volume : Measure (UnitAddTorus (Fin d))) →L[ℝ]
        Lp ℝ 2 (volume : Measure (UnitAddTorus (Fin d))))
      (r c : ℝ) (hr : 0 ≤ r) (hc : 0 ≤ c) (hT : ‖T‖ ≤ c)
      (hlo : ∀ v, -r * ‖v‖^2 ≤ inner ℝ v (T v))
      (hrep : ∀ (f : UnitAddTorus (Fin d) → ℝ) (hf : MemLp f 2 volume),
        ⇑(T (hf.toLp f)) =ᵐ[volume]
          fun x => ∫ y, (1 - Real.exp (-a * G (x-y))) * f y)
      (F : Fin N → UnitAddTorus (Fin d) → ℝ) (hF : ∀ i, MemLp (F i) 2 volume) :
      (∑ i, (∫ z, F i z)^2) +
        (∑ i, ∑ j, if i = j then 0 else
          ∫ z, ∫ v, Real.exp (-a * G (z-v)) * F i z * F j v) -
        (N * r + c) * (∑ i, ∫ z, (F i z)^2) ≤
      (∑ i, ∫ z, F i z)^2 := by
    classical
    haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
      rw [AddCircle.volume_eq_smul_haarAddCircle]
      simp
      infer_instance
    let m : Measure (UnitAddTorus (Fin d)) := volume
    let K := fun x => 1 - Real.exp (-a * G x)
    have hK : ∀ x, 0 ≤ K x ∧ K x ≤ 1 := by
      intro x
      have he : Real.exp (-a * G x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg ha (hGn x)])
      have hp := (Real.exp_pos (-a * G x)).le
      dsimp [K]
      constructor <;> linarith
    have hKmeas : Measurable K := measurable_const.sub (Real.measurable_exp.comp (measurable_const.mul hG))
    have hi (i : Fin N) : Integrable (F i) m := (hF i).integrable (by norm_num)
    have hprod (i j : Fin N) : Integrable (fun p : UnitAddTorus (Fin d) × UnitAddTorus (Fin d) => F i p.1 * F j p.2) (m.prod m) :=
      (hi i).mul_prod (hi j)
    have hkprod (i j : Fin N) : Integrable (fun p : UnitAddTorus (Fin d) × UnitAddTorus (Fin d) => K (p.1-p.2) * F i p.1 * F j p.2) (m.prod m) := by
      simpa only [mul_assoc, Function.comp_apply, Pi.sub_apply] using (hprod i j).bdd_mul
        (hKmeas.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable
        (Eventually.of_forall fun p => by simpa [Real.norm_eq_abs, abs_of_nonneg (hK (p.1-p.2)).1] using (hK (p.1-p.2)).2)
    have heprod (i j : Fin N) : Integrable (fun p : UnitAddTorus (Fin d) × UnitAddTorus (Fin d) => Real.exp (-a*G (p.1-p.2)) * F i p.1 * F j p.2) (m.prod m) := by
      simpa only [mul_assoc, Function.comp_apply, Pi.mul_apply, Pi.sub_apply] using (hprod i j).bdd_mul
        ((Real.measurable_exp.comp (measurable_const.mul (hG.comp (measurable_fst.sub measurable_snd)))).aestronglyMeasurable)
        (Eventually.of_forall fun p => by
          change ‖Real.exp (-a * G (p.1-p.2))‖ ≤ (1 : ℝ)
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg ha (hGn (p.1-p.2))]))
    let V := fun i => (hF i).toLp (F i)
    have hinner (i j : Fin N) : inner ℝ (V i) (T (V j)) =
        ∫ z, ∫ v, K (z-v) * F i z * F j v ∂m ∂m := by
      rw [L2.inner_def]
      have hc : (fun z => inner ℝ ((V i) z) ((T (V j)) z)) =ᵐ[m]
          fun z => F i z * (∫ v, K (z-v) * F j v ∂m) := by
        filter_upwards [(hF i).coeFn_toLp, hrep (F j) (hF j)] with z hz ht
        simp [V, hz, ht, RCLike.inner_apply, mul_comm, K, m]
      rw [integral_congr_ae hc]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        dsimp only
        rw [← integral_const_mul]
        congr 1
        funext v
        ring
    have hsquare (i : Fin N) : ‖V i‖^2 = ∫ z, (F i z)^2 ∂m := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(hF i).coeFn_toLp] with z hz
      simp [V, hz, RCLike.inner_apply, pow_two]
    have hsplit (i j : Fin N) :
        (∫ z, F i z ∂m) * (∫ v, F j v ∂m) =
        (∫ z, ∫ v, Real.exp (-a*G (z-v)) * F i z * F j v ∂m ∂m) +
        inner ℝ (V i) (T (V j)) := by
      rw [hinner, integral_integral (f := fun z v => Real.exp (-a*G (z-v))*F i z*F j v) (heprod i j), integral_integral (f := fun z v => K (z-v)*F i z*F j v) (hkprod i j),
        ← integral_add (heprod i j) (hkprod i j)]
      calc
        _ = ∫ p, F i p.1 * F j p.2 ∂m.prod m := (integral_prod_mul (μ := m) (ν := m) (F i) (F j)).symm
        _ = _ := by apply integral_congr_ae; exact Eventually.of_forall fun p => by dsimp [K]; ring
    have hfinite := finite_remainder N T r c hr hc hT hlo V
    simp_rw [hsquare] at hfinite
    have halgebra : (∑ i, ∫ z, F i z ∂m)^2 =
        (∑ i, (∫ z, F i z ∂m)^2) +
        (∑ i, ∑ j, if i = j then 0 else
          ∫ z, ∫ v, Real.exp (-a*G (z-v)) * F i z * F j v ∂m ∂m) +
        (∑ i, ∑ j, if i = j then 0 else inner ℝ (V i) (T (V j))) := by
      rw [pow_two, Finset.sum_mul_sum]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      have hd : (∫ z, F i z ∂m)^2 = ∑ j : Fin N, if i=j then (∫ z, F i z ∂m)*(∫ v, F j v ∂m) else 0 := by simp [pow_two]
      rw [hd, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs with h
      · subst j; simp
      · simpa using hsplit i j
    rw [halgebra]
    linarith

  have integrated_cross {X : Type} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
      (d N : ℕ) (G : UnitAddTorus (Fin d) → ℝ) (hG : Measurable G) (hGn : ∀ x, 0 ≤ G x)
      (a : ℝ) (ha : 0 ≤ a)
      (T : Lp ℝ 2 (volume : Measure (UnitAddTorus (Fin d))) →L[ℝ] Lp ℝ 2 volume)
      (r c : ℝ) (hr : 0 ≤ r) (hc : 0 ≤ c) (hT : ‖T‖ ≤ c)
      (hlo : ∀ v, -r * ‖v‖^2 ≤ inner ℝ v (T v))
      (hrep : ∀ (f : UnitAddTorus (Fin d) → ℝ) (hf : MemLp f 2 volume),
        ⇑(T (hf.toLp f)) =ᵐ[volume] fun x => ∫ y, (1-Real.exp (-a*G (x-y)))*f y)
      (F : X → Fin N → UnitAddTorus (Fin d) → ℝ)
      (hFm : ∀ i, Measurable (fun w : X × UnitAddTorus (Fin d) => F w.1 i w.2))
      (D : ℝ) (hD : 0 ≤ D) (hFb : ∀ x i, ∀ᵐ z ∂volume, ‖F x i z‖ ≤ D)
      (hC : ∀ i j, i ≠ j → 0 ≤ ∫ x, ∫ z, ∫ v,
        Real.exp (-a*G (z-v))*F x i z*F x j v ∂volume ∂volume ∂P) :
      (∑ i, ∫ x, (∫ z, F x i z)^2 ∂P) -
        (N*r+c)*(∑ i, ∫ x, ∫ z, (F x i z)^2 ∂volume ∂P) ≤
        ∫ x, (∑ i, ∫ z, F x i z)^2 ∂P := by
    classical
    haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
      rw [AddCircle.volume_eq_smul_haarAddCircle]; simp; infer_instance
    let m : Measure (UnitAddTorus (Fin d)) := volume
    let A := fun x i => ∫ z, F x i z ∂m
    let Q := fun x i => ∫ z, (F x i z)^2 ∂m
    let C := fun x i j => ∫ z, ∫ v, Real.exp (-a*G (z-v))*F x i z*F x j v ∂m ∂m
    have hFi x i : MemLp (F x i) 2 m :=
      MemLp.of_bound ((hFm i).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable D (hFb x i)
    have hAb x i : ‖A x i‖ ≤ D := by
      simpa [A] using norm_integral_le_of_norm_le_const (hFb x i)
    have hAm i : Measurable (fun x => A x i) := (hFm i).stronglyMeasurable.integral_prod_right'.measurable
    have hQm i : Measurable (fun x => Q x i) := ((hFm i).pow_const 2).stronglyMeasurable.integral_prod_right'.measurable
    have hQb x i : ‖Q x i‖ ≤ D^2 := by
      have hh : ∀ᵐ z ∂m, ‖(F x i z)^2‖ ≤ D^2 := by
        filter_upwards [hFb x i] with z hz
        simpa [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) hz 2
      simpa [Q] using norm_integral_le_of_norm_le_const hh
    have hCm i j : Measurable (fun x => C x i j) := by
      have he : Measurable (fun w : (X × UnitAddTorus (Fin d)) × UnitAddTorus (Fin d) => Real.exp (-a*G (w.1.2-w.2))) :=
        ((hG.comp ((measurable_snd.comp measurable_fst).sub measurable_snd)).const_mul (-a)).exp
      have hi : Measurable (fun w : (X × UnitAddTorus (Fin d)) × UnitAddTorus (Fin d) => F w.1.1 i w.1.2) := (hFm i).comp measurable_fst
      have hj : Measurable (fun w : (X × UnitAddTorus (Fin d)) × UnitAddTorus (Fin d) => F w.1.1 j w.2) := (hFm j).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
      exact ((he.mul hi).mul hj).stronglyMeasurable.integral_prod_right'.integral_prod_right'.measurable
    have hCb x i j : ‖C x i j‖ ≤ D^2 := by
      have hh : ∀ᵐ z ∂m, ‖∫ v, Real.exp (-a*G (z-v))*F x i z*F x j v ∂m‖ ≤ D^2 := by
        filter_upwards [hFb x i] with z hz
        have hvb : ∀ᵐ v ∂m, ‖Real.exp (-a*G (z-v))*F x i z*F x j v‖ ≤ D^2 := by
          filter_upwards [hFb x j] with v hv
          have he0 := (Real.exp_pos (-a*G (z-v))).le
          have he1 : Real.exp (-a*G (z-v)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg ha (hGn (z-v))])
          rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg he0]
          calc
            _ ≤ 1 * D * D := mul_le_mul (mul_le_mul he1 hz (norm_nonneg _) (by norm_num)) hv (norm_nonneg _) (by simpa using hD)
            _ = _ := by ring
        simpa using norm_integral_le_of_norm_le_const hvb
      simpa [C] using norm_integral_le_of_norm_le_const hh
    have hAi i : Integrable (fun x => (A x i)^2) P := Integrable.of_bound ((hAm i).pow_const 2).aestronglyMeasurable (D^2)
      (Eventually.of_forall fun x => by simpa [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) (hAb x i) 2)
    have hQi i : Integrable (fun x => Q x i) P := Integrable.of_bound (hQm i).aestronglyMeasurable (D^2) (Eventually.of_forall fun x => hQb x i)
    have hCi i j : Integrable (fun x => C x i j) P := Integrable.of_bound (hCm i j).aestronglyMeasurable (D^2) (Eventually.of_forall fun x => hCb x i j)
    have hCrossi : Integrable (fun x => ∑ i, ∑ j, if i=j then 0 else C x i j) P := by
      apply integrable_finset_sum
      intro i _
      apply integrable_finset_sum
      intro j _
      split_ifs
      · exact integrable_zero _ _ _
      · exact hCi i j
    have hSumi : Integrable (fun x => (∑ i, A x i)^2) P := by
      apply Integrable.of_bound ((Finset.measurable_fun_sum _ fun i _ => hAm i).pow_const 2).aestronglyMeasurable ((N*D)^2)
      apply Eventually.of_forall
      intro x
      rw [norm_pow]
      apply pow_le_pow_left₀ (norm_nonneg _)
      calc
        ‖∑ i, A x i‖ ≤ ∑ i, ‖A x i‖ := norm_sum_le _ _
        _ ≤ ∑ i : Fin N, D := Finset.sum_le_sum fun i _ => hAb x i
        _ = _ := by simp
    have hint := integral_mono ((integrable_finset_sum _ fun i _ => hAi i).add hCrossi |>.sub
        ((integrable_finset_sum _ fun i _ => hQi i).const_mul (N*r+c))) hSumi
      (fun x => torus_cross d N G hG hGn a ha T r c hr hc hT hlo hrep (F x) (hFi x))
    have hCrosspos : 0 ≤ ∫ x, (∑ i, ∑ j, if i=j then 0 else C x i j) ∂P := by
      rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ => by split_ifs; exact integrable_zero _ _ _; exact hCi i j)]
      apply Finset.sum_nonneg
      intro i _
      rw [integral_finset_sum _ (fun j _ => by split_ifs; exact integrable_zero _ _ _; exact hCi i j)]
      apply Finset.sum_nonneg
      intro j _
      by_cases hij : i=j
      · simp [hij]
      · simpa [hij, C, m] using hC i j hij
    dsimp only [Pi.add_apply, Pi.sub_apply] at hint
    rw [integral_sub, integral_add, integral_const_mul,
      integral_finset_sum _ (fun i _ => hAi i), integral_finset_sum _ (fun i _ => hQi i)] at hint
    · change (∑ i, ∫ x, (A x i)^2 ∂P) - (N*r+c)*(∑ i, ∫ x, Q x i ∂P) ≤ _
      exact le_trans (by linarith) hint
    all_goals first | exact integrable_finset_sum _ fun i _ => hAi i | exact hCrossi | exact integrable_finset_sum _ fun i _ => hQi i | exact (integrable_finset_sum _ fun i _ => hAi i).add hCrossi | exact (integrable_finset_sum _ fun i _ => hQi i).const_mul _

  have rows (d N : ℕ) (hN : 2 ≤ N) (l u β : ℝ)
      (q : BoundedBackground d l u) (hβ : 0 ≤ β)
      (G : UnitAddTorus (Fin d) → ℝ) (hG : Measurable G) (hGi : Integrable G volume)
      (hGn : ∀ x, 0 ≤ G x) (hGe : ∀ x, G (-x) = G x)
      (f : Configuration d N → ℝ) (hfm : Measurable f) (C : ℝ) (hfC : ∀ X, |f X| ≤ C) :
      let P := CanonicalLaw (N := N) G q.density β
      let F := fun X i z => Real.exp (-ConditionalPotential G β X i z) *
        (f (Replacement X i z)-f X)*q.density z
      let H := fun X i z => Real.exp (-ConditionalPotential G β X i z) *
        (f (Replacement X i z)-f X)^2*q.density z
      (∀ i, Measurable (fun w : Configuration d N × UnitAddTorus (Fin d) => F w.1 i w.2)) ∧
      (∀ X i, ∀ᵐ z ∂volume, ‖F X i z‖ ≤ 2*u*C) ∧
      (∀ i, Integrable (fun X => ∫ z, (F X i z)^2) P) ∧
      (∀ i, Integrable (fun X => ∫ z, H X i z) P) ∧
      (∑ i, ∫ X, ∫ z, (F X i z)^2 ∂volume ∂P) ≤
        u * (∑ i, ∫ X, ∫ z, H X i z ∂volume ∂P) := by
    classical
    haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
      rw [AddCircle.volume_eq_smul_haarAddCircle]; simp; infer_instance
    let m : Measure (UnitAddTorus (Fin d)) := volume
    let P := CanonicalLaw (N := N) G q.density β
    haveI : IsProbabilityMeasure P := (JumpConditionalBalance d N hN l u β q hβ G hG hGi hGn hGe).1
    let U := ConditionalPotential (N := N) G β
    let D := fun X i z => f (Replacement X i z)-f X
    let F := fun X i z => Real.exp (-U X i z)*D X i z*q.density z
    let H := fun X i z => Real.exp (-U X i z)*(D X i z)^2*q.density z
    have hC : 0 ≤ C := (abs_nonneg (f 0)).trans (hfC 0)
    have hu : 0 ≤ u := zero_le_one.trans q.one_le_upper
    have hDm (i : Fin N) : Measurable (fun w : Configuration d N × UnitAddTorus (Fin d) => D w.1 i w.2) := by
      exact (hfm.comp (show Measurable (fun w : Configuration d N × UnitAddTorus (Fin d) => Replacement w.1 i w.2) from measurable_update')).sub (hfm.comp measurable_fst)
    have hDb X i z : |D X i z| ≤ 2*C := by
      exact (abs_sub _ _).trans (by linarith [hfC (Replacement X i z), hfC X])
    have hUm (i : Fin N) : Measurable (fun w : Configuration d N × UnitAddTorus (Fin d) => U w.1 i w.2) := by
      unfold U ConditionalPotential
      refine measurable_const.mul (Finset.measurable_fun_sum _ fun j _ => ?_)
      split_ifs
      · exact measurable_const
      · exact hG.comp (measurable_snd.sub ((measurable_pi_apply j).comp measurable_fst))
    have hUn X i z : 0 ≤ U X i z := by
      unfold U ConditionalPotential
      exact mul_nonneg (div_nonneg hβ (Nat.cast_nonneg N)) (Finset.sum_nonneg fun j _ => by split_ifs; exact le_rfl; exact hGn _)
    have hE0 X i z : 0 ≤ Real.exp (-U X i z) := (Real.exp_pos _).le
    have hE1 X i z : Real.exp (-U X i z) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hUn X i z))
    have hFm (i : Fin N) : Measurable (fun w : Configuration d N × UnitAddTorus (Fin d) => F w.1 i w.2) :=
      (((hUm i).neg.exp).mul (hDm i)).mul (q.measurable.comp measurable_snd)
    have hHm (i : Fin N) : Measurable (fun w : Configuration d N × UnitAddTorus (Fin d) => H w.1 i w.2) :=
      (((hUm i).neg.exp).mul ((hDm i).pow_const 2)).mul (q.measurable.comp measurable_snd)
    have hFb X i : ∀ᵐ z ∂m, ‖F X i z‖ ≤ 2*u*C := by
      filter_upwards [q.bounds] with z hz
      have hq0 := q.lower_pos.le.trans hz.1
      dsimp only [F]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hE0 X i z), abs_of_nonneg hq0]
      calc
        _ ≤ 1*(2*C)*u := mul_le_mul (mul_le_mul (hE1 X i z) (hDb X i z) (abs_nonneg _) (by norm_num)) hz.2 hq0 (by positivity)
        _ = _ := by ring
    have hHb X i : ∀ᵐ z ∂m, ‖H X i z‖ ≤ u*(2*C)^2 := by
      filter_upwards [q.bounds] with z hz
      have hq0 := q.lower_pos.le.trans hz.1
      dsimp only [H]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hE0 X i z), abs_of_nonneg (sq_nonneg _), abs_of_nonneg hq0]
      have hd : (D X i z)^2 ≤ (2*C)^2 := by nlinarith [hDb X i z, le_abs_self (D X i z), neg_le_abs (D X i z)]
      calc
        _ ≤ 1*(2*C)^2*u := mul_le_mul (mul_le_mul (hE1 X i z) hd (sq_nonneg _) (by norm_num)) hz.2 hq0 (by positivity)
        _ = _ := by ring
    have hFi X i : MemLp (F X i) 2 m := MemLp.of_bound ((hFm i).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable (2*u*C) (hFb X i)
    have hHi X i : Integrable (H X i) m := Integrable.of_bound ((hHm i).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable (u*(2*C)^2) (hHb X i)
    have hQb X i : ‖∫ z, (F X i z)^2 ∂m‖ ≤ (2*u*C)^2 := by
      have hh : ∀ᵐ z ∂m, ‖(F X i z)^2‖ ≤ (2*u*C)^2 := by
        filter_upwards [hFb X i] with z hz
        simpa [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) hz 2
      simpa using norm_integral_le_of_norm_le_const hh
    have hQI i : Integrable (fun X => ∫ z, (F X i z)^2 ∂m) P :=
      Integrable.of_bound (((hFm i).pow_const 2).stronglyMeasurable.integral_prod_right').aestronglyMeasurable ((2*u*C)^2) (Eventually.of_forall fun X => hQb X i)
    have hHI i : Integrable (fun X => ∫ z, H X i z ∂m) P :=
      Integrable.of_bound ((hHm i).stronglyMeasurable.integral_prod_right').aestronglyMeasurable (u*(2*C)^2)
        (Eventually.of_forall fun X => by simpa using norm_integral_le_of_norm_le_const (hHb X i))
    refine ⟨hFm, hFb, hQI, hHI, ?_⟩
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← integral_const_mul]
    apply integral_mono (hQI i) ((hHI i).const_mul u)
    intro X
    dsimp only
    rw [← integral_const_mul]
    apply integral_mono_ae (hFi X i).integrable_sq ((hHi X i).const_mul u)
    filter_upwards [q.bounds] with z hz
    have hq0 := q.lower_pos.le.trans hz.1
    have hr0 : 0 ≤ Real.exp (-U X i z)*q.density z := mul_nonneg (hE0 X i z) hq0
    have hr1 : Real.exp (-U X i z)*q.density z ≤ u := (mul_le_of_le_one_left hq0 (hE1 X i z)).trans hz.2
    have hh := mul_nonneg (mul_nonneg hr0 (sub_nonneg.mpr hr1)) (sq_nonneg (D X i z))
    dsimp [F, H]
    nlinarith

  have bounded (d N : ℕ) (hN : 2 ≤ N) (l u β : ℝ)
      (q : BoundedBackground d l u) (hβ : 0 ≤ β)
      (G : UnitAddTorus (Fin d) → ℝ) (hG : Measurable G) (hGi : Integrable G volume)
      (hGn : ∀ x, 0 ≤ G x) (hGe : ∀ x, G (-x) = G x)
      (hF : ∀ k : Fin d → ℤ, 0 ≤ ∫ x, G x * (UnitAddTorus.mFourier k x).re)
      (f : Configuration d N → ℝ) (hfm : Measurable f) (hfb : ∃ C : ℝ, ∀ X, |f X| ≤ C) :
      let P := CanonicalLaw (N := N) G q.density β
      (Real.exp (-β*u*(∫x,G x)) - 2*u*(β*(∫x,G x)/N + N*MayerDefect volume G (β/N))) *
        (-(∫X,f X*JumpOperator G q.density β f X ∂P)) ≤
        ∫X,(JumpOperator G q.density β f X)^2 ∂P := by
    classical
    haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
      rw [AddCircle.volume_eq_smul_haarAddCircle]; simp; infer_instance
    let m : Measure (UnitAddTorus (Fin d)) := volume
    let P := CanonicalLaw (N := N) G q.density β
    let E := -(∫X,f X*JumpOperator G q.density β f X ∂P)
    have hbal := JumpConditionalBalance d N hN l u β q hβ G hG hGi hGn hGe
    haveI : IsProbabilityMeasure P := hbal.1
    obtain ⟨C,hfC⟩ := hfb
    have hC : 0 ≤ C := (abs_nonneg (f 0)).trans (hfC 0)
    have hu : 0 ≤ u := zero_le_one.trans q.one_le_upper
    let F := fun X i z => Real.exp (-ConditionalPotential G β X i z)*
      (f (Replacement X i z)-f X)*q.density z
    let H := fun X i z => Real.exp (-ConditionalPotential G β X i z)*
      (f (Replacement X i z)-f X)^2*q.density z
    have hrows := rows d N hN l u β q hβ G hG hGi hGn hGe f hfm C hfC
    let a : ℝ := β/N
    have ha : 0 ≤ a := div_nonneg hβ (Nat.cast_nonneg N)
    have hGn' : ∀ᵐ x ∂m, 0 ≤ G x := Eventually.of_forall hGn
    have hmay := MayerConvolutionBounds d G hG hGi hGn' hGe hF
    obtain ⟨T,hT,hUnique⟩ := hmay.2.2.2 a ha
    have hr : 0 ≤ MayerDefect m G a := ((MayerRemainderLimit d G hG hGn' hGi).1 a ha).1
    have hc : 0 ≤ a*(∫x,G x ∂m) := mul_nonneg ha (integral_nonneg hGn)
    have hrect := ReplacementRectangle d N hN l u β q hβ G hG hGi hGn hGe f hfm ⟨C,hfC⟩
    have hCross : ∀ i j : Fin N, i≠j → 0 ≤ ∫ X, ∫ z, ∫ v,
        Real.exp (-a*G (z-v))*F X i z*F X j v ∂m ∂m ∂P := by
      intro i j hij
      convert (hrect.2.2 i j hij).2 using 1
      congr 1; funext X
      congr 1; funext z
      congr 1; funext v
      dsimp [F,a]
      rw [show -ConditionalPotential G β X i z - ConditionalPotential G β X j v - β / ↑N * G (z-v) =
        -β/↑N*G (z-v) + -ConditionalPotential G β X i z + -ConditionalPotential G β X j v by ring,
        Real.exp_add, Real.exp_add]
      ring
    have hInt := integrated_cross P d N G hG hGn a ha T (MayerDefect m G a)
      (a*(∫x,G x ∂m)) hr hc hT.1 hT.2.2.1 (fun g hg => (hT.2.2.2 g hg).2)
      F hrows.1 (2*u*C) (by positivity) hrows.2.1 hCross
    have hE := (hbal.2.2 f hfm ⟨C,hfC⟩).1
    have hQ : (∑i,∫X,∫z,(F X i z)^2 ∂m ∂P) ≤ 2*u*E := by
      have hh := hrows.2.2.2.2
      change E = (1/2:ℝ)*(∑i,∫X,∫z,H X i z ∂m ∂P) at hE
      change (∑i,∫X,∫z,(F X i z)^2 ∂m ∂P) ≤ u*(∑i,∫X,∫z,H X i z ∂m ∂P) at hh
      nlinarith
    have hcost : 0 ≤ N*MayerDefect m G a+a*(∫x,G x ∂m) := add_nonneg (mul_nonneg (Nat.cast_nonneg _) hr) hc
    have hS := hrect.2.1
    change Real.exp (-β*u*(∫x,G x ∂m))*E ≤ ∑i,∫X,(∫z,F X i z ∂m)^2 ∂P at hS
    have hh := mul_le_mul_of_nonneg_left hQ hcost
    change (Real.exp (-β*u*(∫x,G x ∂m))-2*u*(β*(∫x,G x ∂m)/N+N*MayerDefect m G a))*E ≤ _
    have hid : ∫X,(JumpOperator G q.density β f X)^2 ∂P = ∫X,(∑i,∫z,F X i z ∂m)^2 ∂P := rfl
    rw [hid]
    dsimp only [a] at *
    have hal : β/↑N*(∫x,G x ∂m) = β*(∫x,G x ∂m)/N := by ring
    rw [hal] at hInt hh
    nlinarith

  have extension (d N : ℕ) (hN : 2 ≤ N) (l u β : ℝ)
      (q : BoundedBackground d l u) (hβ : 0 ≤ β)
      (G : UnitAddTorus (Fin d) → ℝ) (hG : Measurable G) (hGi : Integrable G volume)
      (hGn : ∀ x, 0 ≤ G x) (hGe : ∀ x, G (-x) = G x)
      (hF : ∀ k : Fin d → ℤ, 0 ≤ ∫ x, G x * (UnitAddTorus.mFourier k x).re)
      (f : Configuration d N → ℝ) (hf : MemLp f 2 (CanonicalLaw (N := N) G q.density β)) :
      let P := CanonicalLaw (N := N) G q.density β
      let E := -(∫X,f X*JumpOperator G q.density β f X ∂P)
      0 ≤ E ∧
      (Real.exp (-β*u*(∫x,G x)) - 2*u*(β*(∫x,G x)/N + N*MayerDefect volume G (β/N))) * E ≤
        ∫X,(JumpOperator G q.density β f X)^2 ∂P := by
    classical
    let P := CanonicalLaw (N := N) G q.density β
    let A := Real.exp (-β*u*(∫x,G x)) - 2*u*(β*(∫x,G x)/N + N*MayerDefect volume G (β/N))
    obtain ⟨L,hL,hUni⟩ := JumpL2Extension d N hN l u β q hβ G hG hGi hGn hGe
    have hinner (g : Configuration d N → ℝ) (hg : MemLp g 2 P) :
        inner ℝ (hg.toLp g) (L (hg.toLp g)) = ∫X,g X*JumpOperator G q.density β g X ∂P := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hg.coeFn_toLp, (hL.2.2.2 g hg).2.1] with X hx hLX
      simp [hx,hLX,RCLike.inner_apply,mul_comm]
    have hnorm (g : Configuration d N → ℝ) (hg : MemLp g 2 P) :
        ‖L (hg.toLp g)‖^2 = ∫X,(JumpOperator G q.density β g X)^2 ∂P := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(hL.2.2.2 g hg).2.1] with X hx
      simp [hx,pow_two]
    have hbound : ∀ v : Lp ℝ 2 P, A*(-inner ℝ v (L v)) ≤ ‖L v‖^2 := by
      intro v
      refine (Lp.simpleFunc.denseRange (E := ℝ) (μ := P) (by simp : (2 : ENNReal) ≠ ⊤)).induction_on v ?_ ?_
      · apply isClosed_le <;> fun_prop
      · intro s
        let g := Lp.simpleFunc.toSimpleFunc s
        have hg : MemLp g 2 P := Lp.simpleFunc.memLp s
        have he : hg.toLp g = s.val := by
          apply Lp.ext
          exact hg.coeFn_toLp.trans (Lp.simpleFunc.toSimpleFunc_eq_toFun s)
        have hb : ∃ C : ℝ, ∀ X, |g X| ≤ C := by
          obtain ⟨C,hC⟩ := (g.finite_range.image abs).bddAbove
          exact ⟨C,fun X => hC ⟨g X,mem_range_self X,rfl⟩⟩
        have hh := bounded d N hN l u β q hβ G hG hGi hGn hGe hF g g.measurable hb
        change A*(-(∫X,g X*JumpOperator G q.density β g X ∂P)) ≤ ∫X,(JumpOperator G q.density β g X)^2 ∂P at hh
        rw [← hinner g hg, ← hnorm g hg, he] at hh
        exact hh
    have hpos : 0 ≤ -inner ℝ (hf.toLp f) (L (hf.toLp f)) := (hL.2.2.2 f hf).2.2.2.2.2.1
    rw [hinner f hf] at hpos
    refine ⟨hpos, ?_⟩
    have hh := hbound (hf.toLp f)
    rw [hinner f hf, hnorm f hf] at hh
    exact hh
  classical
  let m : Measure (UnitAddTorus (Fin d)) := volume
  let P := CanonicalLaw (N := N) G q.density β
  let c := ∫ x, G x ∂m
  let η := fun a : ℝ => MayerDefect m G a / a
  let E := -(∫X, f X*JumpOperator G q.density β f X ∂P)
  have hc : 0 ≤ c := integral_nonneg hGn
  have hu : 0 ≤ u := zero_le_one.trans q.one_le_upper
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNa : (N : ℝ) ≠ 0 := ne_of_gt hNp
  have ha : 0 ≤ β/(N : ℝ) := div_nonneg hβ hNp.le
  have hb : 0 ≤ B/(N : ℝ) := div_nonneg hB hNp.le
  have hab : β/(N : ℝ) ≤ B/(N : ℝ) := div_le_div_of_nonneg_right hβB hNp.le
  have hm := MayerConvolutionBounds d G hG hGi (Eventually.of_forall hGn) hGe hF
  have hmon : η (β/N) ≤ η (B/N) := hm.2.1 ha hb hab
  have hη : 0 ≤ η (B/N) := div_nonneg (((MayerRemainderLimit d G hG (Eventually.of_forall hGn) hGi).1 (B/N) hb).1) hb
  have hid : N*MayerDefect m G (β/N) = β*η (β/N) := by
    by_cases hβ0 : β = 0
    · simp [hβ0,η,MayerDefect]
    · dsimp [η]
      field_simp
  have hrem : N*MayerDefect m G (β/N) ≤ B*η (B/N) := by
    rw [hid]
    exact (mul_le_mul_of_nonneg_left hmon hβ).trans (mul_le_mul_of_nonneg_right hβB hη)
  have hlin : β*c/N ≤ B*c/N := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hβB hc) hNp.le
  have hex : Real.exp (-B*u*c) ≤ Real.exp (-β*u*c) := Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hu hc])
  have hcoef : Real.exp (-B*u*c)-2*u*(B*c/N+B*η (B/N)) ≤
      Real.exp (-β*u*c)-2*u*(β*c/N+N*MayerDefect m G (β/N)) := by
    have hh := mul_le_mul_of_nonneg_left (add_le_add hlin hrem) (show 0 ≤ 2*u by positivity)
    linarith
  have hext := extension d N hN l u β q hβ G hG hGi hGn hGe hF f hf
  change 0 ≤ E ∧ _ at hext
  change (Real.exp (-B*u*c)-2*u*(B*c/N+B*η (B/N)))*E ≤ _
  exact (mul_le_mul_of_nonneg_right hcoef hext.1).trans hext.2

