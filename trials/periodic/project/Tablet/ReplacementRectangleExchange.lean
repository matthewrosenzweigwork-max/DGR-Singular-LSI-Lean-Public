module

public import Tablet.ReplacementJointBalance

@[expose] public section
-- [TABLET NODE: ReplacementRectangleExchange]
theorem ReplacementRectangleExchange (d N : ℕ) (hN : 2 ≤ N) (l u β : ℝ)
    (q : BoundedBackground d l u) (hβ : 0 ≤ β)
    (G : UnitAddTorus (Fin d) → ℝ) (hG : Measurable G)
    (hGi : MeasureTheory.Integrable G MeasureTheory.volume)
    (hGn : ∀ x, 0 ≤ G x) (hGe : ∀ x, G (-x) = G x)
    (i j : Fin N) (hij : i ≠ j)
    (H : (Configuration d N × UnitAddTorus (Fin d)) × UnitAddTorus (Fin d) → ℝ)
    (hH : Measurable H) (hb : ∃ C : ℝ, ∀ v, |H v| ≤ C) :
    let P := CanonicalLaw (N := N) G q.density β
    let R := fun X z v => Real.exp (-ConditionalPotential G β X i z -
      ConditionalPotential G β X j v - (β / N) * G (z-v)) * q.density z * q.density v
    MeasureTheory.Integrable (fun w : (Configuration d N × UnitAddTorus (Fin d)) × UnitAddTorus (Fin d) =>
      R w.1.1 w.1.2 w.2 * H w) ((P.prod MeasureTheory.volume).prod MeasureTheory.volume) ∧
    MeasureTheory.Integrable (fun X => ∫ z, ∫ v, R X z v * H ((X,z),v)) P ∧
    (∫ X, (∫ z, ∫ v, R X z v * H ((X,z),v)) ∂P) =
      (∫ X, (∫ z, ∫ v, R X z v * H ((Replacement X i z, X i),v)) ∂P) ∧
    (∫ X, (∫ z, ∫ v, R X z v * H ((X,z),v)) ∂P) =
      ∫ X, (∫ z, ∫ v, R X z v * H ((Replacement X j v,z),X j)) ∂P := by
-- BODY
  classical
  have joint_test_exchange (d N : ℕ) (hN : 2 ≤ N) (l u β : ℝ)
      (q : BoundedBackground d l u) (hβ : 0 ≤ β)
      (G : UnitAddTorus (Fin d) → ℝ) (hG : Measurable G)
      (hGi : MeasureTheory.Integrable G MeasureTheory.volume)
      (hGn : ∀ x, 0 ≤ G x) (hGe : ∀ x, G (-x) = G x) (i : Fin N)
      (H : Configuration d N × UnitAddTorus (Fin d) → ℝ) (hH : Measurable H)
      (hb : ∃ C : ℝ, ∀ v, |H v| ≤ C) :
      let P := CanonicalLaw (N := N) G q.density β
      MeasureTheory.Integrable (fun X => ∫ z,
        Real.exp (-ConditionalPotential G β X i z) * q.density z * H (X,z)) P ∧
      (∫ X, (∫ z, Real.exp (-ConditionalPotential G β X i z) * q.density z * H (X,z)) ∂P) =
        ∫ X, (∫ z, Real.exp (-ConditionalPotential G β X i z) * q.density z *
          H (Replacement X i z, X i)) ∂P := by
    classical
    haveI : MeasureTheory.IsProbabilityMeasure (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) := by
      rw [AddCircle.volume_eq_smul_haarAddCircle]
      simp
      infer_instance
    let T := UnitAddTorus (Fin d)
    let m : MeasureTheory.Measure T := MeasureTheory.volume
    let P := CanonicalLaw (N := N) G q.density β
    let μ := P.prod m
    let r : Configuration d N × T → ℝ := fun v => Real.exp (-ConditionalPotential G β v.1 i v.2) * q.density v.2
    let S : Configuration d N × T → Configuration d N × T := fun v => (Replacement v.1 i v.2, v.1 i)
    let J := μ.withDensity (fun v => ENNReal.ofReal (r v))
    have hgb := GibbsNormalizerBounds d N hN l u q G hG hGi 0 β (le_refl 0) hβ (Filter.Eventually.of_forall fun x => by simpa using hGn x)
    haveI : MeasureTheory.IsProbabilityMeasure P := hgb.2.2.2
    have hUm : Measurable (fun v : Configuration d N × T => ConditionalPotential G β v.1 i v.2) := by
      unfold ConditionalPotential
      refine measurable_const.mul (Finset.measurable_fun_sum _ fun j _ => ?_)
      split_ifs
      · exact measurable_const
      · exact hG.comp (measurable_snd.sub ((measurable_pi_apply j).comp measurable_fst))
    have hrm : Measurable r := (hUm.neg.exp).mul (q.measurable.comp measurable_snd)
    have hUn (X : Configuration d N) (z : T) : 0 ≤ ConditionalPotential G β X i z := by
      unfold ConditionalPotential
      exact mul_nonneg (div_nonneg hβ (Nat.cast_nonneg N)) (Finset.sum_nonneg fun j _ => by split_ifs; exact le_rfl; exact hGn _)
    have hre (v : Configuration d N × T) : 0 ≤ Real.exp (-ConditionalPotential G β v.1 i v.2) ∧ Real.exp (-ConditionalPotential G β v.1 i v.2) ≤ 1 :=
      ⟨(Real.exp_pos _).le, (Real.exp_le_one_iff).mpr (neg_nonpos.mpr (hUn _ _))⟩
    have hqb : ∀ᵐ v ∂μ, l ≤ q.density v.2 ∧ q.density v.2 ≤ u :=
      (MeasureTheory.measurePreserving_snd (μ := P) (ν := m)).quasiMeasurePreserving.tendsto_ae q.bounds
    have hrn : ∀ᵐ v ∂μ, 0 ≤ r v := hqb.mono fun v hv => mul_nonneg (hre v).1 (q.lower_pos.le.trans hv.1)
    have hS := (ReplacementJointBalance d N hN l u β q hβ G hG hGi hGn hGe i).1
    have hSJ : MeasureTheory.MeasurePreserving S J J := hS
    have hSS : Function.LeftInverse S S := by
      intro v
      dsimp only [S]
      simp only [Replacement, Function.update_self, Function.update_idem, Function.update_eq_self]
    let e : (Configuration d N × T) ≃ᵐ (Configuration d N × T) :=
      { toEquiv := { toFun := S, invFun := S, left_inv := hSS, right_inv := hSS }
        measurable_toFun := hSJ.measurable
        measurable_invFun := hSJ.measurable }
    have hSemb : MeasurableEmbedding S := e.measurableEmbedding
    obtain ⟨D, hD⟩ := hb
    have hD0 : 0 ≤ D := (abs_nonneg (H (0,0))).trans (hD (0,0))
    have raw_int : ∀ K : Configuration d N × T → ℝ, Measurable K →
        (∀ v, |K v| ≤ D) → MeasureTheory.Integrable (fun v => r v * K v) μ := by
      intro K hK hKD
      apply MeasureTheory.Integrable.of_bound (hrm.mul hK).aestronglyMeasurable (u*D)
      filter_upwards [hqb] with v hv
      have hq0 := q.lower_pos.le.trans hv.1
      have hr0 : 0 ≤ r v := mul_nonneg (hre v).1 hq0
      have hru : r v ≤ u := (mul_le_of_le_one_left hq0 (hre v).2).trans hv.2
      change |r v * K v| ≤ u * D
      simp only [abs_mul, abs_of_nonneg hr0]
      exact mul_le_mul hru (hKD v) (abs_nonneg _) (zero_le_one.trans q.one_le_upper)
    have hraw := raw_int H hH hD
    have hrawS := raw_int (H ∘ S) (hH.comp hSJ.measurable) (fun v => hD (S v))
    have hconvert : ∀ K : Configuration d N × T → ℝ,
        (∫ v, K v ∂J) = ∫ v, r v * K v ∂μ := by
      intro K
      change (∫ v, K v ∂μ.withDensity (fun v => ENNReal.ofReal (r v))) = _
      rw [integral_withDensity_eq_integral_toReal_smul hrm.ennreal_ofReal
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hrn] with v hv
      simp only [ENNReal.toReal_ofReal hv, smul_eq_mul]
    refine ⟨hraw.integral_prod_left, ?_⟩
    change (∫ X, ∫ z, r (X,z) * H (X,z) ∂m ∂P) =
      ∫ X, ∫ z, r (X,z) * (H ∘ S) (X,z) ∂m ∂P
    calc
      _ = ∫ v, r v * H v ∂μ := MeasureTheory.integral_integral hraw
      _ = ∫ v, H v ∂J := (hconvert H).symm
      _ = ∫ v, H (S v) ∂J := (hSJ.integral_comp hSemb H).symm
      _ = ∫ v, r v * (H ∘ S) v ∂μ := hconvert (H ∘ S)
      _ = _ := (MeasureTheory.integral_integral (f := fun X z => r (X,z) * (H ∘ S) (X,z)) hrawS).symm

  haveI : MeasureTheory.IsProbabilityMeasure (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
    infer_instance
  let T := UnitAddTorus (Fin d)
  let m : MeasureTheory.Measure T := MeasureTheory.volume
  haveI : MeasureTheory.IsProbabilityMeasure m := by dsimp [m,T]; infer_instance
  let P := CanonicalLaw (N := N) G q.density β
  haveI : MeasureTheory.IsProbabilityMeasure P := (GibbsNormalizerBounds d N hN l u q G hG hGi 0 β (le_refl 0) hβ (Filter.Eventually.of_forall fun x => by simpa using hGn x)).2.2.2
  let μ := (P.prod m).prod m
  let a : ℝ := β / N
  let U := ConditionalPotential (N := N) G β
  let R : (Configuration d N × T) × T → ℝ := fun w =>
    Real.exp (-U w.1.1 i w.1.2 - U w.1.1 j w.2 - a * G (w.1.2-w.2)) * q.density w.1.2 * q.density w.2
  let S : (Configuration d N × T) × T → (Configuration d N × T) × T := fun w => ((Replacement w.1.1 i w.1.2,w.1.1 i),w.2)
  have hSm : Measurable S := ((ReplacementHaarSwap d N i).1.measurable.comp measurable_fst).prodMk measurable_snd
  have hUm (k : Fin N) : Measurable (fun w : Configuration d N × T => U w.1 k w.2) := by
    unfold U ConditionalPotential
    refine measurable_const.mul (Finset.measurable_fun_sum _ fun h _ => ?_)
    split_ifs
    · exact measurable_const
    · exact hG.comp (measurable_snd.sub ((measurable_pi_apply h).comp measurable_fst))
  have hUn (X : Configuration d N) (k : Fin N) (z : T) : 0 ≤ U X k z := by
    unfold U ConditionalPotential
    exact mul_nonneg (div_nonneg hβ (Nat.cast_nonneg N)) (Finset.sum_nonneg fun h _ => by split_ifs; exact le_rfl; exact hGn _)
  have ha : 0 ≤ a := div_nonneg hβ (Nat.cast_nonneg N)
  have hRm : Measurable R := by
    have hiu : Measurable (fun w : (Configuration d N × T) × T => U w.1.1 i w.1.2) := (hUm i).comp measurable_fst
    have hju : Measurable (fun w : (Configuration d N × T) × T => U w.1.1 j w.2) := (hUm j).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    exact (((hiu.neg.sub hju).sub ((hG.comp ((measurable_snd.comp measurable_fst).sub measurable_snd)).const_mul a)).exp.mul (q.measurable.comp (measurable_snd.comp measurable_fst))).mul (q.measurable.comp measurable_snd)
  have hqz : ∀ᵐ w ∂μ, l ≤ q.density w.1.2 ∧ q.density w.1.2 ≤ u :=
    ((MeasureTheory.measurePreserving_snd (μ := P) (ν := m)).comp (MeasureTheory.measurePreserving_fst (μ := P.prod m) (ν := m))).quasiMeasurePreserving.tendsto_ae q.bounds
  have hqv : ∀ᵐ w ∂μ, l ≤ q.density w.2 ∧ q.density w.2 ≤ u :=
    (MeasureTheory.measurePreserving_snd (μ := P.prod m) (ν := m)).quasiMeasurePreserving.tendsto_ae q.bounds
  obtain ⟨D,hD⟩ := hb
  have hD0 : 0 ≤ D := (abs_nonneg (H ((0,0),0))).trans (hD ((0,0),0))
  have hraw : ∀ K : (Configuration d N × T) × T → ℝ, Measurable K →
      (∀ w, |K w| ≤ D) → MeasureTheory.Integrable (fun w => R w * K w) μ := by
    intro K hK hKD
    apply MeasureTheory.Integrable.of_bound (hRm.mul hK).aestronglyMeasurable (u^2*D)
    filter_upwards [hqz,hqv] with w hz hv
    have hz0 := q.lower_pos.le.trans hz.1
    have hv0 := q.lower_pos.le.trans hv.1
    have hE0 : 0 ≤ Real.exp (-U w.1.1 i w.1.2 - U w.1.1 j w.2 - a * G (w.1.2-w.2)) := (Real.exp_pos _).le
    have hE1 : Real.exp (-U w.1.1 i w.1.2 - U w.1.1 j w.2 - a * G (w.1.2-w.2)) ≤ 1 := Real.exp_le_one_iff.mpr (by have hh := mul_nonneg ha (hGn (w.1.2-w.2)); linarith [hUn w.1.1 i w.1.2, hUn w.1.1 j w.2])
    have hR0 : 0 ≤ R w := mul_nonneg (mul_nonneg hE0 hz0) hv0
    have hRb : R w ≤ u^2 := by
      calc
        _ ≤ q.density w.1.2 * q.density w.2 := by
          exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hz0 hE1) hv0
        _ ≤ u*u := mul_le_mul hz.2 hv.2 hv0 (zero_le_one.trans q.one_le_upper)
        _ = _ := by ring
    change |R w*K w| ≤ u^2*D
    rw [abs_mul, abs_of_nonneg hR0]
    exact mul_le_mul hRb (hKD w) (abs_nonneg _) (sq_nonneg u)
  have hiH := hraw H hH hD
  have hiHS := hraw (H ∘ S) (hH.comp hSm) (fun w => hD (S w))
  have hcyclic : ∀ F : (Configuration d N × T) × T → ℝ, MeasureTheory.Integrable F μ →
      (∫ X, ∫ z, ∫ v, F ((X,z),v) ∂m ∂m ∂P) = ∫ v, ∫ X, ∫ z, F ((X,z),v) ∂m ∂P ∂m := by
    intro F hFi
    calc
      _ = ∫ w, ∫ v, F (w,v) ∂m ∂P.prod m := MeasureTheory.integral_integral hFi.integral_prod_left
      _ = ∫ v, ∫ w, F (w,v) ∂P.prod m ∂m := MeasureTheory.integral_integral_swap hFi
      _ = _ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [hFi.prod_left_ae] with v hv
        exact MeasureTheory.integral_prod _ hv
  have hcross (i j : Fin N) (hij : i ≠ j) (X : Configuration d N) (z v : T) :
      U (Replacement X i z) j v + a * G (v-X i) = U X j v + a * G (v-z) := by
    let b : Fin N → ℝ := fun k => if k=j then 0 else G (v-X k)
    let c : Fin N → ℝ := fun k => if k=j then 0 else G (v-Replacement X i z k)
    have hb : b i = G (v-X i) := by simp only [b,hij,↓reduceIte]
    have hc : c i = G (v-z) := by simp only [c,hij,↓reduceIte,Replacement,Function.update_self]
    have he : ∑ k ∈ (Finset.univ : Finset (Fin N)).erase i, c k = ∑ k ∈ (Finset.univ : Finset (Fin N)).erase i, b k := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [b,c,Replacement,Function.update_of_ne (Finset.ne_of_mem_erase hk)]
    have hbs := Finset.sum_erase_add (Finset.univ : Finset (Fin N)) b (Finset.mem_univ i)
    have hcs := Finset.sum_erase_add (Finset.univ : Finset (Fin N)) c (Finset.mem_univ i)
    rw [hb] at hbs
    rw [hc,he] at hcs
    unfold U ConditionalPotential
    change a * (∑ k, c k) + a * G (v-X i) = a * (∑ k,b k) + a * G (v-z)
    rw [← hbs,← hcs]
    ring
  have heven (z v : T) : G (z-v) = G (v-z) := by rw [← hGe (z-v), neg_sub]
  have hsuffix (X : Configuration d N) (z v : T) :
      -U (Replacement X i z) j v - a * G (X i-v) = -U X j v - a * G (z-v) := by
    have hh := hcross i j hij X z v
    rw [heven (X i) v,heven z v]
    linarith
  have hfixed : ∀ v : T,
      (∫ X, ∫ z, R ((X,z),v) * H ((X,z),v) ∂m ∂P) =
        ∫ X, ∫ z, R ((X,z),v) * (H ∘ S) ((X,z),v) ∂m ∂P := by
    intro v
    let K : Configuration d N × T → ℝ := fun w =>
      Real.exp (-U w.1 j v - a * G (w.2-v)) * q.density v * H (w,v)
    have hKm : Measurable K := by
      have hu : Measurable (fun w : Configuration d N × T => U w.1 j v) := (hUm j).comp (measurable_fst.prodMk (measurable_const (a := v)))
      exact ((hu.neg.sub ((hG.comp (measurable_snd.sub_const v)).const_mul a)).exp.mul_const (q.density v)).mul (hH.comp (measurable_id.prodMk (measurable_const (a := v))))
    have hKb : ∀ w, |K w| ≤ |q.density v| * D := by
      intro w
      have hex0 : 0 ≤ Real.exp (-U w.1 j v - a * G (w.2-v)) := (Real.exp_pos _).le
      have hex1 : Real.exp (-U w.1 j v - a * G (w.2-v)) ≤ 1 := Real.exp_le_one_iff.mpr (by have hh := mul_nonneg ha (hGn (w.2-v)); linarith [hUn w.1 j v])
      dsimp only [K]
      rw [abs_mul,abs_mul,abs_of_nonneg hex0]
      exact mul_le_mul (mul_le_of_le_one_left (abs_nonneg _) hex1) (hD (w,v)) (abs_nonneg _) (abs_nonneg _)
    have hx := (joint_test_exchange d N hN l u β q hβ G hG hGi hGn hGe i K hKm ⟨_,hKb⟩).2
    have hr0 (X : Configuration d N) (z : T) :
        Real.exp (-U X i z) * q.density z * K (X,z) = R ((X,z),v) * H ((X,z),v) := by
      dsimp only [K,R]
      simp only [sub_eq_add_neg, Real.exp_add]
      ring
    have hr1 (X : Configuration d N) (z : T) :
        Real.exp (-U X i z) * q.density z * K (Replacement X i z,X i) = R ((X,z),v) * (H ∘ S) ((X,z),v) := by
      dsimp only [K]
      rw [hsuffix]
      change Real.exp (-U X i z) * q.density z * (Real.exp (-U X j v-a*G (z-v))*q.density v*H ((Replacement X i z,X i),v)) = _
      change _ = R ((X,z),v) * H ((Replacement X i z,X i),v)
      dsimp only [R]
      simp only [sub_eq_add_neg, Real.exp_add]
      ring
    change (∫ X, ∫ z, Real.exp (-U X i z) * q.density z * K (X,z) ∂m ∂P) =
      ∫ X, ∫ z, Real.exp (-U X i z) * q.density z * K (Replacement X i z,X i) ∂m ∂P at hx
    simp_rw [hr0,hr1] at hx
    exact hx
  let Sj : (Configuration d N × T) × T → (Configuration d N × T) × T :=
    fun w => ((Replacement w.1.1 j w.2,w.1.2),w.1.1 j)
  have hRepj : Measurable (fun w : (Configuration d N × T) × T => Replacement w.1.1 j w.2) :=
    measurable_fst.comp ((ReplacementHaarSwap d N j).1.measurable.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have hSjm : Measurable Sj := (hRepj.prodMk (measurable_snd.comp measurable_fst)).prodMk ((measurable_pi_apply j).comp (measurable_fst.comp measurable_fst))
  have hiHSj := hraw (H ∘ Sj) (hH.comp hSjm) (fun w => hD (Sj w))
  have hsuffixj (X : Configuration d N) (z v : T) :
      -U (Replacement X j v) i z - a * G (z-X j) = -U X i z - a * G (z-v) := by
    have hh := hcross j i hij.symm X v z
    linarith
  have hfixedj : ∀ z : T,
      (∫ X, ∫ v, R ((X,z),v) * H ((X,z),v) ∂m ∂P) =
        ∫ X, ∫ v, R ((X,z),v) * (H ∘ Sj) ((X,z),v) ∂m ∂P := by
    intro z
    let K : Configuration d N × T → ℝ := fun w =>
      Real.exp (-U w.1 i z - a * G (z-w.2)) * q.density z * H ((w.1,z),w.2)
    have hKm : Measurable K := by
      have hu : Measurable (fun w : Configuration d N × T => U w.1 i z) := (hUm i).comp (measurable_fst.prodMk (measurable_const (a := z)))
      exact ((hu.neg.sub ((hG.comp (measurable_const.sub measurable_snd)).const_mul a)).exp.mul_const (q.density z)).mul (hH.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd))
    have hKb : ∀ w, |K w| ≤ |q.density z| * D := by
      intro w
      have hex0 : 0 ≤ Real.exp (-U w.1 i z - a * G (z-w.2)) := (Real.exp_pos _).le
      have hex1 : Real.exp (-U w.1 i z - a * G (z-w.2)) ≤ 1 := Real.exp_le_one_iff.mpr (by have hh := mul_nonneg ha (hGn (z-w.2)); linarith [hUn w.1 i z])
      dsimp only [K]
      rw [abs_mul,abs_mul,abs_of_nonneg hex0]
      exact mul_le_mul (mul_le_of_le_one_left (abs_nonneg _) hex1) (hD ((w.1,z),w.2)) (abs_nonneg _) (abs_nonneg _)
    have hx := (joint_test_exchange d N hN l u β q hβ G hG hGi hGn hGe j K hKm ⟨_,hKb⟩).2
    have hr0 (X : Configuration d N) (v : T) :
        Real.exp (-U X j v) * q.density v * K (X,v) = R ((X,z),v) * H ((X,z),v) := by
      dsimp only [K,R]
      simp only [sub_eq_add_neg, Real.exp_add]
      ring
    have hr1 (X : Configuration d N) (v : T) :
        Real.exp (-U X j v) * q.density v * K (Replacement X j v,X j) = R ((X,z),v) * (H ∘ Sj) ((X,z),v) := by
      dsimp only [K]
      rw [hsuffixj]
      change _ = R ((X,z),v) * H ((Replacement X j v,z),X j)
      dsimp only [R]
      simp only [sub_eq_add_neg, Real.exp_add]
      ring
    change (∫ X, ∫ v, Real.exp (-U X j v) * q.density v * K (X,v) ∂m ∂P) =
      ∫ X, ∫ v, Real.exp (-U X j v) * q.density v * K (Replacement X j v,X j) ∂m ∂P at hx
    simp_rw [hr0,hr1] at hx
    exact hx
  have hswitch : ∀ F : (Configuration d N × T) × T → ℝ, MeasureTheory.Integrable F μ →
      (∫ X, ∫ z, ∫ v, F ((X,z),v) ∂m ∂m ∂P) = ∫ z, ∫ X, ∫ v, F ((X,z),v) ∂m ∂P ∂m := by
    intro F hFi
    exact MeasureTheory.integral_integral_swap hFi.integral_prod_left
  refine ⟨hiH, hiH.integral_prod_left.integral_prod_left, ?_, ?_⟩
  · change (∫ X, ∫ z, ∫ v, R ((X,z),v) * H ((X,z),v) ∂m ∂m ∂P) =
      ∫ X, ∫ z, ∫ v, R ((X,z),v) * (H ∘ S) ((X,z),v) ∂m ∂m ∂P
    calc
      _ = ∫ v, ∫ X, ∫ z, R ((X,z),v) * H ((X,z),v) ∂m ∂P ∂m := hcyclic _ hiH
      _ = ∫ v, ∫ X, ∫ z, R ((X,z),v) * (H ∘ S) ((X,z),v) ∂m ∂P ∂m := by
        congr 1
        funext v
        exact hfixed v
      _ = _ := (hcyclic _ hiHS).symm
  · change (∫ X, ∫ z, ∫ v, R ((X,z),v) * H ((X,z),v) ∂m ∂m ∂P) =
      ∫ X, ∫ z, ∫ v, R ((X,z),v) * (H ∘ Sj) ((X,z),v) ∂m ∂m ∂P
    calc
      _ = ∫ z, ∫ X, ∫ v, R ((X,z),v) * H ((X,z),v) ∂m ∂P ∂m := hswitch _ hiH
      _ = ∫ z, ∫ X, ∫ v, R ((X,z),v) * (H ∘ Sj) ((X,z),v) ∂m ∂P ∂m := by
        congr 1
        funext z
        exact hfixedj z
      _ = _ := (hswitch _ hiHSj).symm
