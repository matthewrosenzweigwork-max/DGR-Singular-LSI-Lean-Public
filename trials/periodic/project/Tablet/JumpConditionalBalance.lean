import Tablet.JumpOperator
import Tablet.PairAlgebra
import Tablet.GibbsNormalizerBounds
import Tablet.CanonicalLaw
import Tablet.VarianceVariational
import Tablet.JumpL2Construction
import Tablet.ReplacementJointBalance
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Probability.Moments.Variance
open MeasureTheory ProbabilityTheory
set_option maxHeartbeats 6000000 in
-- [TABLET NODE: JumpConditionalBalance]
theorem JumpConditionalBalance (d N : ℕ) (hN : 2 ≤ N) (l u β : ℝ)
    (q : BoundedBackground d l u) (hβ : 0 ≤ β)
    (G : UnitAddTorus (Fin d) → ℝ) (hG : Measurable G)
    (hGi : MeasureTheory.Integrable G MeasureTheory.volume)
    (hGn : ∀ x, 0 ≤ G x) (hGe : ∀ x, G (-x) = G x) :
    let P := CanonicalLaw (N := N) G q.density β
    let Z := fun (X : Configuration d N) (i : Fin N) =>
      ∫ z, Real.exp (-ConditionalPotential G β X i z) * q.density z
    let ν := fun (X : Configuration d N) (i : Fin N) =>
      NormalizedTilt MeasureTheory.volume
        (fun z => q.density z * Real.exp (-ConditionalPotential G β X i z))
    MeasureTheory.IsProbabilityMeasure P ∧
    (∀ X i, Real.exp (-β * u * (∫ z, G z)) ≤ Z X i ∧ Z X i ≤ 1 ∧
      MeasureTheory.IsProbabilityMeasure (ν X i)) ∧
    ∀ f : Configuration d N → ℝ, Measurable f →
      (∃ C : ℝ, ∀ X, |f X| ≤ C) →
      let E := -(∫ X, f X * JumpOperator G q.density β f X ∂P)
      E = (1 / 2 : ℝ) * ∑ i : Fin N,
        ∫ X, (∫ z, Real.exp (-ConditionalPotential G β X i z) *
          (f (Replacement X i z) - f X)^2 * q.density z) ∂P ∧
      E = ∑ i : Fin N, ∫ X, Z X i *
        ProbabilityTheory.variance (fun z => f (Replacement X i z)) (ν X i) ∂P ∧
      E ≤ 2 * (N : ℝ) * (∫ X, f X^2 ∂P) ∧
      (∫ X, (JumpOperator G q.density β f X)^2 ∂P) ≤
        4 * (N : ℝ)^2 * (∫ X, f X^2 ∂P) ∧
      (E = 0 ↔ ∃ c : ℝ, ∀ᵐ X ∂P, f X = c) ∧
      (∀ h : Configuration d N → ℝ, Measurable h →
        (∃ C : ℝ, ∀ X, |h X| ≤ C) →
        (∫ X, f X * JumpOperator G q.density β h X ∂P) =
        (∫ X, h X * JumpOperator G q.density β f X ∂P)) := by
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

  have conditionalNormalizer_bounds (d N : ℕ) (hN : 2 ≤ N) (l u β : ℝ)
      (q : BoundedBackground d l u) (hβ : 0 ≤ β)
      (G : UnitAddTorus (Fin d) → ℝ) (hG : Measurable G)
      (hGi : Integrable G volume) (hGn : ∀ x, 0 ≤ G x)
      (X : Configuration d N) (i : Fin N) :
      let U := ConditionalPotential G β X i
      let Z := ∫ z, Real.exp (-U z) * q.density z
      Measurable U ∧ Integrable U volume ∧ (∀ z, 0 ≤ U z) ∧
        Integrable (fun z => U z * q.density z) volume ∧
        Integrable (fun z => Real.exp (-U z) * q.density z) volume ∧
        Real.exp (-β*u*(∫ z,G z)) ≤ Z ∧ Z ≤ 1 ∧
        IsProbabilityMeasure (NormalizedTilt volume (fun z => q.density z * Real.exp (-U z))) := by
    classical
    dsimp only
    let U := ConditionalPotential G β X i
    have hnpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
    have hnne : (N : ℝ) ≠ 0 := ne_of_gt hnpos
    have hcoef : 0 ≤ β/(N : ℝ) := div_nonneg hβ hnpos.le
    have hUmeas : Measurable U := by
      dsimp [U,ConditionalPotential]
      apply Measurable.const_mul
      apply Finset.measurable_fun_sum
      intro j hj
      by_cases h : j = i
      · simp only [h,↓reduceIte]
        exact measurable_const
      · simp only [h,↓reduceIte]
        exact hG.comp (measurable_id.sub measurable_const)
    have hterm (j : Fin N) : Integrable
        (fun z => if j = i then (0 : ℝ) else G (z-X j)) volume := by
      by_cases h : j = i
      · simpa only [h,↓reduceIte] using (integrable_const (0 : ℝ) :
          Integrable (fun _ : UnitAddTorus (Fin d) => (0 : ℝ)) volume)
      · simp only [h,↓reduceIte]
        exact (measurePreserving_sub_right volume (X j)).integrable_comp
          hG.aestronglyMeasurable |>.mpr hGi
    have hUint : Integrable U volume :=
      (integrable_finsetSum _ (fun j _ => hterm j)).const_mul _
    have hUpos (z : UnitAddTorus (Fin d)) : 0 ≤ U z := by
      apply mul_nonneg hcoef
      apply Finset.sum_nonneg
      intro j hj
      split_ifs
      · exact le_rfl
      · exact hGn _
    have hUmean : (∫ z,U z) = β/(N : ℝ) * ((N : ℝ)-1) * (∫ z,G z) := by
      dsimp [U,ConditionalPotential]
      rw [integral_const_mul,integral_finsetSum _ (fun j _ => hterm j)]
      have he (j : Fin N) : (∫ z, if j = i then (0 : ℝ) else G (z-X j)) =
          (∫ z,G z) - (if j = i then (∫ z,G z) else 0) := by
        by_cases h : j = i
        · simp [h]
        · simpa [h] using integral_sub_right_eq_self G (X j)
      simp_rw [he]
      simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
        nsmul_eq_mul,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
      ring
    have hqint : Integrable q.density volume := integrable_of_integral_eq_one q.mass
    have hqpos : ∀ᵐ z ∂volume, 0 ≤ q.density z :=
      q.bounds.mono (fun z h => q.lower_pos.le.trans h.1)
    have hqnorm : ∀ᵐ z ∂volume, ‖q.density z‖ ≤ u := by
      filter_upwards [q.bounds,hqpos] with z h hp
      simpa only [Real.norm_eq_abs,abs_of_nonneg hp] using h.2
    have hUqint : Integrable (fun z => U z*q.density z) volume :=
      hUint.mul_bdd q.measurable.aestronglyMeasurable hqnorm
    have hUqbound : (∫ z,U z*q.density z) ≤ β*u*(∫ z,G z) := by
      have h := integral_mono_ae hUqint (hUint.const_mul u) (q.bounds.mono
        (fun z h => by simpa only [mul_comm] using
          mul_le_mul_of_nonneg_left h.2 (hUpos z)))
      rw [integral_const_mul,hUmean] at h
      have hfract : β/(N : ℝ)*((N : ℝ)-1) ≤ β := by
        calc
          _ ≤ β/(N : ℝ)*(N : ℝ) := mul_le_mul_of_nonneg_left
            (sub_le_self _ zero_le_one) hcoef
          _ = β := div_mul_cancel₀ _ hnne
      have hgc : 0 ≤ ∫ z,G z := integral_nonneg hGn
      have hu : 0 ≤ u := zero_le_one.trans q.one_le_upper
      have hm := mul_le_mul_of_nonneg_right hfract (mul_nonneg hu hgc)
      nlinarith
    have hWmeas : Measurable (fun z => Real.exp (-U z)*q.density z) :=
      hUmeas.neg.exp.mul q.measurable
    have hWpos : ∀ᵐ z ∂volume, 0 ≤ Real.exp (-U z)*q.density z :=
      hqpos.mono (fun z h => mul_nonneg (Real.exp_nonneg _) h)
    have hWbound : ∀ᵐ z ∂volume, Real.exp (-U z)*q.density z ≤ q.density z := by
      filter_upwards [hqpos] with z h
      have he : Real.exp (-U z) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hUpos z))
      simpa only [one_mul] using mul_le_mul_of_nonneg_right he h
    have hWint : Integrable (fun z => Real.exp (-U z)*q.density z) volume :=
      hqint.mono' hWmeas.aestronglyMeasurable (by
        filter_upwards [hWpos,hWbound] with z hp hb
        simpa only [Real.norm_eq_abs,abs_of_nonneg hp] using hb)
    have hupper : (∫ z,Real.exp (-U z)*q.density z) ≤ 1 := by
      exact (integral_mono_ae hWint hqint hWbound).trans_eq q.mass
    let b := ∫ z,U z*q.density z
    let F := fun z => (Real.exp (-b)*(1+b))*q.density z -
      Real.exp (-b)*(U z*q.density z)
    have hFint : Integrable F volume :=
      (hqint.const_mul _).sub (hUqint.const_mul _)
    have hFmass : (∫ z,F z) = Real.exp (-b) := by
      rw [integral_sub (hqint.const_mul _) (hUqint.const_mul _)]
      simp only [integral_const_mul,q.mass]
      change Real.exp (-b)*(1+b)*1 - Real.exp (-b)*b = _
      ring
    have hFbound : ∀ᵐ z ∂volume, F z ≤ Real.exp (-U z)*q.density z := by
      filter_upwards [hqpos] with z hq
      have ht : 1-(U z-b) ≤ Real.exp (-(U z-b)) := by
        nlinarith [Real.add_one_le_exp (-(U z-b))]
      have h := mul_le_mul_of_nonneg_left ht (Real.exp_nonneg (-b))
      have he : Real.exp (-b)*Real.exp (-(U z-b)) = Real.exp (-U z) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [he] at h
      have hm := mul_le_mul_of_nonneg_right h hq
      dsimp [F]
      nlinarith
    have hlowb : Real.exp (-b) ≤ ∫ z,Real.exp (-U z)*q.density z := by
      rw [← hFmass]
      exact integral_mono_ae hFint hWint hFbound
    have hlower : Real.exp (-β*u*(∫ z,G z)) ≤ ∫ z,Real.exp (-U z)*q.density z := by
      refine (Real.exp_le_exp.mpr ?_).trans hlowb
      simpa only [neg_mul,b] using neg_le_neg hUqbound
    have hZpos : 0 < ∫ z,Real.exp (-U z)*q.density z := (Real.exp_pos _).trans_le hlower
    refine ⟨hUmeas,hUint,hUpos,hUqint,hWint,hlower,hupper,?_⟩
    have h := (TiltNormalization volume (fun z => Real.exp (-U z)*q.density z)
      hWmeas hWpos hWint hZpos).1
    simpa only [mul_comm] using h

  have replacement_joint_measurable (d N : ℕ) (i : Fin N) :
      Measurable (fun p : Configuration d N × UnitAddTorus (Fin d) =>
        Replacement p.1 i p.2) := by
    apply measurable_pi_lambda
    intro k
    by_cases h : k = i
    · simpa only [Replacement,Function.update_apply,h,↓reduceIte,Function.comp_def] using
        (measurable_snd : Measurable (Prod.snd : Configuration d N × UnitAddTorus (Fin d) → _))
    · simpa only [Replacement,Function.update_apply,h,↓reduceIte,Function.comp_def] using
        ((measurable_pi_apply k).comp measurable_fst :
          Measurable (fun p : Configuration d N × UnitAddTorus (Fin d) => p.1 k))

  have conditionalPotential_joint_measurable (d N : ℕ) (G : UnitAddTorus (Fin d) → ℝ)
      (hG : Measurable G) (β : ℝ) (i : Fin N) :
      Measurable (fun p : Configuration d N × UnitAddTorus (Fin d) =>
        ConditionalPotential G β p.1 i p.2) := by
    dsimp [ConditionalPotential]
    apply Measurable.const_mul
    apply Finset.measurable_fun_sum
    intro j hj
    by_cases h : j = i
    · simp only [h,↓reduceIte]
      exact measurable_const
    · simp only [h,↓reduceIte]
      exact hG.comp (measurable_snd.sub ((measurable_pi_apply j).comp measurable_fst))

  have replacement_twice_same {d N : ℕ} (X : Configuration d N) (i : Fin N)
      (z v : UnitAddTorus (Fin d)) :
      Replacement (Replacement X i z) i v = Replacement X i v := by
    exact Function.update_idem (a := i) z v X

  have conditionalPotential_replacement_same {d N : ℕ}
      (G : UnitAddTorus (Fin d) → ℝ) (β : ℝ) (X : Configuration d N)
      (i : Fin N) (z v : UnitAddTorus (Fin d)) :
      ConditionalPotential G β (Replacement X i z) i v = ConditionalPotential G β X i v := by
    dsimp [ConditionalPotential]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : j = i <;> simp [h,Replacement]

  have conditionalMoment_replacement_same {d N : ℕ}
      (G q : UnitAddTorus (Fin d) → ℝ) (β : ℝ)
      (f : Configuration d N → ℝ) (X : Configuration d N)
      (i : Fin N) (z : UnitAddTorus (Fin d)) :
      (∫ v, Real.exp (-ConditionalPotential G β (Replacement X i z) i v) *
        f (Replacement (Replacement X i z) i v) * q v) =
      (∫ v, Real.exp (-ConditionalPotential G β X i v) * f (Replacement X i v) * q v) := by
    simp_rw [conditionalPotential_replacement_same,replacement_twice_same]

  have boundedWeighted_moments {Ω : Type} [MeasurableSpace Ω]
      (μ : Measure Ω) (w φ : Ω → ℝ) (hw : Measurable w)
      (hwp : ∀ᵐ x ∂μ, 0 ≤ w x) (hwi : Integrable w μ)
      (hZ : 0 < ∫ x,w x ∂μ) (hφ : Measurable φ)
      (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, |φ x| ≤ C) :
      let Z := ∫ x,w x ∂μ
      let ν := NormalizedTilt μ w
      MemLp φ 2 ν ∧ Integrable (fun x => φ x*w x) μ ∧
        Integrable (fun x => φ x^2*w x) μ ∧
        (∫ x,φ x*w x ∂μ) = Z*(∫ x,φ x ∂ν) ∧
        (∫ x,φ x^2*w x ∂μ) = Z*(∫ x,φ x^2 ∂ν) ∧
        (∫ x,φ x*w x ∂μ)^2 ≤ Z*(∫ x,φ x^2*w x ∂μ) := by
    classical
    dsimp only
    let Z := ∫ x,w x ∂μ
    let ν := NormalizedTilt μ w
    have hTilt := TiltNormalization μ w hw hwp hwi hZ
    haveI : IsProbabilityMeasure ν := hTilt.1
    have hφb : ∀ x, ‖φ x‖ ≤ C := by simpa only [Real.norm_eq_abs] using hbound
    have hφ2b : ∀ x, ‖φ x^2‖ ≤ C^2 := by
      intro x
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hφb x) 2
    have hφw : Integrable (fun x => φ x*w x) μ :=
      hwi.bdd_mul hφ.aestronglyMeasurable (Filter.Eventually.of_forall hφb)
    have hφ2w : Integrable (fun x => φ x^2*w x) μ :=
      hwi.bdd_mul (hφ.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall hφ2b)
    have hφLp : MemLp φ 2 ν := MemLp.of_bound hφ.aestronglyMeasurable C
      (Filter.Eventually.of_forall hφb)
    have hφmean : (∫ x,φ x*w x ∂μ) = Z*(∫ x,φ x ∂ν) := by
      have h := (hTilt.2 φ hφ hφw).2
      change (∫ x,φ x ∂ν) = (∫ x,φ x*w x ∂μ)/Z at h
      have hz : Z ≠ 0 := ne_of_gt hZ
      rw [h]
      field_simp
    have hφ2mean : (∫ x,φ x^2*w x ∂μ) = Z*(∫ x,φ x^2 ∂ν) := by
      have h := (hTilt.2 (fun x => φ x^2) (hφ.pow_const 2) hφ2w).2
      change (∫ x,φ x^2 ∂ν) = (∫ x,φ x^2*w x ∂μ)/Z at h
      have hz : Z ≠ 0 := ne_of_gt hZ
      rw [h]
      field_simp
    refine ⟨hφLp,hφw,hφ2w,hφmean,hφ2mean,?_⟩
    have hv := variance_nonneg φ ν
    rw [variance_eq_sub hφLp] at hv
    change 0 ≤ (∫ x,φ x^2 ∂ν) - (∫ x,φ x ∂ν)^2 at hv
    rw [hφmean,hφ2mean]
    have h := mul_nonneg (sq_nonneg Z) hv
    nlinarith

  have weighted_variance_formula {Ω : Type} [MeasurableSpace Ω]
      (μ : Measure Ω) (w φ : Ω → ℝ) (hw : Measurable w)
      (hwp : ∀ᵐ x ∂μ, 0 ≤ w x) (hwi : Integrable w μ)
      (hZ : 0 < ∫ x,w x ∂μ) (hφ : Measurable φ)
      (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, |φ x| ≤ C) :
      let Z := ∫ x,w x ∂μ
      let ν := NormalizedTilt μ w
      Z * variance φ ν = (∫ x,φ x^2*w x ∂μ) - (∫ x,φ x*w x ∂μ)^2/Z := by
    dsimp only
    have h := boundedWeighted_moments μ w φ hw hwp hwi hZ hφ C hC hbound
    haveI := (TiltNormalization μ w hw hwp hwi hZ).1
    rw [variance_eq_sub h.1,h.2.2.2.1,h.2.2.2.2.1]
    have hz : (∫ x,w x ∂μ) ≠ 0 := ne_of_gt hZ
    change (∫ x,w x ∂μ) * ((∫ x,φ x^2 ∂NormalizedTilt μ w) -
      (∫ x,φ x ∂NormalizedTilt μ w)^2) = _
    field_simp <;> ring

  have weighted_moment_abs_bound {Ω : Type} [MeasurableSpace Ω]
      (μ : Measure Ω) (w φ : Ω → ℝ) (hw : Measurable w)
      (hwp : ∀ᵐ x ∂μ, 0 ≤ w x) (hwi : Integrable w μ)
      (hZ : 0 < ∫ x,w x ∂μ) (hφ : Measurable φ)
      (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, |φ x| ≤ C) :
      |∫ x,φ x*w x ∂μ| ≤ C * ∫ x,w x ∂μ := by
    have h := boundedWeighted_moments μ w φ hw hwp hwi hZ hφ C hC hbound
    have hν := TiltNormalization μ w hw hwp hwi hZ
    haveI := hν.1
    have hφint : Integrable φ (NormalizedTilt μ w) := (hν.2 φ hφ h.2.1).1
    have hb : |∫ x,φ x ∂NormalizedTilt μ w| ≤ C := by
      calc
        _ = ‖∫ x,φ x ∂NormalizedTilt μ w‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∫ x,‖φ x‖ ∂NormalizedTilt μ w := norm_integral_le_integral_norm _
        _ ≤ ∫ x,C ∂NormalizedTilt μ w := integral_mono hφint.norm (integrable_const C)
          (fun x => by simpa only [Real.norm_eq_abs] using hbound x)
        _ = C := by simp
    rw [h.2.2.2.1,abs_mul,abs_of_nonneg hZ.le]
    exact (mul_le_mul_of_nonneg_left hb hZ.le).trans_eq (mul_comm _ _)

  have boundedConditional_variance_integral (d N : ℕ) (hN : 2 ≤ N) (l u β : ℝ)
      (q : BoundedBackground d l u) (hβ : 0 ≤ β)
      (G : UnitAddTorus (Fin d) → ℝ) (hG : Measurable G)
      (hGi : Integrable G volume) (hGn : ∀ x, 0 ≤ G x) (hGe : ∀ x, G (-x) = G x)
      (i : Fin N) (f : Configuration d N → ℝ) (hf : Measurable f)
      (C : ℝ) (hC : 0 ≤ C) (hb : ∀ X, |f X| ≤ C) :
      let P := CanonicalLaw (N := N) G q.density β
      let Z := fun X : Configuration d N => ∫ z, Real.exp (-ConditionalPotential G β X i z)*q.density z
      let M := fun X : Configuration d N => ∫ z, Real.exp (-ConditionalPotential G β X i z)*f (Replacement X i z)*q.density z
      let T := fun X : Configuration d N => ∫ z, Real.exp (-ConditionalPotential G β X i z)*(f (Replacement X i z))^2*q.density z
      let ν := fun X : Configuration d N => NormalizedTilt volume (fun z=>q.density z*Real.exp (-ConditionalPotential G β X i z))
      Measurable Z ∧ Measurable M ∧ Measurable T ∧
      Integrable (fun X=>Z X*variance (fun z=>f (Replacement X i z)) (ν X)) P ∧
      (∫ X,Z X*f X^2 ∂P) = ∫ X,T X ∂P ∧
      (∫ X,f X*M X ∂P) = ∫ X,(M X)^2/Z X ∂P ∧
      (∫ X,Z X*f X^2-f X*M X ∂P) =
        ∫ X,Z X*variance (fun z=>f (Replacement X i z)) (ν X) ∂P := by
    classical
    dsimp only
    let P := CanonicalLaw (N := N) G q.density β
    let r := fun (X : Configuration d N) z => Real.exp (-ConditionalPotential G β X i z)*q.density z
    let Z := fun X : Configuration d N => ∫ z,r X z
    let M := fun X : Configuration d N => ∫ z,r X z*f (Replacement X i z)
    let T := fun X : Configuration d N => ∫ z,r X z*(f (Replacement X i z))^2
    let ν := fun X : Configuration d N => NormalizedTilt volume (fun z=>q.density z*Real.exp (-ConditionalPotential G β X i z))
    let m := fun X => M X/Z X
    have hnorm (X : Configuration d N) := conditionalNormalizer_bounds d N hN l u β q hβ G hG hGi hGn X i
    have hz (X : Configuration d N) : 0 < Z X ∧ Z X ≤ 1 :=
      ⟨(Real.exp_pos _).trans_le (hnorm X).2.2.2.2.2.1,(hnorm X).2.2.2.2.2.2.1⟩
    have hrm : Measurable (fun p : Configuration d N × UnitAddTorus (Fin d) => r p.1 p.2) :=
      ((conditionalPotential_joint_measurable d N G hG β i).neg.exp).mul (q.measurable.comp measurable_snd)
    have hRm := replacement_joint_measurable d N i
    have hZm : Measurable Z := hrm.stronglyMeasurable.integral_prod_right'.measurable
    have hMm : Measurable M := (hrm.mul (hf.comp hRm)).stronglyMeasurable.integral_prod_right'.measurable
    have hTm : Measurable T := (hrm.mul ((hf.comp hRm).pow_const 2)).stronglyMeasurable.integral_prod_right'.measurable
    have hmm : Measurable m := hMm.div hZm
    have hfw (X : Configuration d N) : Measurable (fun z => f (Replacement X i z)) :=
      hf.comp (hRm.comp (measurable_const.prodMk measurable_id))
    have hrn (X : Configuration d N) : ∀ᵐ z ∂volume, 0 ≤ r X z := by
      filter_upwards [q.bounds] with z hz
      exact mul_nonneg (Real.exp_pos _).le (q.lower_pos.le.trans hz.1)
    have hrfm (X : Configuration d N) : Measurable (r X) :=
      hrm.comp (measurable_const.prodMk measurable_id)
    have hri (X : Configuration d N) : Integrable (r X) volume := (hnorm X).2.2.2.2.1
    have hMb (X : Configuration d N) : |M X| ≤ C*Z X := by
      simpa only [M, Z, mul_comm] using weighted_moment_abs_bound volume (r X)
        (fun z=>f (Replacement X i z)) (hrfm X) (hrn X) (hri X) (hz X).1 (hfw X) C hC (fun z=>hb _)
    have hmb (X : Configuration d N) : |m X| ≤ C := by
      dsimp only [m]
      rw [abs_div,abs_of_pos (hz X).1]
      exact (div_le_iff₀ (hz X).1).mpr (hMb X)
    have hTb (X : Configuration d N) : |T X| ≤ C^2 := by
      have hh : ∀ z, |(f (Replacement X i z))^2| ≤ C^2 := by
        intro z
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hb _) 2
      have hh' := weighted_moment_abs_bound volume (r X)
        (fun z=>(f (Replacement X i z))^2) (hrfm X) (hrn X) (hri X) (hz X).1
        ((hfw X).pow_const 2) (C^2) (sq_nonneg C) hh
      change |∫ z,(f (Replacement X i z))^2*r X z| ≤ C^2*Z X at hh'
      have he : T X = ∫ z,(f (Replacement X i z))^2*r X z := by simp only [T,mul_comm]
      rw [he]
      exact hh'.trans (mul_le_of_le_one_right (sq_nonneg C) (hz X).2)
    have hzrep (X : Configuration d N) (z : UnitAddTorus (Fin d)) : Z (Replacement X i z)=Z X := by
      simp only [Z,r,conditionalPotential_replacement_same]
    have hmrep (X : Configuration d N) (z : UnitAddTorus (Fin d)) : m (Replacement X i z)=m X := by
      simp only [m,M,Z,r,conditionalPotential_replacement_same,replacement_twice_same]
    have hP := GibbsNormalizerBounds d N hN l u q G hG hGi 0 β (le_refl 0) hβ
      (Filter.Eventually.of_forall fun x=>by simpa using hGn x)
    haveI : IsProbabilityMeasure P := hP.2.2.2
    have hintZ : Integrable (fun X=>Z X*f X^2) P := by
      apply Integrable.of_bound (hZm.mul (hf.pow_const 2)).aestronglyMeasurable (C^2)
      apply Filter.Eventually.of_forall
      intro X
      change |Z X*f X^2| ≤ C^2
      rw [abs_mul,abs_of_pos (hz X).1,abs_pow]
      exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hb X) 2) (hz X).1.le).trans
        (mul_le_of_le_one_left (sq_nonneg C) (hz X).2)
    have hintT : Integrable T P := Integrable.of_bound hTm.aestronglyMeasurable (C^2)
      (Filter.Eventually.of_forall fun X=>by simpa only [Real.norm_eq_abs] using hTb X)
    have hintM : Integrable (fun X=>f X*M X) P := by
      apply Integrable.of_bound (hf.mul hMm).aestronglyMeasurable (C^2)
      apply Filter.Eventually.of_forall
      intro X
      change |f X*M X| ≤ C^2
      rw [abs_mul]
      have hmle : |M X| ≤ C := (hMb X).trans (mul_le_of_le_one_right hC (hz X).2)
      exact (mul_le_mul (hb X) hmle (abs_nonneg _) hC).trans_eq (by ring)
    have hTidentity : (∫ X,Z X*f X^2 ∂P) = ∫ X,T X ∂P := by
      have he := (joint_test_exchange d N hN l u β q hβ G hG hGi hGn hGe i
        (fun p=>f p.1^2) ((hf.comp measurable_fst).pow_const 2)
        ⟨C^2,fun p=>by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hb _) 2⟩).2
      simpa only [P,Z,T,r,integral_mul_const] using he
    have hMidentity : (∫ X,f X*M X ∂P) = ∫ X,(M X)^2/Z X ∂P := by
      have he := (joint_test_exchange d N hN l u β q hβ G hG hGi hGn hGe i
        (fun p=>f p.1*m p.1) ((hf.mul hmm).comp measurable_fst)
        ⟨C^2,fun p=>by rw [abs_mul]; exact (mul_le_mul (hb _) (hmb _) (abs_nonneg _) hC).trans_eq (by ring)⟩).2
      have hl (X : Configuration d N) : (∫ z,r X z*(f X*m X))=f X*M X := by
        rw [integral_mul_const]
        change Z X*(f X*(M X/Z X))=f X*M X
        field_simp [ne_of_gt (hz X).1]
        <;> ring
      have hr (X : Configuration d N) : (∫ z,r X z*(f (Replacement X i z)*m (Replacement X i z)))=(M X)^2/Z X := by
        simp_rw [hmrep]
        simp_rw [←mul_assoc]
        rw [integral_mul_const]
        dsimp only [m,M]
        ring
      change (∫ X,(∫ z,r X z*(f X*m X)) ∂P) =
        ∫ X,(∫ z,r X z*(f (Replacement X i z)*m (Replacement X i z))) ∂P at he
      simp_rw [hl,hr] at he
      exact he
    have hvar (X : Configuration d N) : Z X*variance (fun z=>f (Replacement X i z)) (ν X)=T X-(M X)^2/Z X := by
      have hh := weighted_variance_formula volume (r X) (fun z=>f (Replacement X i z))
        (hrfm X) (hrn X) (hri X) (hz X).1 (hfw X) C hC (fun z=>hb _)
      simpa only [ν,r,mul_comm,M,T,Z] using hh
    have hintMM : Integrable (fun X=>(M X)^2/Z X) P := by
      apply Integrable.of_bound ((hMm.pow_const 2).div hZm).aestronglyMeasurable (C^2)
      apply Filter.Eventually.of_forall
      intro X
      change |(M X)^2/Z X| ≤ C^2
      rw [abs_div,abs_pow,abs_of_pos (hz X).1]
      apply (div_le_iff₀ (hz X).1).mpr
      have hh := pow_le_pow_left₀ (abs_nonneg _) (hMb X) 2
      have zz : (Z X)^2 ≤ Z X := by
        simpa only [pow_two] using mul_le_of_le_one_right (hz X).1.le (hz X).2
      nlinarith [mul_le_mul_of_nonneg_left zz (sq_nonneg C)]
    have hintvar : Integrable (fun X=>Z X*variance (fun z=>f (Replacement X i z)) (ν X)) P := by
      simp_rw [hvar]
      exact hintT.sub hintMM
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    · exact hZm
    · simpa only [M,r,mul_assoc,mul_comm,mul_left_comm] using hMm
    · simpa only [T,r,mul_assoc,mul_comm,mul_left_comm] using hTm
    · exact hintvar
    · simpa only [Z,T,r,mul_assoc,mul_comm,mul_left_comm] using hTidentity
    · simpa only [M,r,mul_assoc,mul_comm,mul_left_comm] using hMidentity
    · have he : (∫ X,Z X*f X^2-f X*M X ∂P) =
          ∫ X,Z X*variance (fun z=>f (Replacement X i z)) (ν X) ∂P := by
        simp_rw [hvar]
        rw [integral_sub hintZ hintM,integral_sub hintT hintMM,hTidentity,hMidentity]
      simpa only [Z,M,r,ν,mul_assoc,mul_comm,mul_left_comm] using he

  have boundedJump_variance_energy (d N : ℕ) (hN : 2 ≤ N) (l u β : ℝ)
      (q : BoundedBackground d l u) (hβ : 0 ≤ β)
      (G : UnitAddTorus (Fin d) → ℝ) (hG : Measurable G)
      (hGi : Integrable G volume) (hGn : ∀ x, 0 ≤ G x) (hGe : ∀ x, G (-x) = G x)
      (f : Configuration d N → ℝ) (hf : Measurable f)
      (C : ℝ) (hC : 0 ≤ C) (hb : ∀ X, |f X| ≤ C) :
      let P := CanonicalLaw (N := N) G q.density β
      let Z := fun (X : Configuration d N) (i : Fin N) => ∫ z,Real.exp (-ConditionalPotential G β X i z)*q.density z
      let ν := fun (X : Configuration d N) (i : Fin N) => NormalizedTilt volume (fun z=>q.density z*Real.exp (-ConditionalPotential G β X i z))
      (-(∫ X,f X*JumpOperator G q.density β f X ∂P) =
        ∑ i : Fin N, (∫ X, Z X i * ProbabilityTheory.variance (fun z => f (Replacement X i z)) (ν X i) ∂P)) := by
    classical
    dsimp only
    let P := CanonicalLaw (N := N) G q.density β
    let r := fun (i : Fin N) (X : Configuration d N) z => Real.exp (-ConditionalPotential G β X i z)*q.density z
    let Z := fun (i : Fin N) (X : Configuration d N) => ∫ z,r i X z
    let M := fun (i : Fin N) (X : Configuration d N) => ∫ z,r i X z*f (Replacement X i z)
    let A := fun (i : Fin N) (X : Configuration d N) => ∫ z,r i X z*(f (Replacement X i z)-f X)
    have hn (i : Fin N) (X : Configuration d N) := conditionalNormalizer_bounds d N hN l u β q hβ G hG hGi hGn X i
    have hz (i : Fin N) (X : Configuration d N) : 0 < Z i X ∧ Z i X ≤ 1 :=
      ⟨(Real.exp_pos _).trans_le (hn i X).2.2.2.2.2.1,(hn i X).2.2.2.2.2.2.1⟩
    have hrm (i : Fin N) : Measurable (fun p : Configuration d N × UnitAddTorus (Fin d)=>r i p.1 p.2) :=
      ((conditionalPotential_joint_measurable d N G hG β i).neg.exp).mul (q.measurable.comp measurable_snd)
    have hRm (i : Fin N) := replacement_joint_measurable d N i
    have hAm (i : Fin N) : Measurable (A i) :=
      ((hrm i).mul ((hf.comp (hRm i)).sub (hf.comp measurable_fst))).stronglyMeasurable.integral_prod_right'.measurable
    have hrn (i : Fin N) (X : Configuration d N) : ∀ᵐ z ∂volume,0≤r i X z := by
      filter_upwards [q.bounds] with z hq
      exact mul_nonneg (Real.exp_pos _).le (q.lower_pos.le.trans hq.1)
    have hrfm (i : Fin N) (X : Configuration d N) : Measurable (r i X) :=
      (hrm i).comp (measurable_const.prodMk measurable_id)
    have hfw (i : Fin N) (X : Configuration d N) : Measurable (fun z=>f (Replacement X i z)) :=
      hf.comp ((hRm i).comp (measurable_const.prodMk measurable_id))
    have hri (i : Fin N) (X : Configuration d N) : Integrable (r i X) volume := (hn i X).2.2.2.2.1
    have hAb (i : Fin N) (X : Configuration d N) : |A i X| ≤ 2*C := by
      have hD : ∀ z,|f (Replacement X i z)-f X| ≤ 2*C := fun z=>
        (abs_sub _ _).trans (by linarith [hb (Replacement X i z),hb X])
      have hh := weighted_moment_abs_bound volume (r i X) (fun z=>f (Replacement X i z)-f X)
        (hrfm i X) (hrn i X) (hri i X) (hz i X).1 ((hfw i X).sub measurable_const) (2*C) (by positivity) hD
      have hA : |A i X| ≤ 2*C*Z i X := by simpa only [A,Z,mul_comm] using hh
      exact hA.trans (mul_le_of_le_one_right (by positivity) (hz i X).2)
    have hP := GibbsNormalizerBounds d N hN l u q G hG hGi 0 β (le_refl 0) hβ
      (Filter.Eventually.of_forall fun x=>by simpa using hGn x)
    haveI : IsProbabilityMeasure P := hP.2.2.2
    have hint (i : Fin N) : Integrable (fun X=>f X*A i X) P := by
      apply Integrable.of_bound (hf.mul (hAm i)).aestronglyMeasurable (2*C^2)
      apply Filter.Eventually.of_forall
      intro X
      change |f X*A i X| ≤ 2*C^2
      rw [abs_mul]
      exact (mul_le_mul (hb X) (hAb i X) (abs_nonneg _) hC).trans_eq (by ring)
    have hraw (i : Fin N) (X : Configuration d N) : A i X=M i X-Z i X*f X := by
      have hφi : Integrable (fun z=>r i X z*f (Replacement X i z)) volume := by
        have hh := (boundedWeighted_moments volume (r i X) (fun z=>f (Replacement X i z))
          (hrfm i X) (hrn i X) (hri i X) (hz i X).1 (hfw i X) C hC (fun z=>hb _)).2.1
        simpa only [mul_comm] using hh
      have he : (fun z=>r i X z*(f (Replacement X i z)-f X))=
          (fun z=>r i X z*f (Replacement X i z)-r i X z*f X) := by funext z; ring
      dsimp only [A]
      rw [he,integral_sub hφi ((hri i X).mul_const (f X)),integral_mul_const]
    have hJraw : JumpOperator G q.density β f = fun X=>∑ i : Fin N,A i X := by
      funext X
      unfold JumpOperator
      apply Finset.sum_congr rfl
      intro i hi
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z=>by dsimp only [A,r]; ring
    rw [hJraw]
    simp only [Finset.mul_sum]
    rw [integral_finsetSum Finset.univ (fun i _=>hint i),←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have he : (fun X=>-(f X*A i X))=(fun X=>Z i X*f X^2-f X*M i X) := by
      funext X
      rw [hraw]
      ring
    rw [←integral_neg,he]
    have hv := (boundedConditional_variance_integral d N hN l u β q hβ G hG hGi hGn hGe i f hf C hC hb).2.2.2.2.2.2
    simpa only [Z,M,r,mul_assoc,mul_comm,mul_left_comm] using hv
  have real_L2_inner_toLp {α : Type} [MeasurableSpace α] {μ : Measure α}
      (f g : α → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
      inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x*g x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hx hy
    simp [hx,hy,mul_comm]
  have real_L2_norm_sq_toLp {α : Type} [MeasurableSpace α] {μ : Measure α}
      (f : α → ℝ) (hf : MemLp f 2 μ) :
      ‖hf.toLp f‖^2 = ∫ x,f x^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq,real_L2_inner_toLp]
    simp_rw [pow_two]
  intro P Z ν
  have hP := (GibbsNormalizerBounds d N hN l u q G hG hGi 0 β (le_refl 0) hβ
    (Filter.Eventually.of_forall fun x => by simpa using hGn x)).2.2.2
  haveI : MeasureTheory.IsProbabilityMeasure P := hP
  refine ⟨hP, ?_, ?_⟩
  · intro X i
    have hn := conditionalNormalizer_bounds d N hN l u β q hβ G hG hGi hGn X i
    exact ⟨hn.2.2.2.2.2.1, hn.2.2.2.2.2.2.1, hn.2.2.2.2.2.2.2⟩
  · intro f hf hb E
    obtain ⟨C, hCbound⟩ := hb
    have hC : 0 ≤ C := (abs_nonneg (f 0)).trans (hCbound 0)
    obtain ⟨L, hL, _unique⟩ := JumpL2Construction
      d N hN l u β q hβ G hG hGi hGn hGe
    have hfLp : MeasureTheory.MemLp f 2 P := MeasureTheory.MemLp.of_bound hf.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun X => by simpa only [Real.norm_eq_abs] using hCbound X)
    have hc := hL.2.2.2 f hfLp
    have hLv : L (hfLp.toLp f) = hc.1.toLp (JumpOperator G q.density β f) := by
      apply MeasureTheory.Lp.ext
      exact hc.2.1.trans hc.1.coeFn_toLp.symm
    have hE : -inner ℝ (hfLp.toLp f) (L (hfLp.toLp f)) = E := by
      rw [hLv, real_L2_inner_toLp]
    have hclaims := hc.2.2
    dsimp only at hclaims
    rw [hE] at hclaims
    have hfnorm := real_L2_norm_sq_toLp f hfLp
    have hEb : E ≤ 2 * (N : ℝ) * (∫ X,f X^2 ∂P) := by
      rw [← hfnorm]
      exact hclaims.2.2.1
    have hLnorm : (∫ X,(JumpOperator G q.density β f X)^2 ∂P) ≤
        4*(N : ℝ)^2*(∫ X,f X^2 ∂P) := by
      rw [← real_L2_norm_sq_toLp _ hc.1, ← hLv]
      have hbop : ‖L (hfLp.toLp f)‖ ≤ 2*(N : ℝ)*‖hfLp.toLp f‖ :=
        (L.le_opNorm _).trans (mul_le_mul_of_nonneg_right hL.1 (norm_nonneg _))
      calc
        _ ≤ (2*(N : ℝ)*‖hfLp.toLp f‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hbop 2
        _ = _ := by rw [← hfnorm]; ring
    refine ⟨hclaims.1, ?_, hEb, hLnorm, hclaims.2.2.2, ?_⟩
    · exact boundedJump_variance_energy d N hN l u β q hβ G hG hGi hGn hGe f hf C hC hCbound
    · intro h hh hhb
      obtain ⟨D, hD⟩ := hhb
      have hhLp : MeasureTheory.MemLp h 2 P := MeasureTheory.MemLp.of_bound hh.aestronglyMeasurable D
        (Filter.Eventually.of_forall fun X => by simpa only [Real.norm_eq_abs] using hD X)
      have hch := hL.2.2.2 h hhLp
      have hLh : L (hhLp.toLp h) = hch.1.toLp (JumpOperator G q.density β h) := by
        apply MeasureTheory.Lp.ext
        exact hch.2.1.trans hch.1.coeFn_toLp.symm
      have hs := hL.2.1 (hfLp.toLp f) (hhLp.toLp h)
      rw [hLh, hLv, real_L2_inner_toLp,
        real_L2_inner_toLp] at hs
      simpa only [mul_comm] using hs

