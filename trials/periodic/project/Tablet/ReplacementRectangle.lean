import Tablet.ReplacementJointBalance
import Tablet.JumpConditionalBalance
import Tablet.ReplacementRectangleExchange
import Mathlib.MeasureTheory.Group.Integral
open MeasureTheory ProbabilityTheory
set_option maxHeartbeats 4000000
-- [TABLET NODE: ReplacementRectangle]
theorem ReplacementRectangle (d N : ℕ) (hN : 2 ≤ N) (l u β : ℝ)
    (q : BoundedBackground d l u) (hβ : 0 ≤ β)
    (G : UnitAddTorus (Fin d) → ℝ) (hG : Measurable G)
    (hGi : MeasureTheory.Integrable G MeasureTheory.volume)
    (hGn : ∀ x, 0 ≤ G x) (hGe : ∀ x, G (-x) = G x)
    (f : Configuration d N → ℝ) (hf : Measurable f)
    (hfb : ∃ C : ℝ, ∀ X, |f X| ≤ C) :
    let P := CanonicalLaw (N := N) G q.density β
    let U := ConditionalPotential G β
    let D := fun X i z => f (Replacement X i z) - f X
    let Z := fun X i => ∫ z, Real.exp (-U X i z) * q.density z
    let ν := fun X i => NormalizedTilt MeasureTheory.volume
      (fun z => q.density z * Real.exp (-U X i z))
    let S := ∑ i : Fin N, ∫ X,
      (∫ z, Real.exp (-U X i z) * D X i z * q.density z)^2 ∂P
    S = ∑ i : Fin N, ∫ X, (Z X i)^2 *
      ProbabilityTheory.variance (fun z => f (Replacement X i z)) (ν X i) ∂P ∧
    Real.exp (-β * u * (∫ x, G x)) *
      (-(∫ X, f X * JumpOperator G q.density β f X ∂P)) ≤ S ∧
    ∀ i j : Fin N, i ≠ j →
      let R := fun X z v =>
        Real.exp (-U X i z - U X j v - (β / N) * G (z - v)) *
          q.density z * q.density v
      let C := ∫ X, (∫ z, ∫ v, R X z v * D X i z * D X j v) ∂P
      C = (1 / 4 : ℝ) * ∫ X, (∫ z, ∫ v, R X z v *
        (f X - f (Replacement X i z) - f (Replacement X j v) +
          f (Replacement (Replacement X i z) j v))^2) ∂P ∧
      0 ≤ C := by
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

  have weighted_centered_variance_formula {Ω : Type} [MeasurableSpace Ω]
      (μ : Measure Ω) (w φ : Ω → ℝ) (hw : Measurable w)
      (hwp : ∀ᵐ x ∂μ, 0 ≤ w x) (hwi : Integrable w μ)
      (hZ : 0 < ∫ x,w x ∂μ) (hφ : Measurable φ)
      (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, |φ x| ≤ C) :
      let Z := ∫ x,w x ∂μ
      let m := (∫ x,φ x*w x ∂μ)/Z
      Integrable (fun x=>(φ x-m)^2*w x) μ ∧
      (∫ x,(φ x-m)^2*w x ∂μ) = Z*variance φ (NormalizedTilt μ w) := by
    dsimp only
    let Z := ∫ x,w x ∂μ
    let m := (∫ x,φ x*w x ∂μ)/Z
    have h := boundedWeighted_moments μ w φ hw hwp hwi hZ hφ C hC hbound
    have hTilt := TiltNormalization μ w hw hwp hwi hZ
    have hm : m = ∫ x,φ x ∂NormalizedTilt μ w := by
      exact (hTilt.2 φ hφ h.2.1).2.symm
    have hb : ∀ x, ‖(φ x-m)^2‖ ≤ (C+|m|)^2 := by
      intro x
      rw [norm_pow]
      apply pow_le_pow_left₀ (norm_nonneg _)
      calc
        ‖φ x-m‖ ≤ ‖φ x‖+‖m‖ := norm_sub_le _ _
        _ ≤ C+|m| := by simpa only [Real.norm_eq_abs] using add_le_add (hbound x) (le_refl |m|)
    have hi : Integrable (fun x=>(φ x-m)^2*w x) μ :=
      hwi.bdd_mul ((hφ.sub measurable_const).pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall hb)
    refine ⟨hi,?_⟩
    have hh := (hTilt.2 (fun x=>(φ x-m)^2) ((hφ.sub measurable_const).pow_const 2) hi).2
    rw [variance_eq_integral hφ.aemeasurable,←hm,hh]
    change (∫ x,(φ x-m)^2*w x ∂μ)=Z*((∫ x,(φ x-m)^2*w x ∂μ)/Z)
    have hz : Z ≠ 0 := ne_of_gt hZ
    field_simp [hz]

  have boundedConditional_square_integral (d N : ℕ) (hN : 2 ≤ N) (l u β : ℝ)
      (q : BoundedBackground d l u) (hβ : 0 ≤ β)
      (G : UnitAddTorus (Fin d) → ℝ) (hG : Measurable G)
      (hGi : Integrable G volume) (hGn : ∀ x, 0 ≤ G x) (hGe : ∀ x, G (-x) = G x)
      (i : Fin N) (f : Configuration d N → ℝ) (hf : Measurable f)
      (C : ℝ) (hC : 0 ≤ C) (hb : ∀ X, |f X| ≤ C) :
      let P := CanonicalLaw (N := N) G q.density β
      let Z := fun X : Configuration d N => ∫ z, Real.exp (-ConditionalPotential G β X i z)*q.density z
      let ν := fun X : Configuration d N => NormalizedTilt volume (fun z=>q.density z*Real.exp (-ConditionalPotential G β X i z))
      Integrable (fun X=>(Z X)^2*variance (fun z=>f (Replacement X i z)) (ν X)) P ∧
      (∫ X,(∫ z,Real.exp (-ConditionalPotential G β X i z)*(f (Replacement X i z)-f X)*q.density z)^2 ∂P) =
        ∫ X,(Z X)^2*variance (fun z=>f (Replacement X i z)) (ν X) ∂P := by
    classical
    dsimp only
    let P := CanonicalLaw (N := N) G q.density β
    let r := fun (X : Configuration d N) z => Real.exp (-ConditionalPotential G β X i z)*q.density z
    let Z := fun X : Configuration d N => ∫ z,r X z
    let M := fun X : Configuration d N => ∫ z,r X z*f (Replacement X i z)
    let ν := fun X : Configuration d N => NormalizedTilt volume (fun z=>q.density z*Real.exp (-ConditionalPotential G β X i z))
    let m := fun X => M X/Z X
    have hn (X : Configuration d N) := conditionalNormalizer_bounds d N hN l u β q hβ G hG hGi hGn X i
    have hz (X : Configuration d N) : 0 < Z X ∧ Z X ≤ 1 :=
      ⟨(Real.exp_pos _).trans_le (hn X).2.2.2.2.2.1,(hn X).2.2.2.2.2.2.1⟩
    have hrm : Measurable (fun p : Configuration d N × UnitAddTorus (Fin d) => r p.1 p.2) :=
      ((conditionalPotential_joint_measurable d N G hG β i).neg.exp).mul (q.measurable.comp measurable_snd)
    have hRm := replacement_joint_measurable d N i
    have hZm : Measurable Z := hrm.stronglyMeasurable.integral_prod_right'.measurable
    have hMm : Measurable M := (hrm.mul (hf.comp hRm)).stronglyMeasurable.integral_prod_right'.measurable
    have hmm : Measurable m := hMm.div hZm
    have hfw (X : Configuration d N) : Measurable (fun z=>f (Replacement X i z)) :=
      hf.comp (hRm.comp (measurable_const.prodMk measurable_id))
    have hrfm (X : Configuration d N) : Measurable (r X) := hrm.comp (measurable_const.prodMk measurable_id)
    have hrn (X : Configuration d N) : ∀ᵐ z ∂volume, 0 ≤ r X z := by
      filter_upwards [q.bounds] with z hq
      exact mul_nonneg (Real.exp_pos _).le (q.lower_pos.le.trans hq.1)
    have hri (X : Configuration d N) : Integrable (r X) volume := (hn X).2.2.2.2.1
    have hmb (X : Configuration d N) : |m X| ≤ C := by
      have hh := weighted_moment_abs_bound volume (r X) (fun z=>f (Replacement X i z))
        (hrfm X) (hrn X) (hri X) (hz X).1 (hfw X) C hC (fun z=>hb _)
      have hM : |M X| ≤ C*Z X := by simpa only [M,Z,mul_comm] using hh
      dsimp only [m]
      rw [abs_div,abs_of_pos (hz X).1]
      exact (div_le_iff₀ (hz X).1).mpr hM
    have hzrep (X : Configuration d N) (z : UnitAddTorus (Fin d)) : Z (Replacement X i z)=Z X := by
      simp only [Z,r,conditionalPotential_replacement_same]
    have hmrep (X : Configuration d N) (z : UnitAddTorus (Fin d)) : m (Replacement X i z)=m X := by
      simp only [m,M,Z,r,conditionalPotential_replacement_same,replacement_twice_same]
    have hcenter (X : Configuration d N) : (∫ z,r X z*(f (Replacement X i z)-m X)^2)=
        Z X*variance (fun z=>f (Replacement X i z)) (ν X) := by
      have hh := (weighted_centered_variance_formula volume (r X) (fun z=>f (Replacement X i z))
        (hrfm X) (hrn X) (hri X) (hz X).1 (hfw X) C hC (fun z=>hb _)).2
      simpa only [m,M,Z,r,ν,mul_comm] using hh
    have hraw (X : Configuration d N) : (∫ z,r X z*(f (Replacement X i z)-f X))=M X-Z X*f X := by
      have hφint : Integrable (fun z=>r X z*f (Replacement X i z)) volume := by
        have hh := (boundedWeighted_moments volume (r X) (fun z=>f (Replacement X i z))
          (hrfm X) (hrn X) (hri X) (hz X).1 (hfw X) C hC (fun z=>hb _)).2.1
        simpa only [mul_comm] using hh
      have he : (fun z=>r X z*(f (Replacement X i z)-f X)) =
          (fun z=>r X z*f (Replacement X i z)-r X z*f X) := by funext z; ring
      rw [he,integral_sub hφint ((hri X).mul_const (f X)),integral_mul_const]
    have hrawsq (X : Configuration d N) : (∫ z,r X z*(f (Replacement X i z)-f X))^2=
        (Z X)^2*(f X-m X)^2 := by
      rw [hraw]
      dsimp only [m]
      field_simp [ne_of_gt (hz X).1]
      <;> ring
    have hbound (X : Configuration d N) : |Z X*(f X-m X)^2| ≤ (2*C)^2 := by
      rw [abs_mul,abs_of_pos (hz X).1,abs_pow]
      have ha : |f X-m X| ≤ 2*C := (abs_sub _ _).trans (by linarith [hb X,hmb X])
      exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) ha 2) (hz X).1.le).trans
        (mul_le_of_le_one_left (sq_nonneg _) (hz X).2)
    have hex := (joint_test_exchange d N hN l u β q hβ G hG hGi hGn hGe i
      (fun p=>Z p.1*(f p.1-m p.1)^2) ((hZm.mul ((hf.sub hmm).pow_const 2)).comp measurable_fst)
      ⟨(2*C)^2,fun p=>hbound p.1⟩).2
    have hl (X : Configuration d N) : (∫ z,r X z*(Z X*(f X-m X)^2))=(Z X)^2*(f X-m X)^2 := by
      rw [integral_mul_const]
      change Z X*(Z X*(f X-m X)^2)=(Z X)^2*(f X-m X)^2
      ring
    have hr (X : Configuration d N) : (∫ z,r X z*(Z (Replacement X i z)*(f (Replacement X i z)-m (Replacement X i z))^2))=
        (Z X)^2*variance (fun z=>f (Replacement X i z)) (ν X) := by
      simp_rw [hzrep,hmrep]
      have he : (fun z=>r X z*(Z X*(f (Replacement X i z)-m X)^2))=
          (fun z=>(r X z*(f (Replacement X i z)-m X)^2)*Z X) := by funext z; ring
      rw [he,integral_mul_const,hcenter]
      ring
    have hrightint := (joint_test_exchange d N hN l u β q hβ G hG hGi hGn hGe i
      (fun p=>Z (Replacement p.1 i p.2)*(f (Replacement p.1 i p.2)-m (Replacement p.1 i p.2))^2)
      ((hZm.mul ((hf.sub hmm).pow_const 2)).comp hRm)
      ⟨(2*C)^2,fun p=>hbound (Replacement p.1 i p.2)⟩).1
    have hintvar : Integrable (fun X=>(Z X)^2*variance (fun z=>f (Replacement X i z)) (ν X)) P := by
      have hefun : (fun X=>∫ z,r X z*(Z (Replacement X i z)*(f (Replacement X i z)-m (Replacement X i z))^2))=
          (fun X=>(Z X)^2*variance (fun z=>f (Replacement X i z)) (ν X)) := by
        funext X
        exact hr X
      change Integrable (fun X=>∫ z,r X z*(Z (Replacement X i z)*(f (Replacement X i z)-m (Replacement X i z))^2)) P at hrightint
      rw [hefun] at hrightint
      exact hrightint
    change (∫ X,(∫ z,r X z*(Z X*(f X-m X)^2)) ∂P)=
      ∫ X,(∫ z,r X z*(Z (Replacement X i z)*(f (Replacement X i z)-m (Replacement X i z))^2)) ∂P at hex
    simp_rw [hl,hr] at hex
    have he : (∫ X,(∫ z,r X z*(f (Replacement X i z)-f X))^2 ∂P)=
        ∫ X,(Z X)^2*variance (fun z=>f (Replacement X i z)) (ν X) ∂P := by
      simp_rw [hrawsq]
      exact hex
    refine ⟨hintvar,?_⟩
    simpa only [r,Z,ν,mul_assoc,mul_comm,mul_left_comm] using he

  obtain ⟨C,hC⟩ := hfb
  have hC0 : 0 ≤ C := (abs_nonneg (f 0)).trans (hC 0)
  let P := CanonicalLaw (N := N) G q.density β
  let Z := fun (X : Configuration d N) (i : Fin N) => ∫ z, Real.exp (-ConditionalPotential G β X i z)*q.density z
  let ν := fun (X : Configuration d N) (i : Fin N) => NormalizedTilt volume (fun z=>q.density z*Real.exp (-ConditionalPotential G β X i z))
  have hsquare (i : Fin N) :
      Integrable (fun X=>(Z X i)^2*variance (fun z=>f (Replacement X i z)) (ν X i)) P ∧
      (∫ X,(∫ z,Real.exp (-ConditionalPotential G β X i z)*(f (Replacement X i z)-f X)*q.density z)^2 ∂P) =
        ∫ X,(Z X i)^2*variance (fun z=>f (Replacement X i z)) (ν X i) ∂P :=
    boundedConditional_square_integral d N hN l u β q hβ G hG hGi hGn hGe i f hf C hC0 hC
  have hsum : (∑ i : Fin N, ∫ X,(∫ z,Real.exp (-ConditionalPotential G β X i z)*(f (Replacement X i z)-f X)*q.density z)^2 ∂P) =
      ∑ i : Fin N, ∫ X,(Z X i)^2*variance (fun z=>f (Replacement X i z)) (ν X i) ∂P := by
    apply Finset.sum_congr rfl
    intro i hi
    exact (hsquare i).2
  have hbalance := JumpConditionalBalance d N hN l u β q hβ G hG hGi hGn hGe
  have he : -(∫ X,f X*JumpOperator G q.density β f X ∂P) =
      ∑ i : Fin N, ∫ X,Z X i*variance (fun z=>f (Replacement X i z)) (ν X i) ∂P :=
    (hbalance.2.2 f hf ⟨C,hC⟩).2.1
  let k : ℝ := Real.exp (-β*u*(∫ x,G x))
  have hk : 0 < k := Real.exp_pos _
  have hrow (i : Fin N) : k*(∫ X,Z X i*variance (fun z=>f (Replacement X i z)) (ν X i) ∂P) ≤
      ∫ X,(Z X i)^2*variance (fun z=>f (Replacement X i z)) (ν X i) ∂P := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall fun X => mul_nonneg hk.le
        (mul_nonneg (hk.le.trans (hbalance.2.1 X i).1) (variance_nonneg _ _))
    · exact (hsquare i).1
    · apply Filter.Eventually.of_forall
      intro X
      have hz : 0 ≤ Z X i := hk.le.trans (hbalance.2.1 X i).1
      have hv := variance_nonneg (fun z=>f (Replacement X i z)) (ν X i)
      have hlo : k ≤ Z X i := (hbalance.2.1 X i).1
      simpa only [pow_two,mul_assoc] using mul_le_mul_of_nonneg_right hlo (mul_nonneg hz hv)
  refine ⟨hsum, ?_, ?_⟩
  · change k * (-(∫ X,f X*JumpOperator G q.density β f X ∂P)) ≤
      ∑ i : Fin N, ∫ X,(∫ z,Real.exp (-ConditionalPotential G β X i z)*(f (Replacement X i z)-f X)*q.density z)^2 ∂P
    rw [he,hsum,Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hrow i
  · intro i j hij
    classical
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
    let U := ConditionalPotential (N := N) G β
    let R : (Configuration d N × T) × T → ℝ := fun w =>
      Real.exp (-U w.1.1 i w.1.2 - U w.1.1 j w.2 - (β/N)*G (w.1.2-w.2))*q.density w.1.2*q.density w.2
    let Si : (Configuration d N × T) × T → (Configuration d N × T) × T := fun w => ((Replacement w.1.1 i w.1.2,w.1.1 i),w.2)
    let Sj : (Configuration d N × T) × T → (Configuration d N × T) × T := fun w => ((Replacement w.1.1 j w.2,w.1.2),w.1.1 j)
    have hSim : Measurable Si := ((ReplacementHaarSwap d N i).1.measurable.comp measurable_fst).prodMk measurable_snd
    have hRip : Measurable (fun w : (Configuration d N × T) × T => Replacement w.1.1 i w.1.2) :=
      measurable_fst.comp ((ReplacementHaarSwap d N i).1.measurable.comp measurable_fst)
    have hRjp : Measurable (fun w : (Configuration d N × T) × T => Replacement w.1.1 j w.2) :=
      measurable_fst.comp ((ReplacementHaarSwap d N j).1.measurable.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
    have hSjm : Measurable Sj := (hRjp.prodMk (measurable_snd.comp measurable_fst)).prodMk ((measurable_pi_apply j).comp (measurable_fst.comp measurable_fst))
    let H : (Configuration d N × T) × T → ℝ := fun w =>
      (f (Replacement w.1.1 i w.1.2)-f w.1.1)*(f (Replacement w.1.1 j w.2)-f w.1.1)
    have hHm : Measurable H := ((hf.comp hRip).sub (hf.comp (measurable_fst.comp measurable_fst))).mul ((hf.comp hRjp).sub (hf.comp (measurable_fst.comp measurable_fst)))
    have hC0 : 0 ≤ C := (abs_nonneg (f 0)).trans (hC 0)
    let B := (2*C)*(2*C)
    have hHb : ∀ w, |H w| ≤ B := by
      intro w
      have hi : |f (Replacement w.1.1 i w.1.2)-f w.1.1| ≤ 2*C := (abs_sub _ _).trans (by linarith [hC (Replacement w.1.1 i w.1.2), hC w.1.1])
      have hj : |f (Replacement w.1.1 j w.2)-f w.1.1| ≤ 2*C := (abs_sub _ _).trans (by linarith [hC (Replacement w.1.1 j w.2), hC w.1.1])
      dsimp only [H,B]
      rw [abs_mul]
      exact mul_le_mul hi hj (abs_nonneg _) (by linarith)
    let I := fun K : (Configuration d N × T) × T → ℝ => ∫ X, ∫ z, ∫ v, R ((X,z),v)*K ((X,z),v) ∂m ∂m ∂P
    let J := fun K : (Configuration d N × T) × T → ℝ => ∫ w, R w*K w ∂μ
    have hget : ∀ K : (Configuration d N × T) × T → ℝ, Measurable K → (∀ w, |K w| ≤ B) →
        MeasureTheory.Integrable (fun w => R w*K w) μ ∧ I K = I (K ∘ Si) ∧ I K = I (K ∘ Sj) := by
      intro K hKm hKb
      have hx := ReplacementRectangleExchange d N hN l u β q hβ G hG hGi hGn hGe i j hij K hKm ⟨B,hKb⟩
      exact ⟨hx.1,hx.2.2.1,hx.2.2.2⟩
    let H1 := H ∘ Si
    let H2 := H ∘ Sj
    let H3 := H1 ∘ Sj
    have hm1 : Measurable H1 := hHm.comp hSim
    have hm2 : Measurable H2 := hHm.comp hSjm
    have hm3 : Measurable H3 := hm1.comp hSjm
    have hb1 : ∀ w, |H1 w| ≤ B := fun w => hHb (Si w)
    have hb2 : ∀ w, |H2 w| ≤ B := fun w => hHb (Sj w)
    have hb3 : ∀ w, |H3 w| ≤ B := fun w => hb1 (Sj w)
    have hi0 := (hget H hHm hHb).1
    have hi1 := (hget H1 hm1 hb1).1
    have hi2 := (hget H2 hm2 hb2).1
    have hi3 := (hget H3 hm3 hb3).1
    have hIJ : ∀ K : (Configuration d N × T) × T → ℝ, MeasureTheory.Integrable (fun w => R w*K w) μ → I K = J K := by
      intro K hKi
      dsimp only [I,J]
      calc
        _ = ∫ w, ∫ v, R (w,v)*K (w,v) ∂m ∂P.prod m := MeasureTheory.integral_integral hKi.integral_prod_left
        _ = _ := MeasureTheory.integral_integral hKi
    have h01 : J H = J H1 := by rw [← hIJ H hi0, ← hIJ H1 hi1]; exact (hget H hHm hHb).2.1
    have h02 : J H = J H2 := by rw [← hIJ H hi0, ← hIJ H2 hi2]; exact (hget H hHm hHb).2.2
    have h03 : J H = J H3 := by
      rw [← hIJ H hi0, ← hIJ H3 hi3]
      exact ((hget H hHm hHb).2.1).trans ((hget H1 hm1 hb1).2.2)
    have hinv (X : Configuration d N) (k : Fin N) (z : T) : Replacement (Replacement X k z) k (X k) = X := by
      simp only [Replacement,Function.update_idem,Function.update_eq_self]
    have hcomm (X : Configuration d N) (z v : T) : Replacement (Replacement X i z) j v = Replacement (Replacement X j v) i z :=
      by
        change Function.update (Function.update X i z) j v = Function.update (Function.update X j v) i z
        exact Function.update_comm hij z v X
    let Q : (Configuration d N × T) × T → ℝ := fun w =>
      (f w.1.1-f (Replacement w.1.1 i w.1.2)-f (Replacement w.1.1 j w.2)+f (Replacement (Replacement w.1.1 i w.1.2) j w.2))^2
    have hbackj (X : Configuration d N) (z v : T) :
        Replacement (Replacement (Replacement X i z) j v) j (X j) = Replacement X i z := by
      unfold Replacement
      rw [Function.update_idem]
      have hjold : Function.update X i z j = X j := Function.update_of_ne hij.symm _ _
      rw [← hjold,Function.update_eq_self]
    have h1val (w : (Configuration d N × T) × T) : H1 w =
        (f w.1.1-f (Replacement w.1.1 i w.1.2)) *
          (f (Replacement (Replacement w.1.1 i w.1.2) j w.2)-f (Replacement w.1.1 i w.1.2)) := by
      dsimp only [H1,H,Si,Function.comp_def]
      rw [hinv]
    have h2val (w : (Configuration d N × T) × T) : H2 w =
        (f (Replacement (Replacement w.1.1 i w.1.2) j w.2)-f (Replacement w.1.1 j w.2)) *
          (f w.1.1-f (Replacement w.1.1 j w.2)) := by
      dsimp only [H2,H,Sj,Function.comp_def]
      rw [hinv,← hcomm]
    have h3val (w : (Configuration d N × T) × T) : H3 w =
        (f (Replacement w.1.1 j w.2)-f (Replacement (Replacement w.1.1 i w.1.2) j w.2)) *
          (f (Replacement w.1.1 i w.1.2)-f (Replacement (Replacement w.1.1 i w.1.2) j w.2)) := by
      change H1 (Sj w) = _
      rw [h1val]
      dsimp only [Sj]
      rw [← hcomm]
      simp only [Replacement,Function.update_of_ne hij.symm]
      change (f (Replacement w.1.1 j w.2)-f (Replacement (Replacement w.1.1 i w.1.2) j w.2)) *
        (f (Replacement (Replacement (Replacement w.1.1 i w.1.2) j w.2) j (w.1.1 j))-f (Replacement (Replacement w.1.1 i w.1.2) j w.2)) = _
      rw [hbackj]
      rfl
    have hpoly : ∀ w, H w+H1 w+H2 w+H3 w = Q w := by
      intro w
      rw [h1val,h2val,h3val]
      dsimp only [H,Q]
      ring
    have hsum : J H+J H1+J H2+J H3 = J Q := by
      have ht := MeasureTheory.integral_add hi0 hi1
      have htr := MeasureTheory.integral_add (hi0.add hi1) hi2
      have hall := MeasureTheory.integral_add ((hi0.add hi1).add hi2) hi3
      simp only [Pi.add_apply] at ht htr hall
      rw [htr,ht] at hall
      dsimp only [J]
      rw [← hall]
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun w => by dsimp only; rw [← hpoly]; ring
    have hQint : MeasureTheory.Integrable (fun w => R w*Q w) μ := by
      apply (((hi0.add hi1).add hi2).add hi3).congr
      exact Filter.Eventually.of_forall fun w => by simp only [Pi.add_apply]; rw [← hpoly]; ring
    have heq : J H = (1/4:ℝ)*J Q := by linarith [hsum]
    have hnonneg : 0 ≤ J Q := by
      have hqz : ∀ᵐ w ∂μ, l ≤ q.density w.1.2 ∧ q.density w.1.2 ≤ u :=
        ((MeasureTheory.measurePreserving_snd (μ := P) (ν := m)).comp (MeasureTheory.measurePreserving_fst (μ := P.prod m) (ν := m))).quasiMeasurePreserving.tendsto_ae q.bounds
      have hqv : ∀ᵐ w ∂μ, l ≤ q.density w.2 ∧ q.density w.2 ≤ u :=
        (MeasureTheory.measurePreserving_snd (μ := P.prod m) (ν := m)).quasiMeasurePreserving.tendsto_ae q.bounds
      apply MeasureTheory.integral_nonneg_of_ae
      filter_upwards [hqz,hqv] with w hz hv
      exact mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (q.lower_pos.le.trans hz.1)) (q.lower_pos.le.trans hv.1)) (sq_nonneg _)
    have hIeq : I H = (1/4:ℝ)*I Q := by rw [hIJ H hi0,hIJ Q hQint]; exact heq
    have hIn : 0 ≤ I H := by rw [hIeq,hIJ Q hQint]; positivity
    change (∫ X, (∫ z, ∫ v, R ((X,z),v) * (f (Replacement X i z)-f X) * (f (Replacement X j v)-f X)) ∂P) = (1/4:ℝ)*I Q ∧
      0 ≤ (∫ X, (∫ z, ∫ v, R ((X,z),v) * (f (Replacement X i z)-f X) * (f (Replacement X j v)-f X)) ∂P)
    have hmain : (∫ X, (∫ z, ∫ v, R ((X,z),v) * (f (Replacement X i z)-f X) * (f (Replacement X j v)-f X)) ∂P) = I H := by
      dsimp only [I,H]
      congr 1
      funext X
      congr 1
      funext z
      congr 1
      funext v
      ring
    rw [hmain]
    exact ⟨hIeq,hIn⟩
