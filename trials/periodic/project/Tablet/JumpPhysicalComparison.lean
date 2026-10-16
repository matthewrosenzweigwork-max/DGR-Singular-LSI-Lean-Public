module

public import Tablet.HolesPoincare
public import Tablet.JumpL2Extension
public import Tablet.ConfigurationCalculus
public import Tablet.ReplacementJointBalance
public import Tablet.RieszL1Foundation
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ContDiff
-- [TABLET NODE: JumpPhysicalComparison]
theorem JumpPhysicalComparison (d : ℕ) (hd : 2 ≤ d) (s a B : ℝ)
    (hs : 0 ≤ s) (hsd : s ≤ (d : ℝ) - 2) (ha : 0 < a) (hB : 0 ≤ B) :
    ∃ rate : ℝ, 0 < rate ∧ ∀ (N : ℕ), 2 ≤ N →
      ∀ (l u β ε c : ℝ) (q : BoundedBackground d l u),
      0 ≤ β → β ≤ B → 0 < ε → 0 ≤ c →
      (∀ x, -c ≤ RieszKernel d s a ε x) →
      ∀ (f : Configuration d N → ℝ), f ∈ SmoothCore d N →
        let G := fun x => RieszKernel d s a ε x + c
        let P := CanonicalLaw (N := N) G q.density β
        (-(∫ X, f X * JumpOperator G q.density β f X ∂P)) ≤
          (u / l) * rate⁻¹ * PhysicalEnergy P f := by
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

  have configurationLift_quotient (d N : ℕ) :
      IsOpenQuotientMap (ConfigurationLift d N) := by
    have hc : IsOpenQuotientMap ((↑) : ℝ → AddCircle (1 : ℝ)) :=
      QuotientAddGroup.isOpenQuotientMap_mk
    have hp : IsOpenQuotientMap
        (Pi.map (fun _ : Fin N × Fin d => ((↑) : ℝ → AddCircle (1 : ℝ)))) :=
      IsOpenQuotientMap.piMap (fun _ => hc)
    have he := (PiLp.homeomorph 2 (fun _ : Fin N × Fin d => ℝ)).isOpenQuotientMap
    have hh := (Homeomorph.piCurry (X := Fin N) (Y := Fin d)
      (Z := AddCircle (1 : ℝ))).isOpenQuotientMap
    exact hh.comp (hp.comp he)

  have lift_translation_eq {d N : ℕ} (y z : EuclideanSpace ℝ (Fin N × Fin d))
      (h : ConfigurationLift d N y = ConfigurationLift d N z)
      (x : EuclideanSpace ℝ (Fin N × Fin d)) :
      ConfigurationLift d N (x + (z-y)) = ConfigurationLift d N x := by
    funext i j
    have hj := congrFun (congrFun h i) j
    change (y (i,j) : AddCircle (1 : ℝ)) = (z (i,j) : AddCircle (1 : ℝ)) at hj
    simp only [ConfigurationLift, PiLp.add_apply, PiLp.sub_apply]
    rw [AddCircle.coe_add, AddCircle.coe_sub, ← hj, sub_self, add_zero]

  have lift_fderiv_eq {d N : ℕ} (f : Configuration d N → ℝ)
      (y z : EuclideanSpace ℝ (Fin N × Fin d))
      (h : ConfigurationLift d N y = ConfigurationLift d N z) :
      fderiv ℝ (fun x => f (ConfigurationLift d N x)) y =
        fderiv ℝ (fun x => f (ConfigurationLift d N x)) z := by
    let q := fun x => f (ConfigurationLift d N x)
    have hfun : (fun x => q (x+(z-y))) = q := by
      funext x
      exact congrArg f (lift_translation_eq y z h x)
    have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := q) (x := y) (z-y)
    rw [hfun] at hd
    simpa using hd

  have coordinateGradient_on_lift {d N : ℕ} (f : Configuration d N → ℝ)
      (y : EuclideanSpace ℝ (Fin N × Fin d)) (ij : Fin N × Fin d) :
      CoordinateGradient f (ConfigurationLift d N y) ij =
        fderiv ℝ (fun x => f (ConfigurationLift d N x)) y
          (EuclideanSpace.single ij 1) := by
    let z : EuclideanSpace ℝ (Fin N × Fin d) := WithLp.toLp 2
      (fun ij => (AddCircle.equivIco (1 : ℝ) 0 (ConfigurationLift d N y ij.1 ij.2) : ℝ))
    have hz : ConfigurationLift d N z = ConfigurationLift d N y := by
      funext i j
      simp [ConfigurationLift, z, AddCircle.coe_equivIco]
    change fderiv ℝ (fun x => f (ConfigurationLift d N x)) z (EuclideanSpace.single ij 1) = _
    rw [lift_fderiv_eq f z y hz]

  have coordinateGradient_continuous {d N : ℕ} {f : Configuration d N → ℝ}
      (hf : f ∈ SmoothCore d N) : Continuous (CoordinateGradient f) := by
    apply (configurationLift_quotient d N).continuous_comp_iff.mp
    have hF : ContDiff ℝ ∞ (fun y => f (ConfigurationLift d N y)) := hf
    have he : (fun y => CoordinateGradient f (ConfigurationLift d N y)) =
        (fun y : EuclideanSpace ℝ (Fin N × Fin d) =>
          WithLp.toLp 2 (fun ij => fderiv ℝ (fun x => f (ConfigurationLift d N x)) y
            (EuclideanSpace.single ij 1))) := by
      funext y
      ext ij
      exact coordinateGradient_on_lift f y ij
    change Continuous (fun y => CoordinateGradient f (ConfigurationLift d N y))
    rw [he]
    apply (PiLp.continuous_toLp 2 (fun _ : Fin N × Fin d => ℝ)).comp
    apply continuous_pi
    intro ij
    exact (hF.continuous_fderiv_apply (by simp)).comp
      (continuous_id.prodMk continuous_const)

  have rowEnergy_continuous {d N : ℕ} {f : Configuration d N → ℝ}
      (hf : f ∈ SmoothCore d N) (i : Fin N) :
      Continuous (fun X => ∑ j : Fin d, (CoordinateGradient f X (i,j))^2) := by
    apply continuous_finset_sum
    intro j _
    exact ((PiLp.continuous_apply 2 (fun _ : Fin N × Fin d => ℝ) (i,j)).comp
      (coordinateGradient_continuous hf)).pow 2

  have rowEnergy_le_total {d N : ℕ} (f : Configuration d N → ℝ) (X : Configuration d N)
      (i : Fin N) : (∑ j : Fin d, (CoordinateGradient f X (i,j))^2) ≤ ‖CoordinateGradient f X‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
    apply Finset.single_le_sum (f := fun k : Fin N => ∑ j : Fin d, (CoordinateGradient f X (k,j))^2)
    · intro k _
      exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
    · exact Finset.mem_univ i

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

  have conditionalPotential_joint_measurable {d N : ℕ} (G : UnitAddTorus (Fin d) → ℝ)
      (hG : Measurable G) (β : ℝ) (i : Fin N) :
      Measurable (fun p : Configuration d N × UnitAddTorus (Fin d) =>
        ConditionalPotential G β p.1 i p.2) := by
    unfold ConditionalPotential
    apply Measurable.const_mul
    apply Finset.measurable_fun_sum
    intro j _
    by_cases hij : j=i
    · simp only [hij,↓reduceIte]
      exact measurable_const
    · simp only [hij,↓reduceIte]
      exact hG.comp (measurable_snd.sub ((measurable_pi_apply j).comp measurable_fst))

  have conditionalEnergy_integrable {d N : ℕ} (hN : 2≤N) (l u β : ℝ)
      (q : BoundedBackground d l u) (hβ : 0≤β) (G : UnitAddTorus (Fin d) → ℝ)
      (hG : Measurable G) (hGi : Integrable G volume) (hGn : ∀x,0≤G x)
      (P : Measure (Configuration d N)) [IsFiniteMeasure P] (i : Fin N)
      (H : Configuration d N × UnitAddTorus (Fin d) → ℝ) (hH : Measurable H)
      (C : ℝ) (hHb : ∀p,0≤H p ∧ H p≤C) :
      Integrable (fun X => ∫z, Real.exp (-ConditionalPotential G β X i z) * q.density z * H (X,z)) P := by
    have hraw : Measurable (fun p : Configuration d N × UnitAddTorus (Fin d) =>
        Real.exp (-ConditionalPotential G β p.1 i p.2) * q.density p.2 * H p) :=
      ((conditionalPotential_joint_measurable G hG β i).neg.exp.mul
        (q.measurable.comp measurable_snd)).mul hH
    have hm : Measurable (fun X => ∫z, Real.exp (-ConditionalPotential G β X i z) * q.density z * H (X,z)) :=
      hraw.stronglyMeasurable.integral_prod_right'.measurable
    have hqint : Integrable q.density volume := integrable_of_integral_eq_one q.mass
    have hqpos : ∀ᵐ z ∂volume, 0≤q.density z :=
      q.bounds.mono (fun _ h => q.lower_pos.le.trans h.1)
    have hb (X : Configuration d N) :
        0≤(∫z, Real.exp (-ConditionalPotential G β X i z) * q.density z * H (X,z)) ∧
        (∫z, Real.exp (-ConditionalPotential G β X i z) * q.density z * H (X,z)) ≤ C := by
      have hUpos := (conditionalNormalizer_bounds d N hN l u β q hβ G hG hGi hGn X i).2.2.1
      have hrawpos : ∀ᵐ z ∂volume, 0≤Real.exp (-ConditionalPotential G β X i z) * q.density z * H (X,z) :=
        hqpos.mono (fun z hz => mul_nonneg (mul_nonneg (Real.exp_nonneg _) hz) (hHb _).1)
      refine ⟨integral_nonneg_of_ae hrawpos,?_⟩
      calc
        _ ≤ ∫z, C*q.density z := integral_mono_of_nonneg hrawpos (hqint.const_mul C) (by
          filter_upwards [hqpos] with z hz
          have he : Real.exp (-ConditionalPotential G β X i z) ≤ 1 :=
            Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hUpos z))
          calc
            _ ≤ q.density z * H (X,z) := by
              simpa only [one_mul] using mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right he hz) (hHb _).1
            _ ≤ q.density z * C := mul_le_mul_of_nonneg_left (hHb _).2 hz
            _ = C*q.density z := mul_comm _ _)
        _ = C := by rw [integral_const_mul,q.mass,mul_one]
    apply (integrable_const C).mono' hm.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun X => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hb X).1] using (hb X).2)

  have conditional_weighted_integral {d N : ℕ} (hN : 2≤N) (l u β : ℝ)
      (q : BoundedBackground d l u) (hβ : 0≤β) (G : UnitAddTorus (Fin d) → ℝ)
      (hG : Measurable G) (hGi : Integrable G volume) (hGn : ∀x,0≤G x)
      (X : Configuration d N) (i : Fin N) (h : UnitAddTorus (Fin d) → ℝ)
      (hm : Measurable h) (C : ℝ) (hb : ∀z,0≤h z ∧ h z≤C) :
      (∫z,Real.exp (-ConditionalPotential G β X i z)*q.density z) *
        (∫z,h z ∂NormalizedTilt volume (fun z=>q.density z*Real.exp (-ConditionalPotential G β X i z))) =
        ∫z,Real.exp (-ConditionalPotential G β X i z)*q.density z*h z := by
    let U := ConditionalPotential G β X i
    let w := fun z=>q.density z*Real.exp (-U z)
    let Z := ∫z,w z
    have hnm := conditionalNormalizer_bounds d N hN l u β q hβ G hG hGi hGn X i
    have hU : Measurable U := hnm.1
    have hwm : Measurable w := q.measurable.mul hU.neg.exp
    have hqp : ∀ᵐz∂volume,0≤q.density z := q.bounds.mono (fun z h=>q.lower_pos.le.trans h.1)
    have hwp : ∀ᵐz∂volume,0≤w z := hqp.mono (fun z h=>mul_nonneg h (Real.exp_nonneg _))
    have hwi : Integrable w volume := by simpa only [w,U,mul_comm] using hnm.2.2.2.2.1
    have hwb : ∀ᵐz∂volume,‖w z‖≤u := by
      filter_upwards [q.bounds,hqp] with z hz hp
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hp (Real.exp_nonneg _))]
      exact (mul_le_mul_of_nonneg_left
        (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hnm.2.2.1 z))) hp).trans (by simpa using hz.2)
    have hi : Integrable h volume := (integrable_const C).mono' hm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z=>by
        simpa only [Real.norm_eq_abs,abs_of_nonneg (hb z).1] using (hb z).2))
    have hmul := hi.mul_bdd hwm.aestronglyMeasurable hwb
    have hz : 0<Z := by
      have ht := (Real.exp_pos _).trans_le hnm.2.2.2.2.2.1
      simpa only [Z,w,U,mul_comm] using ht
    have ht := (TiltNormalization volume w hwm hwp hwi hz).2 h hm hmul
    have hz' : (∫z,Real.exp (-U z)*q.density z)=Z := by dsimp [Z,w];congr 1;funext z;ring
    change (∫z,Real.exp (-U z)*q.density z)*(∫z,h z ∂NormalizedTilt volume w)=_
    rw [hz',ht.2,mul_div_cancel₀ _ (ne_of_gt hz)]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun z=>by dsimp [w,U];ring))

  have tilt_scale {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (w : Ω → ℝ)
      (t : ℝ) (ht : t ≠ 0) : NormalizedTilt μ (fun x => t*w x) = NormalizedTilt μ w := by
    unfold NormalizedTilt
    simp only [integral_const_mul]
    congr 1
    funext x
    congr 1
    exact mul_div_mul_left _ _ ht

  have conditional_atomic (d N : ℕ) (G : UnitAddTorus (Fin d) → ℝ)
      (β c : ℝ) (X : Configuration d N) (i : Fin N) :
      ConditionalPotential (fun x => G x+c) β X i =
        fun z => AtomicPotential G (fun j => if j=i then 0 else β/(N:ℝ)) X z +
          (∑ j : Fin N, if j=i then 0 else β/(N:ℝ))*c := by
    funext z
    unfold ConditionalPotential AtomicPotential
    have he (j : Fin N) :
        (if j=i then (0:ℝ) else G (z-X j)+c) =
        (if j=i then 0 else G (z-X j)) + (if j=i then 0 else c) := by
      by_cases h : j=i <;> simp [h]
    simp_rw [he,Finset.sum_add_distrib, mul_add,Finset.mul_sum,Finset.sum_mul]
    congr 1
    · apply Finset.sum_congr rfl
      intro j _
      by_cases h : j=i <;> simp [h]
    · apply Finset.sum_congr rfl
      intro j _
      by_cases h : j=i <;> simp [h]

  have conditional_tilt_atomic (d N : ℕ) (G q : UnitAddTorus (Fin d) → ℝ)
      (β c : ℝ) (X : Configuration d N) (i : Fin N) :
      NormalizedTilt volume (fun z => q z * Real.exp (-ConditionalPotential (fun x => G x+c) β X i z)) =
      NormalizedTilt volume (fun z => q z * Real.exp
        (-AtomicPotential G (fun j => if j=i then 0 else β/(N:ℝ)) X z)) := by
    rw [conditional_atomic]
    let C := (∑ j : Fin N, if j=i then (0:ℝ) else β/(N:ℝ))*c
    have he : (fun z => q z * Real.exp (-(AtomicPotential G
        (fun j => if j=i then 0 else β/(N:ℝ)) X z + C))) =
        fun z => Real.exp (-C) * (q z * Real.exp (-AtomicPotential G
          (fun j => if j=i then 0 else β/(N:ℝ)) X z)) := by
      funext z
      rw [neg_add, Real.exp_add]
      ring
    change NormalizedTilt volume (fun z => q z * Real.exp (-(AtomicPotential G
        (fun j => if j=i then 0 else β/(N:ℝ)) X z + C))) = _
    rw [he]
    exact tilt_scale _ _ _ (ne_of_gt (Real.exp_pos _))

  have atomic_mass (N : ℕ) (hN : 2≤N) (β : ℝ) (hβ : 0≤β) (i : Fin N) :
      (∀ j : Fin N, 0≤(if j=i then (0:ℝ) else β/(N:ℝ))) ∧
      (∑ j : Fin N, if j=i then (0:ℝ) else β/(N:ℝ)) ≤ β := by
    have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
    constructor
    · intro j
      split_ifs
      · exact le_rfl
      · exact div_nonneg hβ hNp.le
    · have he (j : Fin N) : (if j=i then (0:ℝ) else β/(N:ℝ)) =
          β/(N:ℝ) - (if j=i then β/(N:ℝ) else 0) := by
        by_cases h : j=i <;> simp [h]
      simp_rw [he]
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [mul_div_cancel₀ _ (ne_of_gt hNp)]
      exact sub_le_self _ (div_nonneg hβ hNp.le)

  have holes_fiber_bound (d : ℕ) (hd : 2≤d) (s a B : ℝ)
      (hs : 0≤s) (hsd : s≤(d:ℝ)-2) (ha : 0<a) (hB : 0≤B) :
      ∃ rate : ℝ, 0<rate ∧ ∀ N : ℕ, 2≤N → ∀ (l u β ε c : ℝ)
        (q : BoundedBackground d l u), 0≤β → β≤B → 0<ε →
        ∀ f : Configuration d N → ℝ, f ∈ SmoothCore d N →
        ∀ (X : Configuration d N) (i : Fin N),
        let ν := NormalizedTilt volume (fun z => q.density z * Real.exp
          (-ConditionalPotential (fun x => RieszKernel d s a ε x+c) β X i z))
        ProbabilityTheory.variance (fun z => f (Replacement X i z)) ν ≤
          (u/l)*rate⁻¹ * (∫ z, ∑ j : Fin d,
            (CoordinateGradient f (Replacement X i z) (i,j))^2 ∂ν) := by
    obtain ⟨rate,hr,hh⟩ := HolesPoincare d hd s a B hs hsd ha hB
    refine ⟨rate,hr,?_⟩
    intro N hN l u β ε c q hβ hβB hε f hf X i
    have hw := atomic_mass N hN β hβ i
    have hp := (hh N (fun j => if j=i then 0 else β/(N:ℝ)) X hw.1
      (hw.2.trans hβB) ε hε).2 q.density l u q.measurable q.lower_pos q.bounds
    obtain ⟨hfs, hfg⟩ := ((ConfigurationCalculus d N).2.2.2 f hf).2.2.2.2.2.2.1 X i
    have h := hp (fun z => f (Replacement X i z)) hfs
    rw [← conditional_tilt_atomic d N (RieszKernel d s a ε) q.density β c X i] at h
    simpa only [hfg] using h

  have weighted_row_exchange (d N : ℕ) (hN : 2≤N) (l u β : ℝ)
      (q : BoundedBackground d l u) (hβ : 0≤β)
      (G : UnitAddTorus (Fin d) → ℝ) (hG : Measurable G) (hGi : Integrable G volume)
      (hGn : ∀x,0≤G x) (hGe : ∀x,G (-x)=G x) (i : Fin N)
      (h : Configuration d N → ℝ) (hm : Measurable h) (hb : ∃C:ℝ,∀X,|h X|≤C) :
      (∫X, (∫z,Real.exp (-ConditionalPotential G β X i z)*q.density z*h (Replacement X i z))
        ∂CanonicalLaw (N:=N) G q.density β) =
      ∫X,(∫z,Real.exp (-ConditionalPotential G β X i z)*q.density z)*h X
        ∂CanonicalLaw (N:=N) G q.density β := by
    classical
    let H := fun p : Configuration d N × UnitAddTorus (Fin d) => h (Replacement p.1 i p.2)
    have hHm : Measurable H := by
      apply hm.comp
      apply measurable_pi_lambda
      intro j
      by_cases hji : j=i
      · subst j
        simpa [Replacement] using (measurable_snd : Measurable (Prod.snd : Configuration d N × UnitAddTorus (Fin d) → _))
      · simpa [Replacement,hji,Function.comp_def] using (measurable_pi_apply j).comp
          (measurable_fst : Measurable (Prod.fst : Configuration d N × UnitAddTorus (Fin d) → _))
    obtain ⟨C,hC⟩ := hb
    have hHb : ∃C:ℝ,∀p,|H p|≤C := ⟨C,fun p=>hC _⟩
    have he := (joint_test_exchange d N hN l u β q hβ G hG hGi hGn hGe i H hHm hHb).2
    have hrep (X : Configuration d N) (z : UnitAddTorus (Fin d)) :
        Replacement (Replacement X i z) i (X i)=X := by
      funext j
      by_cases hji : j=i
      · subst j; simp [Replacement]
      · simp [Replacement,hji,Function.comp_def]
    change (∫X,(∫z,Real.exp (-ConditionalPotential G β X i z)*q.density z*H (X,z))
      ∂CanonicalLaw (N:=N) G q.density β)=_
    rw [he]
    simp only [H,hrep,integral_mul_const]

  have hexchange := weighted_row_exchange
  obtain ⟨rate,hr,hpi⟩ := holes_fiber_bound d hd s a B hs hsd ha hB
  refine ⟨rate,hr,?_⟩
  intro N hN l u β ε c q hβ hβB hε hc hlower f hf
  let G := fun x => RieszKernel d s a ε x+c
  let P := CanonicalLaw (N:=N) G q.density β
  let Z := fun (X : Configuration d N) (i : Fin N) =>
    ∫z,Real.exp (-ConditionalPotential G β X i z)*q.density z
  let ν := fun (X : Configuration d N) (i : Fin N) =>
    NormalizedTilt volume (fun z=>q.density z*Real.exp (-ConditionalPotential G β X i z))
  let K := (u/l)*rate⁻¹
  let e := fun (i : Fin N) (X : Configuration d N) =>
    ∑j:Fin d,(CoordinateGradient f X (i,j))^2
  have hK : 0≤K := mul_nonneg (div_nonneg (zero_le_one.trans q.one_le_upper) q.lower_pos.le)
    (inv_nonneg.mpr hr.le)
  obtain ⟨_,_,hR⟩ := RieszL1Foundation d hd s a hs (by linarith) ha
  obtain ⟨hRm,hRi,_,hRe,_⟩ := hR ε hε.le
  have hGm : Measurable G := hRm.add measurable_const
  have hGi : Integrable G volume := hRi.add (integrable_const c)
  have hGn : ∀x,0≤G x := fun x=>by dsimp [G]; linarith [hlower x]
  have hGe : ∀x,G (-x)=G x := fun x=>by dsimp [G];rw[hRe]
  obtain ⟨hP,hZ,hBalance⟩ := JumpConditionalBalance d N hN l u β q hβ G hGm hGi hGn hGe
  haveI : IsProbabilityMeasure P := hP
  obtain ⟨hflat,hfm,hfb,hegm,⟨C,hCb⟩,hgrad,hfiber,hfull⟩ :=
    (ConfigurationCalculus d N).2.2.2 f hf
  have hepos (i : Fin N) (X : Configuration d N) : 0≤e i X :=
    Finset.sum_nonneg (fun j _=>sq_nonneg _)
  have heb (i : Fin N) (X : Configuration d N) : e i X≤C :=
    (rowEnergy_le_total f X i).trans (hCb X)
  have hem (i : Fin N) : Measurable (e i) := (rowEnergy_continuous hf i).measurable
  have hei (i : Fin N) : Integrable (e i) P :=
    (integrable_const C).mono' (hem i).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun X=>by
        simpa only [Real.norm_eq_abs,abs_of_nonneg (hepos i X)] using heb i X))
  have herepl (i : Fin N) : Measurable (fun p : Configuration d N × UnitAddTorus (Fin d) =>
      e i (Replacement p.1 i p.2)) := by
    apply (hem i).comp
    apply measurable_pi_lambda
    intro j
    by_cases hji : j=i
    · subst j
      simpa [Replacement] using (measurable_snd : Measurable (Prod.snd : Configuration d N × UnitAddTorus (Fin d) → _))
    · simpa [Replacement,hji,Function.comp_def] using (measurable_pi_apply j).comp
        (measurable_fst : Measurable (Prod.fst : Configuration d N × UnitAddTorus (Fin d) → _))
  have hb := hBalance f hfm hfb
  change (-(∫X,f X*JumpOperator G q.density β f X ∂P)) ≤ K*PhysicalEnergy P f
  rw [hb.2.1]
  calc
    (∑i:Fin N,∫X,Z X i*variance (fun z=>f (Replacement X i z)) (ν X i) ∂P) ≤
        ∑i:Fin N,K*(∫X,e i X ∂P) := by
      apply Finset.sum_le_sum
      intro i _
      have hrI := conditionalEnergy_integrable hN l u β q hβ G hGm hGi hGn P i
        (fun p=>e i (Replacement p.1 i p.2)) (herepl i) C
        (fun p=>⟨hepos i _,heb i _⟩)
      have heSliceMeas (X : Configuration d N) :
          Measurable (fun z : UnitAddTorus (Fin d) => e i (Replacement X i z)) := by
        have hpair : Measurable (fun z : UnitAddTorus (Fin d) => (X,z)) :=
          measurable_const.prodMk measurable_id
        simpa only [Function.comp_def] using (herepl i).comp hpair
      have hEq (X : Configuration d N) : Z X i * (∫z,e i (Replacement X i z) ∂ν X i) =
          ∫z,Real.exp (-ConditionalPotential G β X i z)*q.density z*e i (Replacement X i z) := by
        exact conditional_weighted_integral hN l u β q hβ G hGm hGi hGn X i
          (fun z=>e i (Replacement X i z))
          (heSliceMeas X) C
          (fun z=>⟨hepos i _,heb i _⟩)
      have hPI (X : Configuration d N) :
          Z X i*variance (fun z=>f (Replacement X i z)) (ν X i) ≤
          K*(∫z,Real.exp (-ConditionalPotential G β X i z)*q.density z*e i (Replacement X i z)) := by
        have hp := hpi N hN l u β ε c q hβ hβB hε f hf X i
        have hZnn : 0≤Z X i := (Real.exp_pos _).le.trans (hZ X i).1
        calc
          _ ≤ Z X i*(K*(∫z,e i (Replacement X i z) ∂ν X i)) :=
            mul_le_mul_of_nonneg_left hp hZnn
          _ = K*(Z X i*(∫z,e i (Replacement X i z) ∂ν X i)) := by ring
          _ = _ := by rw [hEq]
      calc
        _ ≤ ∫X,K*(∫z,Real.exp (-ConditionalPotential G β X i z)*q.density z*e i (Replacement X i z)) ∂P :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall (fun X=>
            mul_nonneg ((Real.exp_pos _).le.trans (hZ X i).1) (variance_nonneg _ _)))
            (hrI.const_mul K) (Filter.Eventually.of_forall hPI)
        _ = K*(∫X,Z X i*e i X ∂P) := by
          rw [integral_const_mul,hexchange d N hN l u β q hβ G hGm hGi hGn hGe i (e i) (hem i)
            ⟨C,fun X=>by rw[abs_of_nonneg (hepos i X)]; exact heb i X⟩]
        _ ≤ K*(∫X,e i X ∂P) := mul_le_mul_of_nonneg_left
          (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun X=>
            mul_nonneg ((Real.exp_pos _).le.trans (hZ X i).1) (hepos i X)))
            (hei i) (Filter.Eventually.of_forall (fun X=>
              mul_le_of_le_one_left (hepos i X) (hZ X i).2.1))) hK
    _ = K*PhysicalEnergy P f := by
      unfold PhysicalEnergy
      simp_rw [hfull]
      rw [integral_finsetSum _ (fun i _=>hei i),Finset.mul_sum]
