module

public import Tablet.ConfigurationPairPotential
public import Tablet.CompactWeightedPoincare
public import Tablet.RieszHeatSource
public import Tablet.BoundedDensityComparison
public import Tablet.GibbsNormalizerBounds
public import Tablet.RieszLocalStructure
public import Tablet.RieszL1Foundation
public import Tablet.ProductBackgroundFacts
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ContDiff
-- [TABLET NODE: FiniteParticlePoincare]
theorem FiniteParticlePoincare (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N)
    (s a B l u : ℝ) (hs : 0 ≤ s) (hsd : s ≤ (d : ℝ) - 2)
    (ha : 0 < a) (hB : 0 ≤ B) (hl : 0 < l) (hl1 : l ≤ 1) (hu : 1 ≤ u) :
    ∃ rate : ℝ, 0 < rate ∧ ∀ (β ε : ℝ), 0 ≤ β → β ≤ B → 0 < ε →
      ∀ (q : BoundedBackground d l u) (f : Configuration d N → ℝ),
      f ∈ SmoothCore d N →
        ProbabilityTheory.variance f
          (CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β) ≤
        rate⁻¹ * PhysicalEnergy
          (CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β) f := by
-- BODY
  classical
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

  have tilt_map {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
      (μ : Measure A) (ν : Measure B) (e : A ≃ᵐ B)
      (hp : MeasurePreserving e μ ν) (w : A → ℝ) (hw : Measurable w) :
      (NormalizedTilt μ w).map e = NormalizedTilt ν (fun y=>w (e.symm y)) := by
    have hd : (∫y,w (e.symm y) ∂ν)=(∫x,w x ∂μ) := by
      rw [←hp.integral_comp e.measurableEmbedding (fun y=>w (e.symm y))]
      simp
    unfold NormalizedTilt
    rw [hd]
    apply Measure.ext
    intro S hS
    rw [Measure.map_apply e.measurable hS,withDensity_apply _ (e.measurable hS),
      withDensity_apply _ hS]
    have hm : Measurable (fun y=>ENNReal.ofReal (w (e.symm y)/(∫x,w x ∂μ))) :=
      ((hw.comp e.symm.measurable).div_const _).ennreal_ofReal
    have h := (hp.restrict_preimage hS).lintegral_comp hm
    simpa only [MeasurableEquiv.symm_apply_apply] using h

  have flatten_pi (d N : ℕ) (V f : Configuration d N → ℝ)
      (hV : V ∈ SmoothCore d N) (hf : f ∈ SmoothCore d N) (r : ℝ)
      (hpi : ∀g : UnitAddTorus (Fin (N*d)) → ℝ, TorusSmooth g →
        variance g (NormalizedTilt volume (fun x=>Real.exp (-V ((ConfigurationFlatten d N).symm x)))) ≤
        r⁻¹*(∫x,‖TorusGradient g x‖^2
          ∂NormalizedTilt volume (fun x=>Real.exp (-V ((ConfigurationFlatten d N).symm x))))) :
      variance f (NormalizedTilt volume (fun X=>Real.exp (-V X))) ≤
        r⁻¹*(∫X,‖CoordinateGradient f X‖^2
          ∂NormalizedTilt volume (fun X=>Real.exp (-V X))) := by
    let e : Configuration d N ≃ᵐ UnitAddTorus (Fin (N*d)) :=
      {toEquiv := ConfigurationFlatten d N
       measurable_toFun := (ConfigurationCalculus d N).1
       measurable_invFun := (ConfigurationCalculus d N).2.1}
    let μ := NormalizedTilt volume (fun X=>Real.exp (-V X))
    let ν := NormalizedTilt volume (fun x=>Real.exp (-V (e.symm x)))
    let F := fun x=>f (e.symm x)
    have hp : MeasurePreserving e volume volume :=
      ⟨(ConfigurationCalculus d N).1,(ConfigurationCalculus d N).2.2.1⟩
    have ht : μ.map e=ν := tilt_map _ _ e hp
      (fun X=>Real.exp (-V X)) (((ConfigurationCalculus d N).2.2.2 V hV).2.1.neg.exp)
    have hv : variance F ν=variance f μ := by
      rw [←ht,variance_map_equiv]
      congr 1
      funext X
      simp [F,Function.comp_def]
    have he : (∫x,‖TorusGradient F x‖^2 ∂ν)=(∫X,‖CoordinateGradient f X‖^2 ∂μ) := by
      rw [←ht,integral_map_equiv]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun X=>
        ((ConfigurationCalculus d N).2.2.2 f hf).2.2.2.2.2.1 X)
    have h := hpi F (((ConfigurationCalculus d N).2.2.2 f hf).1)
    change variance F ν ≤ r⁻¹*(∫x,‖TorusGradient F x‖^2 ∂ν) at h
    rw [hv,he] at h
    exact h

  have tilt_scale {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (w : Ω → ℝ)
      (t : ℝ) (ht : t ≠ 0) : NormalizedTilt μ (fun x => t*w x) = NormalizedTilt μ w := by
    unfold NormalizedTilt
    simp only [integral_const_mul]
    congr 1
    funext x
    congr 1
    exact mul_div_mul_left _ _ ht

  have pair_shift {d N : ℕ} (hN : 1≤N) (G : UnitAddTorus (Fin d) → ℝ)
      (c : ℝ) (X : Configuration d N) :
      PairEnergy (fun x=>G x+c) X=PairEnergy G X+((N:ℝ)-1)*c/2 := by
    have hn : (N:ℝ)≠0 := by exact_mod_cast (show N≠0 by omega)
    have he (i j : Fin N) : (if i<j then G (X i-X j)+c else (0:ℝ)) =
        (if i<j then G (X i-X j) else 0)+(if i<j then (1:ℝ) else 0)*c := by
      by_cases h : i<j <;> simp [h]
    unfold PairEnergy
    simp_rw [he,Finset.sum_add_distrib,←Finset.sum_mul]
    rw [pair_count_real]
    field_simp
    <;> ring

  have canonical_shift {d N : ℕ} (hN : 1≤N) (G q : UnitAddTorus (Fin d) → ℝ)
      (β c : ℝ) : CanonicalLaw (N:=N) (fun x=>G x+c) q β=CanonicalLaw (N:=N) G q β := by
    unfold CanonicalLaw
    have he : GibbsWeight (N:=N) (fun x=>G x+c) q β =
        fun X=>Real.exp (-β*((N:ℝ)-1)*c/2)*GibbsWeight G q β X := by
      funext X
      unfold GibbsWeight
      rw [pair_shift hN]
      have hneg : -β*(PairEnergy G X+((N:ℝ)-1)*c/2)=
          -β*((N:ℝ)-1)*c/2 + -β*PairEnergy G X := by ring
      rw [hneg,Real.exp_add]
      ring
    rw [he]
    exact tilt_scale _ _ _ (ne_of_gt (Real.exp_pos _))

  have tilt_multiply {Ω : Type} [MeasurableSpace Ω]
      (μ : Measure Ω) (w b : Ω → ℝ) (l u : ℝ)
      (hw : Measurable w) (hwp : ∀ᵐ x ∂μ, 0 ≤ w x)
      (hwi : Integrable w μ) (hZ : 0 < ∫ x, w x ∂μ)
      (hb : Measurable b) (hl : 0 < l)
      (hbb : ∀ᵐ x ∂μ, l ≤ b x ∧ b x ≤ u) :
      NormalizedTilt μ (fun x => b x * w x) =
        NormalizedTilt (NormalizedTilt μ w) b := by
    have hbn : ∀ᵐ x ∂μ, 0 ≤ b x := hbb.mono fun x hx => hl.le.trans hx.1
    have hbabs : ∀ᵐ x ∂μ, ‖b x‖ ≤ max |l| |u| := by
      filter_upwards [hbb, hbn] with x hx hp
      rw [Real.norm_eq_abs, abs_of_nonneg hp]
      exact hx.2.trans ((le_abs_self u).trans (le_max_right _ _))
    have hbwi : Integrable (fun x => b x * w x) μ := hwi.bdd_mul hb.aestronglyMeasurable hbabs
    have hZbw : 0 < ∫ x, b x * w x ∂μ := by
      have hlow : l * ∫ x, w x ∂μ ≤ ∫ x, b x * w x ∂μ := by
        rw [← integral_const_mul]
        apply integral_mono_ae (hwi.const_mul l) hbwi
        filter_upwards [hbb, hwp] with x hx hp
        exact mul_le_mul_of_nonneg_right hx.1 hp
      exact (mul_pos hl hZ).trans_le hlow
    have ht := (TiltNormalization μ w hw hwp hwi hZ).2 b hb (by
      simpa only [mul_comm] using hbwi)
    simp only [NormalizedTilt] at ht ⊢
    rw [ht.2]
    rw [← withDensity_mul μ (by fun_prop) (by fun_prop)]
    apply withDensity_congr_ae
    filter_upwards [hwp, hbn] with x hx hbpos
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (div_nonneg hx hZ.le)]
    congr 1
    field_simp [ne_of_gt hZ, ne_of_gt hZbw]
    <;> ring

  classical
  have hNm : 0≤(N:ℝ)-1 := sub_nonneg.mpr (by exact_mod_cast (show 1≤N by omega))
  have hdN : 0<N*d := Nat.mul_pos (by omega) (by omega)
  have hsd' : s<(d:ℝ) := by linarith
  obtain ⟨c,hc,hcf⟩ := RieszL1Foundation d hd s a hs hsd' ha
  obtain ⟨M,hM,_,_,hMf⟩ := RieszHeatSource d hd s a 1 hs hsd ha (by norm_num)
  let K := B*((N:ℝ)-1)*c/2
  let L := B*((N:ℝ)-1)*M
  have hK : 0≤K := div_nonneg (mul_nonneg (mul_nonneg hB hNm) hc) (by norm_num)
  have hL : 0≤L := mul_nonneg (mul_nonneg hB hNm) hM
  obtain ⟨r,hr,hcompact⟩ := CompactWeightedPoincare (N*d) hdN K L hK hL
  let rate := r*l^N/u^N
  have hu0 : 0<u := zero_lt_one.trans_le hu
  have hrate : 0<rate := div_pos (mul_pos hr (pow_pos hl _)) (pow_pos hu0 _)
  refine ⟨rate,hrate,?_⟩
  intro β ε hβ hβB hε q f hf
  let G := RieszKernel d s a ε
  let Gc := fun x=>G x+c
  let V := fun X:Configuration d N=>β*PairEnergy Gc X
  let μ := NormalizedTilt volume (fun X=>Real.exp (-V X))
  let b := ProductDensity (N:=N) q.density
  let P := CanonicalLaw (N:=N) Gc q.density β
  have hGF := hcf ε hε.le
  have hGs : TorusSmooth G := (RieszLocalStructure d hd s a hs hsd' ha).2.1 ε hε
  have hGcs : TorusSmooth Gc := hGs.add contDiff_const
  have hGcp (x) : 0≤Gc x := by
    have h := hGF.2.2.2.2.1 x
    dsimp [Gc];linarith
  have hGcLap (x) : TorusLaplacian Gc x≤M := by
    have hLap : TorusLaplacian Gc x=TorusLaplacian G x := by
      unfold TorusLaplacian
      simp only [Gc, fderiv_add_const]
    rw [hLap]
    exact (hMf ε hε).2.2.2 x
  obtain ⟨hVs,hVfs,hVp,hVm,hVL,hVLb⟩ :=
    ConfigurationPairPotential d N hN Gc hGcs hGcp M β hM hβ hGcLap
  haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1:ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simpa using (inferInstance : IsProbabilityMeasure AddCircle.haarAddCircle)
  haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := by infer_instance
  haveI : IsProbabilityMeasure (volume : Measure (Configuration d N)) := by infer_instance
  have hGi : Integrable G volume := hGF.2.1
  have hmean : (∫x,Gc x)=c := by
    rw [integral_add hGi (integrable_const c),hGF.2.2.1]
    simp
  have hVmK : (∫x,V ((ConfigurationFlatten d N).symm x))≤K := by
    have hp : MeasurePreserving (ConfigurationFlatten d N) volume volume :=
      ⟨(ConfigurationCalculus d N).1,(ConfigurationCalculus d N).2.2.1⟩
    have he : (∫x,V ((ConfigurationFlatten d N).symm x))=(∫X,V X) := by
      let e : Configuration d N ≃ᵐ UnitAddTorus (Fin (N*d)) :=
        {toEquiv:=ConfigurationFlatten d N
         measurable_toFun:=(ConfigurationCalculus d N).1
         measurable_invFun:=(ConfigurationCalculus d N).2.1}
      rw [←hp.integral_comp e.measurableEmbedding]
      simp
    rw [he,hVm,hmean]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hβB hNm) hc) (by norm_num)
  have hVLL (x) : TorusLaplacian (fun x=>V ((ConfigurationFlatten d N).symm x)) x≤L :=
    (hVLb x).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hβB hNm) hM)
  have hbase := flatten_pi d N V f hVs hf r
    (hcompact _ hVfs (fun x=>hVp _) hVmK hVLL)
  obtain ⟨hfs,hfm,⟨Cf,hfb⟩,hem,⟨Ce,heb⟩,hgrad,hfiber,hfull⟩ :=
    (ConfigurationCalculus d N).2.2.2 f hf
  have hVm : Measurable V := ((ConfigurationCalculus d N).2.2.2 V hVs).2.1
  have hwm : Measurable (fun X=>Real.exp (-V X)) := hVm.neg.exp
  have hwp : ∀ᵐX∂volume,0≤Real.exp (-V X) := Filter.Eventually.of_forall (fun X=>(Real.exp_pos _).le)
  have hwi : Integrable (fun X=>Real.exp (-V X)) volume :=
    (integrable_const (1:ℝ)).mono' hwm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun X=>by
        rw [Real.norm_eq_abs,abs_of_nonneg (Real.exp_nonneg _)]
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hVp X))))
  have hwZ : 0<(∫X,Real.exp (-V X)) := integral_exp_pos hwi
  have ht := TiltNormalization volume _ hwm hwp hwi hwZ
  haveI : IsProbabilityMeasure μ := ht.1
  have hbF := ProductBackgroundFacts d N l u q
  have hbm : Measurable b := hbF.1
  have hbb : ∀ᵐX∂volume,l^N≤b X ∧ b X≤u^N := hbF.2.2.2
  have hac : μ.AbsolutelyContinuous volume := withDensity_absolutelyContinuous _ _
  have hbbμ := hbb.filter_mono hac.ae_le
  have hei : Integrable (fun X=>‖CoordinateGradient f X‖^2) μ :=
    (integrable_const Ce).mono' hem.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun X=>by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)];exact heb X))
  have hcomp := tilt_multiply volume (fun X=>Real.exp (-V X)) b (l^N) (u^N)
    hwm hwp hwi hwZ hbm (pow_pos hl _) hbb
  have hP : P=NormalizedTilt μ b := by
    unfold P CanonicalLaw GibbsWeight
    have hw : (fun X=>Real.exp (-β*PairEnergy Gc X)*b X)=
        fun X=>b X*Real.exp (-V X) := by funext X;dsimp [V];ring
    rw [hw,hcomp]
  have hcPI := BoundedDensityComparison μ b f (fun X=>‖CoordinateGradient f X‖^2)
    (l^N) (u^N) (pow_pos hl _) hbm hbbμ hfm
    ⟨Cf,Filter.Eventually.of_forall hfb⟩ hem
    (Filter.Eventually.of_forall (fun X=>sq_nonneg _)) hei
  have hbB := BoundedTiltBounds μ b (l^N) (u^N) (pow_pos hl _) hbm hbbμ
  have hbZ : 0<(∫X,b X ∂μ) := (pow_pos hl _).trans_le hbB.2.1
  have hfact : 0≤u^N/(∫X,b X ∂μ) := div_nonneg (pow_nonneg hu0.le _) hbZ.le
  have hfinal : variance f P≤(u^N/l^N)*r⁻¹*PhysicalEnergy P f := by
    rw [hP]
    calc
      _ ≤ (u^N/(∫X,b X ∂μ))*variance f μ := hcPI.1
      _ ≤ (u^N/(∫X,b X ∂μ))*(r⁻¹*(∫X,‖CoordinateGradient f X‖^2 ∂μ)) :=
        mul_le_mul_of_nonneg_left hbase hfact
      _ ≤ (u^N/l^N)*r⁻¹*(∫X,‖CoordinateGradient f X‖^2 ∂NormalizedTilt μ b) := by
        have hE := hcPI.2.2.1
        have hfactor : 0≤(u^N/l^N)*r⁻¹ := mul_nonneg
          (div_nonneg (pow_nonneg hu0.le _) (pow_pos hl _).le) (inv_nonneg.mpr hr.le)
        have h := mul_le_mul_of_nonneg_left hE hfactor
        have hid : (u^N/l^N)*r⁻¹*((l^N/(∫X,b X ∂μ))*(∫X,‖CoordinateGradient f X‖^2 ∂μ)) =
            (u^N/(∫X,b X ∂μ))*(r⁻¹*(∫X,‖CoordinateGradient f X‖^2 ∂μ)) := by
          field_simp [ne_of_gt (pow_pos hl N)]
          <;> ring
        rw [hid] at h
        exact h
  have hrateInv : rate⁻¹=(u^N/l^N)*r⁻¹ := by
    dsimp [rate]
    field_simp
  change variance f (CanonicalLaw (N:=N) G q.density β) ≤
    rate⁻¹*PhysicalEnergy (CanonicalLaw (N:=N) G q.density β) f
  rw [←canonical_shift (by omega : 1≤N) G q.density β c]
  rw [hrateInv]
  exact hfinal
