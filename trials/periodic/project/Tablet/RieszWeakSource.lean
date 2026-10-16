module

public import Tablet.RieszSourceMeasure
public import Tablet.RieszFourierCoefficients
public import Tablet.TorusFourierLaplacian
public import Tablet.TorusSmoothFourierSummable
public import Mathlib.MeasureTheory.Measure.WithDensityFinite
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Topology.ContinuousMap.Compact

@[expose] public section
open MeasureTheory Filter UnitAddTorus
open scoped ComplexConjugate
-- [TABLET NODE: RieszWeakSource]
theorem RieszWeakSource (d : ℕ) (hd : 2 ≤ d) (s a a₂ : ℝ)
    (hs : 0 ≤ s) (hsd : s ≤ (d : ℝ) - 2) (ha : 0 < a) (ha₂ : 0 < a₂) :
    ∃ M : ℝ, 0 ≤ M ∧
      (s = (d : ℝ) - 2 → M = a) ∧
      (s < (d : ℝ) - 2 → ∀ x,
        0 ≤ (a / a₂) * RieszKernel d (s + 2) a₂ 0 x + M) ∧
      MeasureTheory.IsFiniteMeasure (RieszSourceMeasure d s a a₂ M) ∧
      (RieszSourceMeasure d s a a₂ M) Set.univ = ENNReal.ofReal M ∧
      ∀ φ : UnitAddTorus (Fin d) → ℝ, TorusSmooth φ →
        -(∫ x, RieszKernel d s a 0 x * TorusLaplacian φ x ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d)))) +
          M * (∫ x, φ x ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d)))) =
            ∫ x, φ x ∂RieszSourceMeasure d s a a₂ M := by
-- BODY
  have riesz_source_mass (d : ℕ) (hd : 2 ≤ d) (s a a₂ : ℝ)
      (hs : 0 ≤ s) (hsd : s ≤ (d : ℝ)-2) (ha : 0<a) (ha₂ : 0<a₂) :
      ∃ M : ℝ,0≤M ∧ (s=(d:ℝ)-2→M=a) ∧
        (s<(d:ℝ)-2→∀x,0≤(a/a₂)*RieszKernel d (s+2) a₂ 0 x+M) ∧
        IsFiniteMeasure (RieszSourceMeasure d s a a₂ M) ∧
        (RieszSourceMeasure d s a a₂ M) Set.univ = ENNReal.ofReal M := by
    classical
    haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
      rw [AddCircle.volume_eq_smul_haarAddCircle]
      simp
      infer_instance
    haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := inferInstance
    by_cases hstrict : s<(d:ℝ)-2
    · obtain ⟨c,hc,hg⟩ := RieszL1Foundation d hd (s+2) a₂ (by linarith) (by linarith) ha₂
      have hp := hg 0 (le_refl 0)
      let M := (a/a₂)*c+1
      let g := RieszKernel d (s+2) a₂ 0
      let w := fun x => (a/a₂)*g x+M
      have hM : 0≤M := by dsimp [M]; positivity
      have hwm : Measurable w := (hp.1.const_mul (a/a₂)).add_const M
      have hwi : Integrable w volume := (hp.2.1.const_mul (a/a₂)).add (integrable_const M)
      have hwp (x) :0≤w x := by
        have hh := mul_le_mul_of_nonneg_left (hp.2.2.2.2.1 x) (div_nonneg ha.le ha₂.le)
        dsimp [w,g,M]
        nlinarith
      have hmean : (∫ x,w x)=M := by
        rw [integral_add (hp.2.1.const_mul (a/a₂)) (integrable_const M),integral_const_mul,
          hp.2.2.1]
        simp
      have hmass : (RieszSourceMeasure d s a a₂ M) Set.univ=ENNReal.ofReal M := by
        unfold RieszSourceMeasure
        rw [if_pos hstrict,withDensity_apply _ MeasurableSet.univ]
        simp only [Measure.restrict_univ]
        rw [←ofReal_integral_eq_lintegral_ofReal hwi
          (Filter.Eventually.of_forall hwp),hmean]
      haveI : IsFiniteMeasure (RieszSourceMeasure d s a a₂ M) :=
        ⟨by rw [hmass]; exact ENNReal.ofReal_lt_top⟩
      refine ⟨M,hM,?_,?_,inferInstance,hmass⟩
      · intro he
        exact False.elim (by linarith)
      · intro h
        exact hwp
    · refine ⟨a,ha.le,fun _=>rfl,?_,?_,?_⟩
      · intro h
        exact False.elim (hstrict h)
      · unfold RieszSourceMeasure
        rw [if_neg hstrict]
        constructor
        simp [Measure.smul_apply, ENNReal.ofReal_lt_top]
      · simp [RieszSourceMeasure,hstrict]

  have char_inverse {d : ℕ} (k : Fin d → ℤ) (x : UnitAddTorus (Fin d)) :
      mFourier k (-x) = conj (mFourier k x) := by
    simp only [mFourier, ContinuousMap.coe_mk, Pi.neg_apply, fourier_apply, smul_neg,
      fourier_neg', map_prod]

  have character_integrable {d : ℕ} (g : UnitAddTorus (Fin d) → ℂ)
      (hg : Integrable g volume) (k : Fin d → ℤ) :
      Integrable (fun x => g x * mFourier k x) volume :=
    hg.mul_bdd (mFourier k).continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => by
        simpa only [mFourier_norm] using (mFourier k).norm_coe_le_norm x)

  have even_character_integral {d : ℕ} (g : UnitAddTorus (Fin d) → ℝ)
      (hg : Integrable g volume) (he : ∀x,g (-x)=g x) (k : Fin d → ℤ) :
      (∫x,(g x : ℂ)*mFourier k x) = (∫x,g x*(mFourier k x).re : ℝ) := by
    have hic : Integrable (fun x => (g x : ℂ)) volume := Complex.ofRealCLM.integrable_comp hg
    have hreal : conj (∫x,(g x : ℂ)*mFourier k x) = ∫x,(g x : ℂ)*mFourier k x := by
      rw [← integral_conj]
      calc
        _ = ∫x,(g (-x) : ℂ)*mFourier k (-x) := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by
            simp only [map_mul, char_inverse, he, Complex.conj_ofReal]
        _ = _ := integral_neg_eq_self (fun x => (g x : ℂ)*mFourier k x) volume
    have hre : (∫x,(g x : ℂ)*mFourier k x).re = ∫x,g x*(mFourier k x).re := by
      change RCLike.re (∫x,(g x : ℂ)*mFourier k x) = _
      rw [← integral_re (character_integrable _ hic k)]
      congr 1
      funext x
      simp
    apply Complex.ext
    · simpa using hre
    · simpa using Complex.conj_eq_iff_im.mp hreal

  have character_mean (d : ℕ) (k : Fin d → ℤ) :
      (∫x,mFourier k x ∂(volume : Measure (UnitAddTorus (Fin d)))) =
        if k=0 then (1:ℂ) else 0 := by
    classical
    have h := (orthonormal_iff_ite.mp (UnitAddTorus.orthonormal_mFourier (d := Fin d))) (-k) 0
    simp only [ContinuousMap.inner_toLp, ← UnitAddTorus.mFourier_neg,
      ← UnitAddTorus.mFourier_add, neg_neg, zero_add, neg_eq_zero] at h
    have hvol : (volume : Measure (UnitAddTorus (Fin d))) =
        Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle (T := (1:ℝ))) := by
      change Measure.pi (fun _ : Fin d => (volume : Measure (AddCircle (1:ℝ)))) = _
      congr 1
      funext j
      rw [AddCircle.volume_eq_smul_haarAddCircle]
      simp
    rw [hvol]
    exact h

  have riesz_complex_coefficient (d : ℕ) (hd : 2≤d) (s a : ℝ)
      (hs : 0≤s) (hsd : s<(d:ℝ)) (ha : 0<a) (k : Fin d→ℤ) (hk : k≠0) :
      (∫x,(RieszKernel d s a 0 x : ℂ)*mFourier k x) =
        (a*Real.rpow (4*Real.pi^2*∑j,(k j:ℝ)^2) (-((d:ℝ)-s)/2) : ℝ) := by
    obtain ⟨c,hc,hg⟩ := RieszL1Foundation d hd s a hs hsd ha
    have hp := hg 0 (le_refl 0)
    rw [even_character_integral _ hp.2.1 hp.2.2.2.1,
      RieszFourierCoefficients d hd s a 0 hs hsd ha (le_refl 0) k hk]
    simp

  have frequency_positive {d : ℕ} (k : Fin d→ℤ) (hk : k≠0) :
      0<4*Real.pi^2*∑j,(k j:ℝ)^2 := by
    have hsum : 0<∑j,(k j:ℝ)^2 := by
      apply Finset.sum_pos'
      · intro j hj; positivity
      · have he : ∃j,k j≠0 := by
          by_contra hh
          push_neg at hh
          exact hk (funext hh)
        obtain ⟨j,hj⟩ := he
        exact ⟨j,Finset.mem_univ j,sq_pos_of_ne_zero (by exact_mod_cast hj)⟩
    positivity

  have source_character_identity (d : ℕ) (hd : 2≤d) (s a a₂ M : ℝ)
      (hs : 0≤s) (hsd : s≤(d:ℝ)-2) (ha : 0<a) (ha₂ : 0<a₂)
      (hM : 0≤M) (hend : s=(d:ℝ)-2→M=a)
      (hpos : s<(d:ℝ)-2→∀x,0≤(a/a₂)*RieszKernel d (s+2) a₂ 0 x+M)
      [IsFiniteMeasure (RieszSourceMeasure d s a a₂ M)]
      (hmass : (RieszSourceMeasure d s a a₂ M) Set.univ=ENNReal.ofReal M)
      (k : Fin d→ℤ) :
      ((4*Real.pi^2*∑j,(k j:ℝ)^2 : ℝ) : ℂ)*
        (∫x,(RieszKernel d s a 0 x : ℂ)*mFourier k x) =
        (∫x,mFourier k x ∂RieszSourceMeasure d s a a₂ M) -
          (M:ℂ)*(∫x,mFourier k x) := by
    classical
    haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
      rw [AddCircle.volume_eq_smul_haarAddCircle]
      simp
      infer_instance
    by_cases hk : k=0
    · subst k
      simp only [Pi.zero_apply,Int.cast_zero,zero_pow (by decide : 2≠0),Finset.sum_const_zero,
        mul_zero,Complex.ofReal_zero,zero_mul,mFourier_zero,ContinuousMap.one_apply]
      rw [integral_const,Measure.real,hmass,ENNReal.toReal_ofReal hM]
      simp
    · rw [riesz_complex_coefficient d hd s a hs (by linarith) ha k hk,
        character_mean,if_neg hk,mul_zero,sub_zero]
      let B : ℝ := 4*Real.pi^2*∑j,(k j:ℝ)^2
      have hB : 0<B := frequency_positive k hk
      by_cases hstrict : s<(d:ℝ)-2
      · obtain ⟨c,hc,hg⟩ := RieszL1Foundation d hd (s+2) a₂ (by linarith) (by linarith) ha₂
        have hp := hg 0 (le_refl 0)
        let w := fun x => (a/a₂)*RieszKernel d (s+2) a₂ 0 x+M
        have hwm : Measurable w := hp.1.const_mul (a/a₂) |>.add_const M
        have hi := character_integrable _ (Complex.ofRealCLM.integrable_comp hp.2.1) k
        change Integrable (fun x=>(RieszKernel d (s+2) a₂ 0 x:ℂ)*mFourier k x) volume at hi
        have hcint : Integrable (mFourier k) volume :=
          (mFourier k).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
        unfold RieszSourceMeasure
        rw [if_pos hstrict, integral_withDensity_eq_integral_toReal_smul
          (hwm.ennreal_ofReal) (Eventually.of_forall fun _=>ENNReal.ofReal_lt_top)]
        simp only [w, ENNReal.toReal_ofReal (hpos hstrict _),Complex.real_smul,
          Complex.ofReal_add,Complex.ofReal_mul,add_mul]
        simp_rw [mul_assoc ((a/a₂:ℝ):ℂ)]
        rw [integral_add (hi.const_mul (a/a₂:ℝ)) (hcint.const_mul (M:ℂ)),
          integral_const_mul,integral_const_mul,
          riesz_complex_coefficient d hd (s+2) a₂ (by linarith) (by linarith) ha₂ k hk,
          character_mean,if_neg hk,mul_zero,add_zero]
        have hexp : -((d:ℝ)-(s+2))/2 = 1+(-((d:ℝ)-s)/2) := by ring
        rw [hexp]
        have hpB : Real.rpow B (1 + (-((d:ℝ)-s)/2)) = B*Real.rpow B (-((d:ℝ)-s)/2) := by
          simp only [Real.rpow_eq_pow]
          rw [Real.rpow_add hB, Real.rpow_one]
        have harith : (B:ℂ)*((a*Real.rpow B (-((d:ℝ)-s)/2):ℝ):ℂ) =
            ((a/a₂:ℝ):ℂ)*((a₂*Real.rpow B (1+(-((d:ℝ)-s)/2)):ℝ):ℂ) := by
          rw [hpB]
          push_cast
          field_simp [ha₂.ne']
        simpa only [B,Complex.ofReal_mul] using harith
      · have he : s=(d:ℝ)-2 := by linarith
        unfold RieszSourceMeasure
        rw [if_neg hstrict,integral_smul_measure,integral_dirac]
        have hchar : mFourier k 0=1 := by
          simp [mFourier,fourier_apply]
        rw [hchar,ENNReal.toReal_ofReal ha.le]
        simp only [Complex.real_smul,smul_eq_mul,mul_one]
        rw [he]
        have hexp : -((d:ℝ)-((d:ℝ)-2))/2 = (-1:ℝ) := by ring
        rw [hexp]
        change (B:ℂ)*((a*Real.rpow B (-1):ℝ):ℂ)=(a:ℂ)
        simp only [Real.rpow_eq_pow]
        rw [Real.rpow_neg_one B]
        change (B:ℂ)*((a*B⁻¹:ℝ):ℂ)=(a:ℂ)
        push_cast
        field_simp [hB.ne']

  have complex_weighted_continuous_integral {Ω : Type} [TopologicalSpace Ω]
      [CompactSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
      (μ : Measure Ω) (g : Ω → ℂ) (hg : Integrable g μ) :
      ∃ I : C(Ω,ℂ) →L[ℂ] ℂ, ∀ φ, I φ = ∫ x,g x*φ x ∂μ := by
    have hi (φ : C(Ω,ℂ)) : Integrable (fun x=>g x*φ x) μ :=
      hg.mul_bdd φ.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x=>φ.norm_coe_le_norm x)
    let A : C(Ω,ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun φ => ∫ x,g x*φ x ∂μ
        map_add' := by
          intro φ ψ
          simp only [ContinuousMap.add_apply,mul_add]
          exact integral_add (hi φ) (hi ψ)
        map_smul' := by
          intro c φ
          simp only [ContinuousMap.smul_apply,smul_eq_mul]
          simp_rw [mul_left_comm (g _) c]
          exact integral_const_mul c _ }
    have hb (φ : C(Ω,ℂ)) : ‖A φ‖ ≤ (∫ x,‖g x‖ ∂μ)*‖φ‖ := by
      change ‖∫ x,g x*φ x ∂μ‖ ≤ _
      calc
        _ ≤ ∫ x,‖g x*φ x‖ ∂μ := norm_integral_le_integral_norm _
        _ ≤ ∫ x,‖g x‖*‖φ‖ ∂μ := by
          apply integral_mono (hi φ).norm (hg.norm.mul_const ‖φ‖)
          intro x
          change ‖g x*φ x‖ ≤ ‖g x‖*‖φ‖
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (φ.norm_coe_le_norm x) (norm_nonneg _)
        _ = (∫ x,‖g x‖ ∂μ)*‖φ‖ := integral_mul_const _ _
    exact ⟨A.mkContinuous _ hb, fun _=>rfl⟩

  have torus_fourier_weak_join (d : ℕ) (g : UnitAddTorus (Fin d) → ℝ)
      (hg : Integrable g volume) (μ : Measure (UnitAddTorus (Fin d))) [IsFiniteMeasure μ]
      (M : ℝ)
      (hchar : ∀k : Fin d→ℤ,
        ((4*Real.pi^2*∑j,(k j:ℝ)^2:ℝ):ℂ)*(∫x,(g x:ℂ)*mFourier k x) =
          (∫x,mFourier k x ∂μ)-(M:ℂ)*(∫x,mFourier k x))
      (φ : UnitAddTorus (Fin d) → ℝ) (hφ : TorusSmooth φ) :
      -(∫x,g x*TorusLaplacian φ x)+M*(∫x,φ x)=∫x,φ x ∂μ := by
    have hcont := (TorusFourierLaplacian d φ hφ).1
    have hlap := (TorusFourierLaplacian d φ hφ).2.1
    have hdlcont := (TorusFourierLaplacian d (TorusLaplacian φ) hlap).1
    let Φ : C(UnitAddTorus (Fin d),ℂ) := ⟨fun x=>(φ x:ℂ),Complex.continuous_ofReal.comp hcont⟩
    let D : C(UnitAddTorus (Fin d),ℂ) :=
      ⟨fun x=>(TorusLaplacian φ x:ℂ),Complex.continuous_ofReal.comp hdlcont⟩
    have hdcoeff (k : Fin d→ℤ) :
        mFourierCoeff D k = ((-(4*Real.pi^2*∑j,(k j:ℝ)^2):ℝ):ℂ)*mFourierCoeff Φ k := by
      have hh := (TorusFourierLaplacian d φ hφ).2.2.2 (-k)
      have hvol : (volume:Measure (UnitAddTorus (Fin d))) =
          Measure.pi (fun _:Fin d=>AddCircle.haarAddCircle (T := (1:ℝ))) := by
        change Measure.pi (fun _:Fin d=>(volume:Measure (AddCircle (1:ℝ)))) = _
        congr 1
        funext j
        rw [AddCircle.volume_eq_smul_haarAddCircle]
        simp
      simp only [mFourierCoeff,smul_eq_mul,Φ,D,ContinuousMap.coe_mk]
      change (∫t,mFourier (-k) t*(TorusLaplacian φ t:ℂ)
        ∂Measure.pi (fun _:Fin d=>AddCircle.haarAddCircle)) = _
      change _ = ((-(4*Real.pi^2*∑j,(k j:ℝ)^2):ℝ):ℂ)*
        (∫t,mFourier (-k) t*(φ t:ℂ)
        ∂Measure.pi (fun _:Fin d=>AddCircle.haarAddCircle))
      rw [←hvol]
      simpa only [Pi.neg_apply,Int.cast_neg,neg_sq,mul_comm] using hh
    obtain ⟨G,hG⟩ := complex_weighted_continuous_integral volume (fun x=>(g x:ℂ))
      (Complex.ofRealCLM.integrable_comp hg)
    obtain ⟨U,hU⟩ := complex_weighted_continuous_integral μ (fun _=>(1:ℂ)) (integrable_const 1)
    obtain ⟨H,hH⟩ := complex_weighted_continuous_integral (volume : Measure (UnitAddTorus (Fin d))) (fun _=>(1:ℂ)) (integrable_const 1)
    have hchar' k :
        ((4*Real.pi^2*∑j,(k j:ℝ)^2:ℝ):ℂ)*G (mFourier k) =
          U (mFourier k)-(M:ℂ)*H (mFourier k) := by
      simpa only [hG,hU,hH,one_mul] using hchar k
    have hsΦ : HasSum (fun k=>mFourierCoeff Φ k • mFourier k) Φ :=
      hasSum_mFourier_series_of_summable (TorusSmoothFourierSummable d φ hφ)
    have hsD : HasSum (fun k=>mFourierCoeff D k • mFourier k) D :=
      hasSum_mFourier_series_of_summable (TorusSmoothFourierSummable d (TorusLaplacian φ) hlap)
    have hsleft := (G.hasSum hsD).neg
    have hsright := (U.hasSum hsΦ).sub ((H.hasSum hsΦ).mul_left (M:ℂ))
    have heq : -G D=U Φ-(M:ℂ)*H Φ := by
      apply hsleft.unique
      convert hsright using 1
      funext k
      simp only [map_smul,smul_eq_mul,hdcoeff]
      have hh := congrArg (fun z : ℂ => mFourierCoeff Φ k*z) (hchar' k)
      push_cast at hh ⊢
      linear_combination hh
    have hgc : Integrable (fun x=>(g x:ℂ)*(TorusLaplacian φ x:ℂ)) volume :=
      (Complex.ofRealCLM.integrable_comp hg).mul_bdd D.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x=>D.norm_coe_le_norm x)
    have hφi : Integrable (fun x=>(φ x:ℂ)) volume :=
      Φ.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hφμi : Integrable (fun x=>(φ x:ℂ)) μ :=
      Φ.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    simp only [hG,hU,hH,one_mul] at heq
    have hr := congrArg Complex.re heq
    simp only [Complex.neg_re,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero] at hr
    have hgr : (∫x,(g x:ℂ)*D x).re=∫x,g x*TorusLaplacian φ x := by
      change RCLike.re (∫x,(g x:ℂ)*(TorusLaplacian φ x:ℂ))=_
      rw [← integral_re hgc]
      simp [D]
    have hHr : (∫x,Φ x).re=∫x,φ x := by
      change RCLike.re (∫x,(φ x:ℂ))=_
      rw [← integral_re hφi]
      rfl
    have hUr : (∫x,Φ x ∂μ).re=∫x,φ x ∂μ := by
      change RCLike.re (∫x,(φ x:ℂ) ∂μ)=_
      rw [← integral_re hφμi]
      rfl
    rw [hgr,hHr,hUr] at hr
    linarith

  obtain ⟨M,hM,hend,hpos,hfinite,hmass⟩ := riesz_source_mass d hd s a a₂ hs hsd ha ha₂
  haveI := hfinite
  obtain ⟨c,hc,hg⟩ := RieszL1Foundation d hd s a hs (by linarith) ha
  refine ⟨M,hM,hend,hpos,hfinite,hmass,?_⟩
  intro φ hφ
  exact torus_fourier_weak_join d (RieszKernel d s a 0) (hg 0 (le_refl 0)).2.1
    (RieszSourceMeasure d s a a₂ M) M
    (source_character_identity d hd s a a₂ M hs hsd ha ha₂ hM hend hpos hmass) φ hφ
