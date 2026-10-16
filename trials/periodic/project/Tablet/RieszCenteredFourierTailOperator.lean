module

public import Tablet.PositiveFourierConvolution
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Tablet.Preamble
public import Mathlib.MeasureTheory.Integral.Prod
public import Tablet.CenteredKernel
public import Tablet.RieszMellinFourier
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section
open MeasureTheory Set Filter UnitAddTorus
open scoped Topology ComplexConjugate
set_option maxHeartbeats 4000000
-- [TABLET NODE: RieszCenteredFourierTailOperator]
theorem RieszCenteredFourierTailOperator (d:ℕ)(s a:ℝ)(hsd:s<(d:ℝ))(ha:0<a)
    (δ ε:ℝ)(hδ:0<δ)(hε:0≤ε)(K:Finset (Fin d→ℤ))(hKs:∀k,k∈K↔-k∈K)
    (σ:ℝ)(hσ:0≤σ)
    (htail:∀k:Fin d→ℤ,k∉K→
      (if k=0 then 0 else a*(4*Real.pi^2*∑j,(k j:ℝ)^2)^(-((d:ℝ)-s)/2))≤σ)
    (r:UnitAddTorus (Fin d)→ℝ)(hr:Measurable r)(M:ℝ)(hM:0≤M)
    (hrb:∀ᵐx∂(volume:Measure (UnitAddTorus (Fin d))),0≤r x∧r x≤M)(hmass:∫x,r x=1):
    let low:=fun x:UnitAddTorus (Fin d)=>∑k∈K,RieszMellinCoefficient d s a δ ε k*(mFourier k x).re
    let v:=fun x=>RieszMellinLong d s a δ ε x-low x
    let μ:Measure (UnitAddTorus (Fin d)):=volume.withDensity (fun x=>ENNReal.ofReal (r x))
    ∀f g:UnitAddTorus (Fin d)→ℝ,Measurable f→Measurable g→
      ∀hf:MemLp f 2 μ,∀hg:MemLp g 2 μ,
      |∫x,∫y,CenteredKernel v r x y*f x*g y∂μ∂μ|≤
        M*σ*‖hf.toLp f‖*‖hg.toLp g‖:=by
-- BODY
  have hpot_integral {d : ℕ} (v w : UnitAddTorus (Fin d)→ℝ) :
      BackgroundPotential v w = fun x => ∫y,v (x-y)*w y := by
    funext x
    unfold BackgroundPotential convolution
    change (∫y,w y*v (x-y)) = ∫y,v (x-y)*w y
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => mul_comm _ _)
  classical
  have HaarSpectralConvolutionNorm (d : ℕ) (K : UnitAddTorus (Fin d) → ℝ)
      (hKm : Measurable K) (hK : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), ‖K x‖ ≤ 1)
      (he : ∀x,K (-x)=K x) (hF : ∀k:Fin d→ℤ,0≤∫x,K x*(mFourier k x).re)
      (σ : ℝ) (hσ : 0≤σ) (hcoeff : ∀k:Fin d→ℤ, |∫x,K x*(mFourier k x).re|≤σ) :
      ∃T:Lp ℝ 2 (volume:Measure (UnitAddTorus (Fin d))) →L[ℝ] Lp ℝ 2 volume,
        ‖T‖≤σ ∧ ∀f:UnitAddTorus (Fin d)→ℝ,∀hf:MemLp f 2 volume,
          ⇑(T (hf.toLp f))=ᵐ[volume] fun x=>∫y,K (x-y)*f y := by
    let conv {d : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (K : UnitAddTorus (Fin d) → ℝ) (f : UnitAddTorus (Fin d) → E) :
        UnitAddTorus (Fin d) → E := convolution K f (ContinuousLinearMap.lsmul ℝ ℝ) volume
  
    have conv_formula {d : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (K : UnitAddTorus (Fin d) → ℝ) (f : UnitAddTorus (Fin d) → E) (x) :
        conv K f x = ∫ y, K (x-y) • f y := by
      dsimp only [conv]
      rw [← convolution_flip]
      rfl
  
    have volume_eq_haar (d : ℕ) : (volume : Measure (UnitAddTorus (Fin d))) =
        Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle) := by
      change Measure.pi _ = _
      congr 1
      funext i
      rw [AddCircle.volume_eq_smul_haarAddCircle]
      simp
  
    have char_add {d : ℕ} (k : Fin d → ℤ) (x y : UnitAddTorus (Fin d)) :
        mFourier k (x+y) = mFourier k x * mFourier k y := by
      simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply, smul_add,
        AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]
  
    have char_inv {d : ℕ} (k : Fin d → ℤ) (x : UnitAddTorus (Fin d)) :
        mFourier k (-x) = conj (mFourier k x) := by
      simp only [mFourier, ContinuousMap.coe_mk, Pi.neg_apply, fourier_apply, smul_neg,
        fourier_neg', map_prod]
  
    have char_norm {d : ℕ} (k : Fin d → ℤ) (x : UnitAddTorus (Fin d)) : ‖mFourier k x‖ = 1 := by
      simp only [mFourier, ContinuousMap.coe_mk, norm_prod, fourier_apply, Circle.norm_coe,
        Finset.prod_const_one]
  
    let coef {d : ℕ} (f : UnitAddTorus (Fin d) → ℂ) (k : Fin d → ℤ) :=
      ∫ x, mFourier (-k) x * f x
  
    have coef_integrable {d : ℕ} (f : UnitAddTorus (Fin d) → ℂ) (hi : Integrable f volume) (k : Fin d → ℤ) :
        Integrable (fun x => mFourier (-k) x * f x) volume := by
      exact hi.bdd_mul (mFourier (-k)).continuous.measurable.aestronglyMeasurable
        (Eventually.of_forall fun x => (char_norm (-k) x).le)
  
    have coef_eq {d : ℕ} (f : UnitAddTorus (Fin d) → ℂ) (k : Fin d → ℤ) : coef f k = mFourierCoeff f k := by
      unfold coef mFourierCoeff
      simp only [smul_eq_mul]
      change (∫ x, mFourier (-k) x * f x ∂(volume : Measure (UnitAddTorus (Fin d)))) =
        ∫ x, mFourier (-k) x * f x ∂Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle)
      rw [volume_eq_haar]
  
    have coef_congr {d : ℕ} {f g : UnitAddTorus (Fin d) → ℂ} (h : f =ᵐ[volume] g) (k : Fin d → ℤ) :
        coef f k = coef g k := by
      exact integral_congr_ae (h.mono fun x hx => by simp only [hx])
  
    have coef_conv {d : ℕ} (K : UnitAddTorus (Fin d) → ℝ) (hKm : Measurable K)
        (hK : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), ‖K x‖ ≤ 1)
        (f : UnitAddTorus (Fin d) → ℂ) (hfi : Integrable f volume) (k : Fin d → ℤ) :
        coef (conv K f) k = coef (fun x => (K x : ℂ)) k * coef f k := by
      have hKi : Integrable K volume := Integrable.of_bound hKm.aestronglyMeasurable 1 hK
      have hci : Integrable (fun v : UnitAddTorus (Fin d) × UnitAddTorus (Fin d) =>
          (mFourier (-k) v.1) * (K v.2 • f (v.1-v.2))) (volume.prod volume) :=
        (hKi.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hfi).bdd_mul
          ((mFourier (-k)).continuous.measurable.comp measurable_fst).aestronglyMeasurable
          (Eventually.of_forall fun v => (char_norm (-k) v.1).le)
      have htrans (y : UnitAddTorus (Fin d)) :
          (∫ x, mFourier (-k) x * (K y • f (x-y))) =
            mFourier (-k) y * (K y : ℂ) * coef f k := by
        calc
          _ = ∫ z, mFourier (-k) (z+y) * (K y • f ((z+y)-y)) :=
            (integral_add_right_eq_self _ y).symm
          _ = ∫ z, (mFourier (-k) y * (K y : ℂ)) * (mFourier (-k) z * f z) := by
            apply integral_congr_ae
            exact Eventually.of_forall fun z => by
              dsimp only
              rw [char_add, add_sub_cancel_right]
              simp only [Complex.real_smul]
              ring
          _ = _ := integral_const_mul _ _
      change (∫ x, mFourier (-k) x * conv K f x) = _
      calc
        _ = ∫ x, ∫ y, mFourier (-k) x * (K y • f (x-y)) := by
          congr 1
          funext x
          change mFourier (-k) x * (∫ y, K y • f (x-y)) = _
          exact (integral_const_mul _ _).symm
        _ = ∫ y, ∫ x, mFourier (-k) x * (K y • f (x-y)) := integral_integral_swap hci
        _ = ∫ y, (mFourier (-k) y * (K y : ℂ)) * coef f k := by
          congr 1
          funext y
          exact htrans y
        _ = _ := integral_mul_const _ _
  
    have coef_real {d : ℕ} (K : UnitAddTorus (Fin d) → ℝ) (hi : Integrable K volume)
        (he : ∀ x, K (-x) = K x) (k : Fin d → ℤ) :
        coef (fun x => (K x : ℂ)) k = (∫ x, K x * (mFourier (-k) x).re : ℝ) := by
      have hic : Integrable (fun x => (K x : ℂ)) volume := Complex.ofRealCLM.integrable_comp hi
      have hreal : conj (coef (fun x => (K x : ℂ)) k) = coef (fun x => (K x : ℂ)) k := by
        unfold coef
        rw [← integral_conj]
        calc
          _ = ∫ x, mFourier (-k) (-x) * (K (-x) : ℂ) := by
            apply integral_congr_ae
            exact Eventually.of_forall fun x => by dsimp; simp only [map_mul, char_inv, he, Complex.conj_ofReal]
          _ = _ := integral_neg_eq_self (fun x => mFourier (-k) x * (K x : ℂ)) volume
      have hre : (coef (fun x => (K x : ℂ)) k).re = ∫ x, K x * (mFourier (-k) x).re := by
        unfold coef
        change RCLike.re (∫ x, mFourier (-k) x * (K x : ℂ)) = _
        rw [← integral_re (coef_integrable _ hic k)]
        congr 1
        funext x
        change (mFourier (-k) x * (K x : ℂ)).re = K x * (mFourier (-k) x).re
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        ring
      apply Complex.ext
      · simpa using hre
      · simpa using Complex.conj_eq_iff_im.mp hreal
  
    have norm_sq_integral {d : ℕ} (f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d)))) :
        (∫ x, ‖f x‖ ^ 2) = ‖f‖ ^ 2 := by
      have hi := congrArg Complex.re (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) f)
      rw [L2.inner_def] at hi
      have hri := integral_re (L2.integrable_inner (𝕜 := ℂ) f f)
      change (∫ x, RCLike.re (inner ℂ (f x) (f x))) = _ at hri
      change RCLike.re (∫ x, inner ℂ (f x) (f x)) = RCLike.re ((‖f‖ : ℂ) ^ 2) at hi
      rw [← hri] at hi
      simp only [inner_self_eq_norm_sq_to_K] at hi
      change (∫ x, (((‖f x‖ : ℂ) ^ 2).re)) = ((‖f‖ : ℂ) ^ 2).re at hi
      simpa only [← Complex.ofReal_pow, Complex.ofReal_re] using hi
  
    have square_sum_function {d : ℕ} (f : UnitAddTorus (Fin d) → ℂ) (hf : MemLp f 2 volume) :
        HasSum (fun k => ‖coef f k‖ ^ 2) (∫ x, ‖f x‖ ^ 2) := by
      let mh : Measure (UnitAddTorus (Fin d)) := Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle)
      have hfh : MemLp f 2 mh := by dsimp [mh]; rw [← volume_eq_haar]; exact hf
      let fh := hfh.toLp f
      have heq := MemLp.coeFn_toLp hfh
      have hs := hasSum_sq_mFourierCoeff fh
      have hc (k : Fin d → ℤ) : mFourierCoeff fh k = coef f k := by
        rw [coef_eq]
        unfold mFourierCoeff
        exact integral_congr_ae (heq.mono fun x hx => by simp only [fh, hx])
      simp_rw [hc] at hs
      convert hs using 1
      dsimp only [mh] at heq
      rw [volume_eq_haar]
      exact integral_congr_ae (heq.symm.mono fun x hx => by simp only [fh, hx])
  
    obtain ⟨T,hT,_⟩:=PositiveFourierConvolution d K hKm hK he hF
    refine ⟨T,?_,fun f hf=>(hT.2.2.2 f hf).2⟩
    apply ContinuousLinearMap.opNorm_le_bound T hσ
    intro f
    let F:UnitAddTorus (Fin d)→ℂ:=fun x=>(f x:ℂ)
    let G:UnitAddTorus (Fin d)→ℂ:=fun x=>(T f x:ℂ)
    have hFm:MemLp F 2 volume:=(Lp.memLp f).ofReal
    have hGm:MemLp G 2 volume:=(Lp.memLp (T f)).ofReal
    have hG:G=ᵐ[volume] conv K F:=by
      have hh:=(hT.2.2.2 (fun x=>f x) (Lp.memLp f)).2
      have hrep:(Lp.memLp f).toLp (fun x=>f x)=f:=by
        apply Lp.ext
        exact (Lp.memLp f).coeFn_toLp
      rw[hrep] at hh
      filter_upwards[hh] with x hx
      rw[conv_formula]
      change (T f x:ℂ)=∫y,K (x-y) • (f y:ℂ)
      rw[hx]
      simp_rw[Complex.real_smul,←Complex.ofReal_mul]
      exact integral_ofReal.symm
    have hcoef(k:Fin d→ℤ):coef G k=coef (fun x=>(K x:ℂ)) k*coef F k:=by
      rw[coef_congr hG]
      exact coef_conv K hKm hK F (hFm.integrable (by norm_num)) k
    have hpF:=square_sum_function F hFm
    have hpG:=square_sum_function G hGm
    have hnormF:(∫x,‖F x‖^2)=‖f‖^2:=by
      have hh:=real_inner_self_eq_norm_sq f
      rw[L2.inner_def] at hh
      simpa [F,Complex.norm_real,Real.norm_eq_abs,sq_abs,real_inner_self_eq_norm_sq] using hh
    have hnormG:(∫x,‖G x‖^2)=‖T f‖^2:=by
      have hh:=real_inner_self_eq_norm_sq (T f)
      rw[L2.inner_def] at hh
      simpa [G,Complex.norm_real,Real.norm_eq_abs,sq_abs,real_inner_self_eq_norm_sq] using hh
    have hb(k:Fin d→ℤ):‖coef G k‖^2≤σ^2*‖coef F k‖^2:=by
      rw[hcoef,norm_mul,mul_pow]
      have hc:‖coef (fun x=>(K x:ℂ)) k‖≤σ:=by
        rw[coef_real K (Integrable.of_bound hKm.aestronglyMeasurable 1 hK) he,
          Complex.norm_real,Real.norm_eq_abs]
        exact hcoeff (-k)
      exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) hσ).mpr hc) (sq_nonneg _)
    have hi:(∫x,‖G x‖^2)≤σ^2*(∫x,‖F x‖^2):=by
      rw[←hpG.tsum_eq,←hpF.tsum_eq,←tsum_mul_left]
      exact Summable.tsum_le_tsum hb hpG.summable (hpF.summable.mul_left (σ^2))
    rw[hnormF,hnormG] at hi
    nlinarith [norm_nonneg f,norm_nonneg (T f),mul_nonneg hσ (norm_nonneg f)]
  have WeightedCenteredDensityL2 {d:ℕ}
      (m:Measure (UnitAddTorus (Fin d)))[IsProbabilityMeasure m](r:(UnitAddTorus (Fin d))→ℝ)(hr:Measurable r)(M:ℝ)(hM:0≤M)
      (hrb:∀ᵐx∂m,0≤r x∧r x≤M)(hmass:∫x,r x∂m=1)
      (f:(UnitAddTorus (Fin d))→ℝ)(hfm:Measurable f)
      (hf:MemLp f 2 (m.withDensity (fun x=>ENNReal.ofReal (r x)))) :
      let μ:=m.withDensity (fun x=>ENNReal.ofReal (r x))
      let F:=fun x=>r x*(f x-∫y,f y∂μ)
      MemLp F 2 m ∧ (∫x,F x^2∂m)≤M*(∫x,f x^2∂μ) := by
    let μ:=m.withDensity (fun x=>ENNReal.ofReal (r x))
    have hrn:=hrb.mono fun x hx=>hx.1
    have hri:Integrable r m:=Integrable.of_bound hr.aestronglyMeasurable M
      (hrb.mono fun x hx=>by simpa [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2)
    haveI:IsProbabilityMeasure μ:=by
      apply isProbabilityMeasure_iff.mpr
      rw [withDensity_apply _ MeasurableSet.univ]
      simp only [Measure.restrict_univ]
      rw [←ofReal_integral_eq_lintegral_ofReal hri hrn,hmass]
      simp
    let a:=∫x,f x∂μ
    let f0:=fun x=>f x-a
    have hf0:MemLp f0 2 μ:=hf.sub (memLp_const a)
    have hf0i:Integrable (fun x=>f0 x^2) μ:=hf0.integrable_sq
    have hfi:Integrable f μ:=hf.integrable (by norm_num)
    have hsfi:Integrable (fun x=>f x^2) μ:=hf.integrable_sq
    have intμ(g:(UnitAddTorus (Fin d))→ℝ):(∫x,g x∂μ)=∫x,r x*g x∂m:=by
      rw[integral_withDensity_eq_integral_toReal_smul hr.ennreal_ofReal
        (Eventually.of_forall fun _=>ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      filter_upwards[hrn] with x hx
      simp only[ENNReal.toReal_ofReal hx,smul_eq_mul]
    have hwi:Integrable (fun x=>r x*f0 x^2) m:=by
      have hh:=(integrable_withDensity_iff_integrable_smul' hr.ennreal_ofReal
        (Eventually.of_forall fun _=>ENNReal.ofReal_lt_top)).mp hf0i
      apply hh.congr
      filter_upwards[hrn] with x hx
      simp only[ENNReal.toReal_ofReal hx,smul_eq_mul]
    have hb:∀ᵐx∂m,‖(r x*f0 x)^2‖≤M*(r x*f0 x^2):=by
      filter_upwards[hrb] with x hx
      rw[Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have hh:=mul_le_mul_of_nonneg_right hx.2 hx.1
      nlinarith [mul_le_mul_of_nonneg_right hh (sq_nonneg (f0 x))]
    have hFsi:Integrable (fun x=>(r x*f0 x)^2) m:=
      (hwi.const_mul M).mono' ((hr.mul (hfm.sub_const a)).pow_const 2).aestronglyMeasurable hb
    have hF:MemLp (fun x=>r x*f0 x) 2 m:=
      (memLp_two_iff_integrable_sq (hr.mul (hfm.sub_const a)).aestronglyMeasurable).mpr hFsi
    have hsq:(∫x,f0 x^2∂μ)=(∫x,f x^2∂μ)-a^2:=by
      have hid:∀x,f0 x^2=f x^2-(2*a)*f x+a^2:=fun x=>by dsimp[f0];ring
      simp_rw[hid]
      rw[integral_add (f:=fun x=>f x^2-(2*a)*f x) (g:=fun _=>a^2)
        (hsfi.sub (hfi.const_mul (2*a))) (integrable_const (a^2)),
        integral_sub hsfi (hfi.const_mul (2*a)),integral_const_mul]
      simp only[integral_const]
      simp only[Measure.real,measure_univ,ENNReal.toReal_one,one_smul]
      change (∫x,f x^2∂μ)-2*a*a+a^2=_
      ring
    refine ⟨hF,?_⟩
    change (∫x,(r x*f0 x)^2∂m)≤M*(∫x,f x^2∂μ)
    calc
      _≤∫x,M*(r x*f0 x^2)∂m:=integral_mono_ae hFsi (hwi.const_mul M)
        (hb.mono fun x hx=>by simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (r x*f0 x))] using hx)
      _=M*(∫x,f0 x^2∂μ):=by rw[integral_const_mul,←intμ]
      _≤M*(∫x,f x^2∂μ):=by rw[hsq];nlinarith [mul_nonneg hM (sq_nonneg a)]
  have CenteredBilinearIdentity {d:ℕ}
      (μ:Measure (UnitAddTorus (Fin d)))[IsProbabilityMeasure μ](K:(UnitAddTorus (Fin d))→(UnitAddTorus (Fin d))→ℝ)
      (hK:Measurable (fun p:(UnitAddTorus (Fin d))×(UnitAddTorus (Fin d))=>K p.1 p.2)) (A:ℝ)(hA:0≤A)
      (hKb:∀x y,|K x y|≤A)(hKs:∀x y,K x y=K y x)
      (f g:(UnitAddTorus (Fin d))→ℝ)(hf:Integrable f μ)(hg:Integrable g μ) :
      let h:=fun x=>∫y,K x y∂μ
      let J:=∫x,h x∂μ
      (∫p:(UnitAddTorus (Fin d))×(UnitAddTorus (Fin d)),(K p.1 p.2-h p.1-h p.2+J)*f p.1*g p.2∂μ.prod μ)=
        ∫p:(UnitAddTorus (Fin d))×(UnitAddTorus (Fin d)),K p.1 p.2*(f p.1-∫x,f x∂μ)*(g p.2-∫y,g y∂μ)∂μ.prod μ := by
    let h:=fun x=>∫y,K x y∂μ
    let J:=∫x,h x∂μ
    let a:=∫x,f x∂μ
    let b:=∫x,g x∂μ
    have hkm(x):Measurable (fun y=>K x y):=hK.comp (measurable_const.prodMk measurable_id)
    have hki(x):Integrable (fun y=>K x y) μ:=Integrable.of_bound (hkm x).aestronglyMeasurable A
      (Eventually.of_forall fun y=>by simpa [Real.norm_eq_abs] using hKb x y)
    have hhm:Measurable h:=hK.stronglyMeasurable.integral_prod_right.measurable
    have hhb(x):‖h x‖≤A:=by
      calc
        _≤∫y,‖K x y‖∂μ:=norm_integral_le_integral_norm _
        _≤∫_:(UnitAddTorus (Fin d)),A∂μ:=integral_mono (hki x).norm (integrable_const A)
          (fun y=>by simpa [Real.norm_eq_abs] using hKb x y)
        _=A:=by simp
    have hhi:Integrable h μ:=Integrable.of_bound hhm.aestronglyMeasurable A (Eventually.of_forall hhb)
    have hfh:Integrable (fun x=>h x*f x) μ:=hf.bdd_mul hhm.aestronglyMeasurable (Eventually.of_forall hhb)
    have hgh:Integrable (fun x=>h x*g x) μ:=hg.bdd_mul hhm.aestronglyMeasurable (Eventually.of_forall hhb)
    have pair_int(u v:(UnitAddTorus (Fin d))→ℝ)(hu:Integrable u μ)(hv:Integrable v μ):
        Integrable (fun p:(UnitAddTorus (Fin d))×(UnitAddTorus (Fin d))=>K p.1 p.2*u p.1*v p.2) (μ.prod μ):=by
      have hh:=hu.mul_prod hv
      have hi:=hh.bdd_mul hK.aestronglyMeasurable
        (Eventually.of_forall fun p=>by simpa [Real.norm_eq_abs] using hKb p.1 p.2)
      convert hi using 1
      funext p
      ring
    have left(u:(UnitAddTorus (Fin d))→ℝ)(hu:Integrable u μ):
        (∫p:(UnitAddTorus (Fin d))×(UnitAddTorus (Fin d)),K p.1 p.2*u p.1∂μ.prod μ)=∫x,h x*u x∂μ:=by
      have hi:=pair_int u (fun _=>1) hu (integrable_const 1)
      simp only[mul_one] at hi
      rw[integral_prod _ hi]
      congr 1
      funext x
      change (∫y,K x y*u x∂μ)=h x*u x
      rw[integral_mul_const]
    have right(v:(UnitAddTorus (Fin d))→ℝ)(hv:Integrable v μ):
        (∫p:(UnitAddTorus (Fin d))×(UnitAddTorus (Fin d)),K p.1 p.2*v p.2∂μ.prod μ)=∫y,h y*v y∂μ:=by
      have hi:=pair_int (fun _=>1) v (integrable_const 1) hv
      simp only[mul_one] at hi
      rw[integral_prod _ hi,integral_integral_swap hi]
      congr 1
      funext y
      simp_rw[hKs _ y]
      rw[integral_mul_const]
    have mean:(∫p:(UnitAddTorus (Fin d))×(UnitAddTorus (Fin d)),K p.1 p.2∂μ.prod μ)=J:=by
      have hh:=left (fun _=>1) (integrable_const 1)
      simpa [J] using hh
    let t1:=fun p:(UnitAddTorus (Fin d))×(UnitAddTorus (Fin d))=>K p.1 p.2*f p.1*g p.2
    let t2:=fun p:(UnitAddTorus (Fin d))×(UnitAddTorus (Fin d))=>(h p.1*f p.1)*g p.2
    let t3:=fun p:(UnitAddTorus (Fin d))×(UnitAddTorus (Fin d))=>f p.1*(h p.2*g p.2)
    let t4:=fun p:(UnitAddTorus (Fin d))×(UnitAddTorus (Fin d))=>J*(f p.1*g p.2)
    have i1:Integrable t1 (μ.prod μ):=pair_int f g hf hg
    have i2:Integrable t2 (μ.prod μ):=hfh.mul_prod hg
    have i3:Integrable t3 (μ.prod μ):=hf.mul_prod hgh
    have i4:Integrable t4 (μ.prod μ):=(hf.mul_prod hg).const_mul J
    have qexp:(fun p:(UnitAddTorus (Fin d))×(UnitAddTorus (Fin d))=>(K p.1 p.2-h p.1-h p.2+J)*f p.1*g p.2)=
        (fun p=>t1 p-t2 p-t3 p+t4 p):=by funext p;dsimp[t1,t2,t3,t4];ring
    have qint:(∫p:(UnitAddTorus (Fin d))×(UnitAddTorus (Fin d)),(K p.1 p.2-h p.1-h p.2+J)*f p.1*g p.2∂μ.prod μ)=
        (∫p,t1 p∂μ.prod μ)-(∫x,h x*f x∂μ)*b-a*(∫y,h y*g y∂μ)+J*(a*b):=by
      rw[qexp,integral_add (f:=fun p=>t1 p-t2 p-t3 p) (g:=t4) ((i1.sub i2).sub i3) i4,
        integral_sub (f:=fun p=>t1 p-t2 p) (g:=t3) (i1.sub i2) i3,integral_sub i1 i2]
      dsimp only[t2,t3,t4]
      rw[integral_prod_mul (fun x=>h x*f x) g,
        integral_prod_mul f (fun x=>h x*g x),integral_const_mul,integral_prod_mul f g]
    let s2:=fun p:(UnitAddTorus (Fin d))×(UnitAddTorus (Fin d))=>b*(K p.1 p.2*f p.1)
    let s3:=fun p:(UnitAddTorus (Fin d))×(UnitAddTorus (Fin d))=>a*(K p.1 p.2*g p.2)
    let s4:=fun p:(UnitAddTorus (Fin d))×(UnitAddTorus (Fin d))=>(a*b)*K p.1 p.2
    have j2:Integrable s2 (μ.prod μ):=by
      have hh:=pair_int f (fun _=>1) hf (integrable_const 1)
      simp only[mul_one] at hh
      exact hh.const_mul b
    have j3:Integrable s3 (μ.prod μ):=by
      have hh:=pair_int (fun _=>1) g (integrable_const 1) hg
      simp only[mul_one] at hh
      exact hh.const_mul a
    have j4:Integrable s4 (μ.prod μ):=by
      have hh:=pair_int (fun _=>1) (fun _=>1) (integrable_const 1) (integrable_const 1)
      simp only[mul_one] at hh
      exact hh.const_mul (a*b)
    have cexp:(fun p:(UnitAddTorus (Fin d))×(UnitAddTorus (Fin d))=>K p.1 p.2*(f p.1-a)*(g p.2-b))=
        (fun p=>t1 p-s2 p-s3 p+s4 p):=by funext p;dsimp[t1,s2,s3,s4];ring
    change (∫p:(UnitAddTorus (Fin d))×(UnitAddTorus (Fin d)),(K p.1 p.2-h p.1-h p.2+J)*f p.1*g p.2∂μ.prod μ)=
        ∫p:(UnitAddTorus (Fin d))×(UnitAddTorus (Fin d)),K p.1 p.2*(f p.1-a)*(g p.2-b)∂μ.prod μ
    rw[qint,cexp,integral_add (f:=fun p=>t1 p-s2 p-s3 p) (g:=s4) ((i1.sub j2).sub j3) j4,
      integral_sub (f:=fun p=>t1 p-s2 p) (g:=s3) (i1.sub j2) j3,integral_sub i1 j2]
    dsimp only[s2,s3,s4]
    rw[integral_const_mul,integral_const_mul,integral_const_mul,left f hf,right g hg,mean]
    ring
  have WeightedCenteredFourierOperatorBound (d:ℕ)(K r:UnitAddTorus (Fin d)→ℝ)
      (hKm:Measurable K)(hKb:∀x,|K x|≤1)(he:∀x,K (-x)=K x)
      (hF:∀k:Fin d→ℤ,0≤∫x,K x*(mFourier k x).re)
      (σ:ℝ)(hσ:0≤σ)(hcoeff:∀k:Fin d→ℤ,|∫x,K x*(mFourier k x).re|≤σ)
      (hr:Measurable r)(M:ℝ)(hM:0≤M)
      (hrb:∀ᵐx∂(volume:Measure (UnitAddTorus (Fin d))),0≤r x∧r x≤M)(hmass:∫x,r x=1):
      let μ:Measure (UnitAddTorus (Fin d)):=volume.withDensity (fun x=>ENNReal.ofReal (r x))
      ∀f g:UnitAddTorus (Fin d)→ℝ,Measurable f→Measurable g→
        ∀hf:MemLp f 2 μ,∀hg:MemLp g 2 μ,
        |∫x,∫y,CenteredKernel K r x y*f x*g y∂μ∂μ|≤
          M*σ*‖hf.toLp f‖*‖hg.toLp g‖:=by
    dsimp only
    haveI:IsProbabilityMeasure (volume:Measure (AddCircle (1:ℝ))):=by
      rw[AddCircle.volume_eq_smul_haarAddCircle];simp;infer_instance
    let m:Measure (UnitAddTorus (Fin d)):=volume
    let μ:Measure (UnitAddTorus (Fin d)):=m.withDensity (fun x=>ENNReal.ofReal (r x))
    have hrn:=hrb.mono fun x hx=>hx.1
    have hri:Integrable r m:=Integrable.of_bound hr.aestronglyMeasurable M
      (hrb.mono fun x hx=>by simpa [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2)
    haveI:IsProbabilityMeasure μ:=by
      apply isProbabilityMeasure_iff.mpr
      rw [withDensity_apply _ MeasurableSet.univ]
      simp only [Measure.restrict_univ]
      rw [←ofReal_integral_eq_lintegral_ofReal hri hrn,hmass]
      simp
    have intμ(u:UnitAddTorus (Fin d)→ℝ):(∫x,u x∂μ)=∫x,r x*u x∂m:=by
      rw[integral_withDensity_eq_integral_toReal_smul hr.ennreal_ofReal
        (Eventually.of_forall fun _=>ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      filter_upwards[hrn] with x hx
      simp only[ENNReal.toReal_ofReal hx,smul_eq_mul]
    let k:=fun(x y:UnitAddTorus (Fin d))=>K (x-y)
    have hkm:Measurable (fun p:UnitAddTorus (Fin d)×UnitAddTorus (Fin d)=>k p.1 p.2):=
      hKm.comp (measurable_fst.sub measurable_snd)
    have hks(x y):k x y=k y x:=by
      dsimp[k];rw[←neg_sub x y,he]
    have hki(x):Integrable (fun y=>k x y) μ:=Integrable.of_bound
      (hKm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable 1
      (Eventually.of_forall fun y=>by simpa[Real.norm_eq_abs,k] using hKb (x-y))
    let h:=fun x=>∫y,k x y∂μ
    let J:=∫x,h x∂μ
    have hhm:Measurable h:=hkm.stronglyMeasurable.integral_prod_right.measurable
    have hhb(x):‖h x‖≤1:=by
      calc
        _≤∫y,‖k x y‖∂μ:=norm_integral_le_integral_norm _
        _≤∫_:UnitAddTorus (Fin d),(1:ℝ)∂μ:=integral_mono (hki x).norm (integrable_const _)
          (fun y=>by simpa[Real.norm_eq_abs,k] using hKb (x-y))
        _=1:=by simp
    have hJ:|J|≤1:=by
      calc
        _≤∫x,‖h x‖∂μ:=by simpa[Real.norm_eq_abs] using norm_integral_le_integral_norm h
        _≤∫_:UnitAddTorus (Fin d),(1:ℝ)∂μ:=integral_mono
          (Integrable.of_bound hhm.aestronglyMeasurable 1 (Eventually.of_forall hhb)).norm
          (integrable_const _) hhb
        _=1:=by simp
    have hid(x):h x=BackgroundPotential K r x:=by
      dsimp only[h]
      rw[intμ]
      simp only [hpot_integral]
      apply integral_congr_ae
      exact Eventually.of_forall fun y=>by dsimp[k];ring
    have hJid:J=BackgroundPairMean K r:=by
      dsimp[J]
      rw[intμ]
      unfold BackgroundPairMean
      apply integral_congr_ae
      exact Eventually.of_forall fun x=>by change r x*h x=BackgroundPotential K r x*r x;rw[hid x];ring
    have qid(x y):CenteredKernel K r x y=k x y-h x-h y+J:=by
      rw[hid,hid,hJid];rfl
    obtain ⟨T,hT,hTf⟩:=HaarSpectralConvolutionNorm d K hKm
      (Eventually.of_forall fun x=>by simpa[Real.norm_eq_abs] using hKb x) he hF σ hσ hcoeff
    intro f g hfm hgm hf hg
    have hfi:=hf.integrable (by norm_num: (1:ENNReal)≤2)
    have hgi:=hg.integrable (by norm_num: (1:ENNReal)≤2)
    let f0:=fun x=>f x-∫z,f z∂μ
    let g0:=fun x=>g x-∫z,g z∂μ
    let F:=fun x=>r x*f0 x
    let G:=fun x=>r x*g0 x
    obtain ⟨hFm,hFb⟩:=WeightedCenteredDensityL2 m r hr M hM hrb hmass f hfm hf
    obtain ⟨hGm,hGb⟩:=WeightedCenteredDensityL2 m r hr M hM hrb hmass g hgm hg
    have pairI(u v:UnitAddTorus (Fin d)→ℝ)(hu:Integrable u μ)(hv:Integrable v μ):
        Integrable (fun p=>k p.1 p.2*u p.1*v p.2) (μ.prod μ):=by
      have hh:=(hu.mul_prod hv).bdd_mul hkm.aestronglyMeasurable
        (Eventually.of_forall fun p=>by simpa[Real.norm_eq_abs,k] using hKb (p.1-p.2))
      convert hh using 1
      funext p;ring
    have hqm:Measurable (fun p:UnitAddTorus (Fin d)×UnitAddTorus (Fin d)=>CenteredKernel K r p.1 p.2):=by
      simp_rw[qid]
      exact ((hkm.sub (hhm.comp measurable_fst)).sub (hhm.comp measurable_snd)).add measurable_const
    have qi:Integrable (fun p=>CenteredKernel K r p.1 p.2*f p.1*g p.2) (μ.prod μ):=by
      apply ((hfi.norm.mul_prod hgi.norm).const_mul 4).mono'
        ((hqm.mul (hfm.comp measurable_fst)).mul (hgm.comp measurable_snd)).aestronglyMeasurable
      exact Eventually.of_forall fun p=>by
        change ‖CenteredKernel K r p.1 p.2*f p.1*g p.2‖≤4*(‖f p.1‖*‖g p.2‖)
        rw[norm_mul,norm_mul,qid,Real.norm_eq_abs]
        have hx:|h p.1|≤1:=by simpa[Real.norm_eq_abs] using hhb p.1
        have hy:|h p.2|≤1:=by simpa[Real.norm_eq_abs] using hhb p.2
        have hh:|k p.1 p.2-h p.1-h p.2+J|≤4:=by
          calc
            _≤|k p.1 p.2-h p.1-h p.2|+|J|:=abs_add_le _ _
            _≤(|k p.1 p.2-h p.1|+|h p.2|)+|J|:=
              by linarith [abs_sub (k p.1 p.2-h p.1) (h p.2)]
            _≤(|k p.1 p.2|+|h p.1|)+|h p.2|+|J|:=
              by linarith [abs_sub (k p.1 p.2) (h p.1)]
            _≤4:=by have hk:=hKb (p.1-p.2);dsimp[k] at *;linarith
        nlinarith [mul_le_mul_of_nonneg_right hh (mul_nonneg (norm_nonneg (f p.1)) (norm_nonneg (g p.2)))]
    have center:(∫x,∫y,CenteredKernel K r x y*f x*g y∂μ∂μ)=
        ∫x,∫y,k x y*f0 x*g0 y∂μ∂μ:=by
      rw[←integral_prod _ qi]
      simp_rw[qid]
      have hc:=CenteredBilinearIdentity μ k hkm 1 (by norm_num) (fun x y=>hKb (x-y)) hks f g hfi hgi
      exact hc.trans (integral_prod _ (pairI f0 g0 (hfi.sub (integrable_const _)) (hgi.sub (integrable_const _))))
    have transfer:(∫x,∫y,k x y*f0 x*g0 y∂μ∂μ)=
        ∫x,F x*(∫y,K (x-y)*G y∂m)∂m:=by
      rw[intμ]
      apply integral_congr_ae
      exact Eventually.of_forall fun x=>by
        change r x*(∫y,k x y*f0 x*g0 y∂μ)=F x*(∫y,K (x-y)*G y∂m)
        rw[intμ,←integral_const_mul,←integral_const_mul]
        congr 1
        funext y
        dsimp[F,G,k]
        ring
    have innerEq:(∫x,F x*(∫y,K (x-y)*G y∂m)∂m)=
        inner ℝ (hFm.toLp F) (T (hGm.toLp G)):=by
      rw[L2.inner_def]
      apply integral_congr_ae
      filter_upwards[hFm.coeFn_toLp,hTf G hGm] with x hx hy
      change (hFm.toLp F) x=F x at hx
      change F x*(∫y,K (x-y)*G y∂m)=inner ℝ ((hFm.toLp F) x) ((T (hGm.toLp G)) x)
      rw[hx,hy]
      change F x*(∫y,K (x-y)*G y∂m)=(∫y,K (x-y)*G y∂m)*F x
      ring
    have normSq (ρ:Measure (UnitAddTorus (Fin d))) (u:UnitAddTorus (Fin d)→ℝ)(hu:MemLp u 2 ρ):
        ‖hu.toLp u‖^2=∫x,u x^2∂ρ:=by
      have hh:=real_inner_self_eq_norm_sq (hu.toLp u)
      rw[L2.inner_def] at hh
      rw[←hh]
      apply integral_congr_ae
      filter_upwards[hu.coeFn_toLp] with x hx
      simp[real_inner_self_eq_norm_sq,hx,Real.norm_eq_abs,sq_abs]
    have nF:‖hFm.toLp F‖≤Real.sqrt M*‖hf.toLp f‖:=by
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
      rw[←normSq m F hFm,←normSq μ f hf] at hFb
      simpa only[mul_pow,Real.sq_sqrt hM] using hFb
    have nG:‖hGm.toLp G‖≤Real.sqrt M*‖hg.toLp g‖:=by
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
      rw[←normSq m G hGm,←normSq μ g hg] at hGb
      simpa only[mul_pow,Real.sq_sqrt hM] using hGb
    rw[center,transfer,innerEq]
    calc
      _≤‖hFm.toLp F‖*‖T (hGm.toLp G)‖:=abs_real_inner_le_norm _ _
      _≤(Real.sqrt M*‖hf.toLp f‖)*(σ*(Real.sqrt M*‖hg.toLp g‖)):=by
        apply mul_le_mul nF _ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
        exact (T.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hT (norm_nonneg _)).trans
          (mul_le_mul_of_nonneg_left nG hσ))
      _=M*σ*‖hf.toLp f‖*‖hg.toLp g‖:=by
        calc
          _=(Real.sqrt M)^2*σ*‖hf.toLp f‖*‖hg.toLp g‖:=by ring
          _=_:=by rw[Real.sq_sqrt hM]
  have BoundedWeightedCenteredFourierOperator (d:ℕ)(K r:UnitAddTorus (Fin d)→ℝ)
      (hKm:Measurable K)(C:ℝ)(hC:0<C)(hKb:∀x,|K x|≤C)(he:∀x,K (-x)=K x)
      (hF:∀k:Fin d→ℤ,0≤∫x,K x*(mFourier k x).re)
      (σ:ℝ)(hσ:0≤σ)(hcoeff:∀k:Fin d→ℤ,|∫x,K x*(mFourier k x).re|≤σ)
      (hr:Measurable r)(M:ℝ)(hM:0≤M)
      (hrb:∀ᵐx∂(volume:Measure (UnitAddTorus (Fin d))),0≤r x∧r x≤M)(hmass:∫x,r x=1):
      let μ:Measure (UnitAddTorus (Fin d)):=volume.withDensity (fun x=>ENNReal.ofReal (r x))
      ∀f g:UnitAddTorus (Fin d)→ℝ,Measurable f→Measurable g→
        ∀hf:MemLp f 2 μ,∀hg:MemLp g 2 μ,
        |∫x,∫y,CenteredKernel K r x y*f x*g y∂μ∂μ|≤
          M*σ*‖hf.toLp f‖*‖hg.toLp g‖:=by
    dsimp only
    let μ:Measure (UnitAddTorus (Fin d)):=volume.withDensity (fun x=>ENNReal.ofReal (r x))
    let L:=fun x=>K x/C
    have hLm:Measurable L:=hKm.div_const C
    have hLb(x):|L x|≤1:=by
      dsimp[L];rw[abs_div,abs_of_pos hC]
      exact (div_le_one hC).mpr (hKb x)
    have hLe(x):L (-x)=L x:=by dsimp[L];rw[he]
    have hc(k:Fin d→ℤ):(∫x,L x*(mFourier k x).re)=(∫x,K x*(mFourier k x).re)/C:=by
      simp_rw[L,div_mul_eq_mul_div,integral_div]
    have hLF(k:Fin d→ℤ):0≤∫x,L x*(mFourier k x).re:=by rw[hc];exact div_nonneg (hF k) hC.le
    have hLc(k:Fin d→ℤ):|∫x,L x*(mFourier k x).re|≤σ/C:=by
      rw[hc,abs_div,abs_of_pos hC]
      exact div_le_div_of_nonneg_right (hcoeff k) hC.le
    have hp(x):BackgroundPotential L r x=BackgroundPotential K r x/C:=by
      simp only [hpot_integral]
      dsimp only[L]
      simp_rw[div_mul_eq_mul_div]
      rw[integral_div]
    have hJ:BackgroundPairMean L r=BackgroundPairMean K r/C:=by
      unfold BackgroundPairMean
      simp_rw[hp,div_mul_eq_mul_div]
      rw[integral_div]
    have hq(x y):CenteredKernel L r x y=CenteredKernel K r x y/C:=by
      unfold CenteredKernel
      rw[hp,hp,hJ]
      ring
    have ht:=WeightedCenteredFourierOperatorBound d L r hLm hLb hLe hLF
      (σ/C) (div_nonneg hσ hC.le) hLc hr M hM hrb hmass
    intro f g hfm hgm hf hg
    have hh:=ht f g hfm hgm hf hg
    simp_rw[hq,div_mul_eq_mul_div,integral_div] at hh
    rw[abs_div,abs_of_pos hC] at hh
    have hs:=(div_le_iff₀ hC).mp hh
    convert hs using 1 <;> field_simp [hC.ne'] <;> ring
  classical
  dsimp only
  have volume_eq_haar (d:ℕ):
      (volume:Measure (UnitAddTorus (Fin d)))=Measure.pi (fun _:Fin d=>AddCircle.haarAddCircle (T:=(1:ℝ))):=by
    change Measure.pi (fun _:Fin d=>(volume:Measure (AddCircle (1:ℝ))))=_
    congr 1
    funext j
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
  have character_mean (d:ℕ) (k:Fin d→ℤ):
      (∫x:UnitAddTorus (Fin d),mFourier k x)=if k=0 then (1:ℂ) else 0:=by
    classical
    have h:=(orthonormal_iff_ite.mp (orthonormal_mFourier (d:=Fin d))) (-k) 0
    simp only [ContinuousMap.inner_toLp,←mFourier_neg,←mFourier_add,neg_neg,zero_add,neg_eq_zero] at h
    rw [volume_eq_haar]
    exact h

  have cosine_complex (d:ℕ) (n:Fin d→ℤ) (x:UnitAddTorus (Fin d)):
      ((mFourier n x).re:ℂ)=(mFourier n x+mFourier (-n) x)/2:=by
    rw [mFourier_neg]
    apply Complex.ext <;>simp <;>ring
  have cosine_series_coefficient (d:ℕ) (c:(Fin d→ℤ)→ℝ) (hc:∀n,0≤c n)
      (hs:Summable c) (he:∀n,c (-n)=c n) (k:Fin d→ℤ):
      (∫x:UnitAddTorus (Fin d),((∑'n:Fin d→ℤ,c n*(mFourier n x).re:ℝ):ℂ)*mFourier k x)=(c k:ℂ):=by
    classical
    letI:IsProbabilityMeasure (volume:Measure (AddCircle (1:ℝ))):=by
      rw [AddCircle.volume_eq_smul_haarAddCircle];simp;infer_instance
    have hcn(n:Fin d→ℤ)(x:UnitAddTorus (Fin d)):‖mFourier n x‖=1:=by
      simp only [mFourier,ContinuousMap.coe_mk,fourier_apply,norm_prod,Circle.norm_coe,Finset.prod_const_one]
    let F:=fun(n:Fin d→ℤ)(x:UnitAddTorus (Fin d))=>((c n*(mFourier n x).re:ℝ):ℂ)*mFourier k x
    have hFi:∀n,Integrable (F n) volume:=fun n=>
      ((Complex.continuous_ofReal.comp (continuous_const.mul (Complex.continuous_re.comp (mFourier n).continuous))).mul
        (mFourier k).continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hbn(n)(x:UnitAddTorus (Fin d)):‖F n x‖≤c n:=by
      dsimp [F]
      rw [norm_mul,hcn, mul_one,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_nonneg (hc n)]
      exact mul_le_of_le_one_right (hc n) ((Complex.abs_re_le_norm _).trans_eq (hcn n x))
    have hbs:Summable (fun n=>∫x:UnitAddTorus (Fin d),‖F n x‖):=
      Summable.of_nonneg_of_le (fun _=>integral_nonneg (fun _=>norm_nonneg _))
        (fun n=>by simpa using integral_mono (hFi n).norm (integrable_const (c n)) (hbn n)) hs
    have hint:=integral_tsum_of_summable_integral_norm hFi hbs
    have hcoef(n:Fin d→ℤ):(∫x:UnitAddTorus (Fin d),F n x)=
        (if n=-k then ((c n/2:ℝ):ℂ) else 0)+(if n=k then ((c n/2:ℝ):ℂ) else 0):=by
      have hprod(m:Fin d→ℤ):Integrable (fun x:UnitAddTorus (Fin d)=>mFourier m x*mFourier k x) volume:=
        ((mFourier m).continuous.mul (mFourier k).continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      have hF:F n=(fun x:UnitAddTorus (Fin d)=>(c n/2:ℂ)*(mFourier (n+k) x+mFourier (-n+k) x)):=by
        funext x
        dsimp [F]
        rw [Complex.ofReal_mul,cosine_complex]
        simp only [mFourier_add]
        push_cast
        ring
      rw [hF,integral_const_mul,integral_add
        ((mFourier (n+k)).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        ((mFourier (-n+k)).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
        character_mean,character_mean]
      have h1:n+k=0↔n=-k:=add_eq_zero_iff_eq_neg
      have h2:-n+k=0↔n=k:=by simp [neg_add_eq_zero]
      simp only [h1,h2]
      split_ifs <;>push_cast <;>ring
    have hfns:(fun x:UnitAddTorus (Fin d)=>((∑'n:Fin d→ℤ,c n*(mFourier n x).re:ℝ):ℂ)*mFourier k x)=
        (fun x=>∑'n,F n x):=by
      funext x
      rw [Complex.ofReal_tsum,←tsum_mul_right]
    rw [hfns,←hint]
    simp_rw [hcoef]
    have h1:Summable (fun n:Fin d→ℤ=>if n=-k then ((c n/2:ℝ):ℂ) else 0):=by
      convert (hasSum_ite_eq (-k) ((c (-k)/2:ℝ):ℂ)).summable using 1
      funext n
      split_ifs with h
      · subst n;rfl
      · rfl
    have h2:Summable (fun n:Fin d→ℤ=>if n=k then ((c n/2:ℝ):ℂ) else 0):=by
      convert (hasSum_ite_eq k ((c k/2:ℝ):ℂ)).summable using 1
      funext n
      split_ifs with h
      · subst n;rfl
      · rfl
    rw [h1.tsum_add h2]
    simp [he]

  have character_norm (d:ℕ)(k:Fin d→ℤ)(x:UnitAddTorus (Fin d)):‖mFourier k x‖=1:=by
    simp only[mFourier,ContinuousMap.coe_mk,fourier_apply,norm_prod,Circle.norm_coe,Finset.prod_const_one]
  let full:=fun k:Fin d→ℤ=>if k=0 then 0 else a*(4*Real.pi^2*∑j,(k j:ℝ)^2)^(-((d:ℝ)-s)/2)
  let c:=RieszMellinCoefficient d s a δ ε
  let low:=fun x:UnitAddTorus (Fin d)=>∑k∈K,c k*(mFourier k x).re
  let q:=fun x:UnitAddTorus (Fin d)=>RieszMellinLong d s a δ ε x-low x
  let b:=fun k:Fin d→ℤ=>if k∈K then 0 else c k
  have hc:∀k,0≤c k:=fun k=>(RieszMellinCoefficientBounds d s a hsd ha δ ε hδ hε).2.2 k|>.1
  have hcb:∀k,c k≤full k:=fun k=>(RieszMellinCoefficientBounds d s a hsd ha δ ε hδ hε).2.2 k|>.2.1
  have hcs:Summable c:=(RieszMellinCoefficientBounds d s a hsd ha δ ε hδ hε).1
  have hb:∀k,0≤b k:=by intro k;dsimp [b];split_ifs;exact le_rfl;exact hc k
  have hble:∀k,b k≤c k:=by intro k;dsimp [b];split_ifs;exact hc k;exact le_rfl
  have hbs:Summable b:=Summable.of_nonneg_of_le hb hble hcs
  have hbe:∀k,b (-k)=b k:=by
    intro k
    dsimp [b]
    have hce:c (-k)=c k:=(RieszMellinCoefficientBounds d s a hsd ha δ ε hδ hε).2.1 k
    simp only [←hKs k,hce]
  have hq:∀x:UnitAddTorus (Fin d),q x=∑'k:Fin d→ℤ,b k*(mFourier k x).re:=by
    intro x
    have hss:Summable (fun k:Fin d→ℤ=>c k*(mFourier k x).re):=by
      apply summable_norm_iff.mp
      apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _) _ hcs
      intro k
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hc k)]
      exact mul_le_of_le_one_right (hc k) ((Complex.abs_re_le_norm _).trans_eq (character_norm d k x))
    have hex:=hss.sum_add_tsum_subtype_compl K
    have hsub:=tsum_subtype {k:Fin d→ℤ|k∉K} (fun k=>c k*(mFourier k x).re)
    simp only [Set.indicator_apply,Set.mem_setOf_eq] at hsub
    have hsub':(∑'k:{k//k∉K},c k*(mFourier k x).re)=
        (∑'k:Fin d→ℤ,if k∉K then c k*(mFourier k x).re else 0):=by
      convert! hsub using 1
    rw [hsub'] at hex
    have hrep:∑'k:Fin d→ℤ,(if k∉K then c k*(mFourier k x).re else 0)=
        ∑'k:Fin d→ℤ,b k*(mFourier k x).re:=by
      apply tsum_congr
      intro k
      dsimp [b]
      by_cases hk:k∈K
      · simp only [hk,not_true_eq_false,if_false,if_true,zero_mul]
      · simp only [hk,not_false_eq_true,if_true,if_false]
    rw [hrep,←(RieszMellinFourier d s a hsd ha δ ε hδ hε).2.1 x] at hex
    dsimp [q,low]
    linarith
  have hqc:Continuous q:=by
    dsimp [q,low]
    exact (RieszMellinFourier d s a hsd ha δ ε hδ hε).2.2.2.sub
      (continuous_finsetSum K (fun k _=>continuous_const.mul (Complex.continuous_re.comp (mFourier k).continuous)))
  letI:IsProbabilityMeasure (volume:Measure (AddCircle (1:ℝ))):=by
    rw [AddCircle.volume_eq_smul_haarAddCircle];simp;infer_instance
  obtain ⟨D,hD⟩:= (isCompact_univ: IsCompact (Set.univ:Set (UnitAddTorus (Fin d)))).exists_bound_of_continuousOn hqc.continuousOn
  have hqm:MemLp q 2 volume:=MemLp.of_bound hqc.measurable.aestronglyMeasurable D
    (Eventually.of_forall (fun x=>hD x (mem_univ x)))
  have hcoef(k:Fin d→ℤ): (∫x:UnitAddTorus (Fin d),(q x:ℂ)*mFourier k x)=(b k:ℂ):=by
    simp_rw[hq]
    exact cosine_series_coefficient d b hb hbs hbe k
  have hrealcoef(k:Fin d→ℤ):(∫x:UnitAddTorus (Fin d),q x*(mFourier k x).re)=b k:=by
    have hi:Integrable (fun x:UnitAddTorus (Fin d)=>(q x:ℂ)*mFourier k x) volume:=
      ((Complex.continuous_ofReal.comp hqc).mul (mFourier k).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hh:=congrArg Complex.re (hcoef k)
    change RCLike.re (∫x:UnitAddTorus (Fin d),(q x:ℂ)*mFourier k x)=b k at hh
    rw[←integral_re hi] at hh
    change (∫x:UnitAddTorus (Fin d),((q x:ℂ)*mFourier k x).re)=b k at hh
    simpa only[Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hh
  have hqn(k:Fin d→ℤ):0≤∫x:UnitAddTorus (Fin d),q x*(mFourier k x).re:=by rw[hrealcoef];exact hb k
  have hqb(k:Fin d→ℤ):|∫x:UnitAddTorus (Fin d),q x*(mFourier k x).re|≤σ:=by
    rw[hrealcoef,abs_of_nonneg (hb k)]
    dsimp[b]
    split_ifs with hk
    · exact hσ
    · exact (hcb k).trans (htail k hk)
  have hinv(k:Fin d→ℤ)(x:UnitAddTorus (Fin d)):mFourier k (-x)=conj (mFourier k x):=by
    simp only[mFourier,ContinuousMap.coe_mk,Pi.neg_apply,fourier_apply,smul_neg,
      fourier_neg',map_prod]
  have hqe(x):q (-x)=q x:=by simp_rw[hq,hinv,Complex.conj_re]
  have hDb(x):|q x|≤|D|+1:=by
    calc
      _≤D:=by simpa[Real.norm_eq_abs] using hD x (mem_univ x)
      _≤|D|:=le_abs_self D
      _≤|D|+1:=by linarith
  exact BoundedWeightedCenteredFourierOperator d q r hqc.measurable (|D|+1)
    (by positivity) hDb hqe hqn σ hσ hqb hr M hM hrb hmass
