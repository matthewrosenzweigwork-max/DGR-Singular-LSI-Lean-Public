module

public import Tablet.RieszMellinFourier
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section
open MeasureTheory Set Filter UnitAddTorus
open scoped Topology ComplexConjugate
-- [TABLET NODE: TorusCosineSeriesParseval]
theorem TorusCosineSeriesParseval (d:ℕ) (c:(Fin d→ℤ)→ℝ) (hc:∀k,0≤c k)
    (hs:Summable c) (he:∀k,c (-k)=c k)
    (v:UnitAddTorus (Fin d)→ℝ) (hv:Continuous v)
    (hrep:∀x,v x=∑'k:Fin d→ℤ,c k*(mFourier k x).re) :
    Integrable (fun x=>v x^2) volume ∧
      (∫x:UnitAddTorus (Fin d),v x^2)=∑'k:Fin d→ℤ,c k^2 := by
-- BODY
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

  have coeff_square_parseval (d:ℕ) (f:UnitAddTorus (Fin d)→ℂ) (hf:MemLp f 2 volume):
      HasSum (fun k:Fin d→ℤ=>‖∫x:UnitAddTorus (Fin d),f x*mFourier k x‖^2)
        (∫x:UnitAddTorus (Fin d),‖f x‖^2):=by
    have hv:=volume_eq_haar d
    rw [hv] at hf
    let F:=hf.toLp f
    have he:∀k:Fin d→ℤ,mFourierCoeff F (-k)=∫x:UnitAddTorus (Fin d),f x*mFourier k x:=by
      intro k
      unfold mFourierCoeff
      simp only [neg_neg,smul_eq_mul]
      rw [hv]
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      change mFourier k x*F x=f x*mFourier k x
      rw [hx,mul_comm]
    have hint:(∫x:UnitAddTorus (Fin d),‖f x‖^2)=
        ∫x:UnitAddTorus (Fin d),‖F x‖^2∂Measure.pi (fun _:Fin d=>AddCircle.haarAddCircle (T:=(1:ℝ))):=by
      rw [hv]
      apply integral_congr_ae
      exact hf.coeFn_toLp.symm.fun_comp (fun z:ℂ=>‖z‖^2)
    rw [hint]
    have hn:= (Equiv.neg (Fin d→ℤ)).hasSum_iff.mpr (hasSum_sq_mFourierCoeff F)
    convert! hn using 1 <;> simp only [Function.comp_def,Equiv.neg_apply,he]

  haveI:IsProbabilityMeasure (volume:Measure (AddCircle (1:ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle];simp;infer_instance
  obtain ⟨D,hD⟩:=(isCompact_univ:IsCompact (Set.univ:Set (UnitAddTorus (Fin d)))).exists_bound_of_continuousOn hv.continuousOn
  have hm:MemLp v 2 volume:=MemLp.of_bound hv.measurable.aestronglyMeasurable D
    (Eventually.of_forall (fun x=>hD x (mem_univ x)))
  have hcoef(k:Fin d→ℤ):(∫x:UnitAddTorus (Fin d),(v x:ℂ)*mFourier k x)=(c k:ℂ) := by
    simp_rw [hrep]
    exact cosine_series_coefficient d c hc hs he k
  have hP:=coeff_square_parseval d (fun x=>(v x:ℂ)) hm.ofReal
  have hPB:HasSum (fun k:Fin d→ℤ=>c k^2) (∫x:UnitAddTorus (Fin d),v x^2) := by
    simpa only [hcoef,Complex.norm_real,Real.norm_eq_abs,sq_abs] using hP
  exact ⟨(hv.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _),hPB.tsum_eq.symm⟩
