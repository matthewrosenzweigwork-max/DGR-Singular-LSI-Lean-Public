module

public import Tablet.SummableGramEnergyBound
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section
open MeasureTheory
open scoped ComplexConjugate
-- [TABLET NODE: SummableGramCentering]
theorem SummableGramCentering {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (w : ι→ℝ) (f : ι→Ω→ℂ)
    (hw : ∀k,0≤w k) (hws : Summable w) (hf : ∀k,Measurable (f k))
    (hfb : ∀k x,‖f k x‖≤1) :
    let a:ι→ℂ:=fun k=>∫x,f k x∂μ
    let G:Ω→Ω→ℝ:=fun x y=>∑'k,w k*(f k x*conj (f k y)).re
    (∀x y,G x y-(∫z,G x z∂μ)-(∫z,G y z∂μ)+(∫z,∫z',G z z'∂μ∂μ)=
      ∑'k,w k*((f k x-a k)*conj (f k y-a k)).re) ∧
    (∀k x,‖f k x-a k‖≤2) ∧
    (∀N:ℕ,1≤N→∀X:Fin N→Ω,
      -2*(∑'k,w k)≤(N:ℝ)⁻¹*∑i:Fin N,∑j:Fin N,
        if i<j then G (X i) (X j)-(∫z,G (X i) z∂μ)-(∫z,G (X j) z∂μ)+(∫z,∫z',G z z'∂μ∂μ) else 0) := by
-- BODY
  classical
  let a:ι→ℂ:=fun k=>∫x,f k x∂μ
  let G:Ω→Ω→ℝ:=fun x y=>∑'k,w k*(f k x*conj (f k y)).re
  have hfi (k:ι) : Integrable (f k) μ:=Integrable.of_bound (hf k).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (hfb k))
  have hab (k:ι) : ‖a k‖≤1 :=by
    calc
      _≤∫x,‖f k x‖∂μ:=norm_integral_le_integral_norm _
      _≤∫_:Ω,(1:ℝ)∂μ:=integral_mono (hfi k).norm (integrable_const _) (hfb k)
      _=1:=by simp
  have hbound (k:ι) (z z':ℂ) (hz:‖z‖≤1) (hz':‖z'‖≤1) : ‖w k*(z*conj z').re‖≤w k :=by
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hw k)]
    have hRe : |(z*conj z').re|≤1 :=by
      calc
        _≤‖z*conj z'‖:=Complex.abs_re_le_norm _
        _=‖z‖*‖z'‖:=by rw [norm_mul,Complex.norm_conj]
        _≤1*1:=mul_le_mul hz hz' (norm_nonneg _) (by norm_num)
        _=1:=by norm_num
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hRe (hw k)
  have hcomm (F:ι→Ω→ℝ) (hFm:∀k,Measurable (F k)) (hFb:∀k x,‖F k x‖≤w k) :
      (∫x,∑'k,F k x∂μ)=∑'k,∫x,F k x∂μ :=by
    have hFi (k:ι) : Integrable (F k) μ:=Integrable.of_bound (hFm k).aestronglyMeasurable (w k)
      (Filter.Eventually.of_forall (hFb k))
    have hIs : Summable (fun k=>∫x,‖F k x‖∂μ) :=by
      apply hws.of_norm_bounded
      intro k
      rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg fun _=>norm_nonneg _)]
      calc
        _≤∫_:Ω,w k∂μ:=integral_mono (hFi k).norm (integrable_const _) (hFb k)
        _=w k:=by simp
    exact (integral_tsum_of_summable_integral_norm hFi hIs).symm
  have hrow (x:Ω) : (∫z,G x z∂μ)=∑'k,w k*(f k x*conj (a k)).re :=by
    rw [hcomm (fun k z=>w k*(f k x*conj (f k z)).re)
      (fun k=>by fun_prop) (fun k z=>hbound k _ _ (hfb k x) (hfb k z))]
    apply tsum_congr
    intro k
    rw [integral_const_mul]
    have hic : Integrable (fun z=>conj (f k z)) μ := Integrable.of_bound (by fun_prop) 1
      (Filter.Eventually.of_forall fun z=>by simpa only [Complex.norm_conj] using hfb k z)
    have hci:Integrable (fun z=>f k x*conj (f k z)) μ:=hic.const_mul (f k x)
    have hre := integral_re hci
    change (∫z,(f k x*conj (f k z)).re∂μ)=(∫z,f k x*conj (f k z)∂μ).re at hre
    rw [hre,integral_const_mul,integral_conj]
  have hmean : (∫z,∫z',G z z'∂μ∂μ)=∑'k,w k*(a k*conj (a k)).re :=by
    simp_rw [hrow]
    rw [hcomm (fun k z=>w k*(f k z*conj (a k)).re)
      (fun k=>by fun_prop) (fun k z=>hbound k _ _ (hfb k z) (hab k))]
    apply tsum_congr
    intro k
    rw [integral_const_mul]
    have hci:Integrable (fun z=>f k z*conj (a k)) μ:=(hfi k).mul_const (conj (a k))
    have hre := integral_re hci
    change (∫z,(f k z*conj (a k)).re∂μ)=(∫z,f k z*conj (a k)∂μ).re at hre
    rw [hre,integral_mul_const]
  have hcenter (x y:Ω) : G x y-(∫z,G x z∂μ)-(∫z,G y z∂μ)+(∫z,∫z',G z z'∂μ∂μ)=
      ∑'k,w k*((f k x-a k)*conj (f k y-a k)).re :=by
    have hxy : Summable (fun k=>w k*(f k x*conj (f k y)).re):=hws.of_norm_bounded
      (fun k=>hbound k _ _ (hfb k x) (hfb k y))
    have hxa : Summable (fun k=>w k*(f k x*conj (a k)).re):=hws.of_norm_bounded
      (fun k=>hbound k _ _ (hfb k x) (hab k))
    have hya : Summable (fun k=>w k*(f k y*conj (a k)).re):=hws.of_norm_bounded
      (fun k=>hbound k _ _ (hfb k y) (hab k))
    have haa : Summable (fun k=>w k*(a k*conj (a k)).re):=hws.of_norm_bounded
      (fun k=>hbound k _ _ (hab k) (hab k))
    rw [hrow,hrow,hmean]
    change (∑'k,w k*(f k x*conj (f k y)).re)-(∑'k,w k*(f k x*conj (a k)).re)-
      (∑'k,w k*(f k y*conj (a k)).re)+(∑'k,w k*(a k*conj (a k)).re)=_
    rw [←hxy.tsum_sub hxa,←(hxy.sub hxa).tsum_sub hya,←((hxy.sub hxa).sub hya).tsum_add haa]
    apply tsum_congr
    intro k
    simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im,Complex.sub_re,Complex.sub_im]
    ring
  have hv (k:ι) (x:Ω) : ‖f k x-a k‖≤2:=
    (norm_sub_le _ _).trans (by linarith [hfb k x,hab k])
  dsimp only
  refine ⟨hcenter,hv,?_⟩
  intro N hN X
  change -2*(∑'k,w k)≤(N:ℝ)⁻¹*∑i:Fin N,∑j:Fin N,
    if i<j then G (X i) (X j)-(∫z,G (X i) z∂μ)-(∫z,G (X j) z∂μ)+(∫z,∫z',G z z'∂μ∂μ) else 0
  simp_rw [hcenter]
  exact SummableGramEnergyBound N hN w (fun k i=>f k (X i)-a k) hw hws (fun k i=>hv k (X i))
