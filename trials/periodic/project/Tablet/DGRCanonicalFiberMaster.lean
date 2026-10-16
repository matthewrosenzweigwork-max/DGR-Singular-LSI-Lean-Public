import Tablet.CanonicalFiberFourRegimeTail
import Tablet.DGRConditionalMasterLayerCake
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
open MeasureTheory
open scoped InnerProductSpace
universe u
-- [TABLET NODE: DGRCanonicalFiberMaster]
/-- Actual canonical master with deliberately coarsened H=D=F; no probability premise. -/
theorem DGRCanonicalFiberMaster : ∃L:ℝ,1≤L ∧
    ∀{Ω:Type u}[MeasurableSpace Ω](μ:Measure Ω)[IsProbabilityMeasure μ]
      (N:ℕ)(hN:0<N)(Xi:(Fin N→Ω)→ℝ)
      (hXi:Measurable Xi)(q:ℝ→Ω→Ω→ℝ)(A m:ℝ→ℝ)(F U:ℝ),
      1≤U → 0<F → F≤1/L →
      (∀v,U≤v → 0<A v ∧ Measurable (fun p:Ω×Ω=>q v p.1 p.2) ∧
        (∀x y,|q v x y|≤A v) ∧ (∀x,∫y,q v x y∂μ=0) ∧
        (∀y,∫x,q v x y∂μ=0) ∧ (∀x,∫y,(q v x y)^2∂μ≤F^2) ∧
        (∀y,∫x,(q v x y)^2∂μ≤F^2)) →
      (∀v,U≤v → ∀ᵐX∂Measure.pi (fun _:Fin N=>μ),v≤Xi X →
        v≤-(∑i,∑j,if i=j then (0:ℝ) else q v (X i) (X j))/(2*(N:ℝ))) →
      (∀v,U≤v → ∀ᵐX∂Measure.pi (fun _:Fin N=>μ),
        -(∑i,∑j,if i=j then (0:ℝ) else q v (X i) (X j))/(2*(N:ℝ))≤m v) →
      (∀v,U≤v → 2*L^2*min v (m v)*(1+A v)≤(N:ℝ)) →
      let ν:=Measure.pi (fun _:Fin N=>μ)
      let R:=fun v (X:Fin N→Ω)=>∑i,∑j,if i=j then (0:ℝ) else q v (X i) (X j)
      (∀v,U≤v →
        Real.sqrt (∫p:Ω×Ω,(q v p.1 p.2)^2∂μ.prod μ)≤F ∧
        (∀f:Ω→ℝ,Measurable f→MemLp f 2 μ→
          (∫x,(∫y,q v x y*f y∂μ)^2∂μ)≤F^2*(∫y,(f y)^2∂μ)) ∧
        (∀f g:Ω→ℝ,Measurable f→Measurable g→∀hf:MemLp f 2 μ,∀hg:MemLp g 2 μ,
          |∫x,∫y,q v x y*f x*g y∂μ∂μ|≤F*‖hf.toLp f‖*‖hg.toLp g‖) ∧
        ν.real {X | 2*(N:ℝ)*v≤|R v X|}≤
          L*Real.exp (-(1/L)*min (min (4*v^2/F^2) (2*v/F))
            (min ((4*(N:ℝ)*v^2/F^2)^((3:ℝ)⁻¹)) ((2*(N:ℝ)*v/A v)^((2:ℝ)⁻¹))))) ∧
      (∀v,U≤v → ν.real {X | v≤Xi X}≤L*Real.exp (-2*v)) ∧
      Integrable (fun X=>Real.exp (Xi X)) ν ∧
      (∫X,Real.exp (Xi X)∂ν)≤Real.exp U+L := by
-- BODY
  obtain ⟨L,hL,hTail⟩:=CanonicalFiberFourRegimeTail
  refine ⟨L,hL,?_⟩
  intro Ω _ μ _ N hN Xi hXi q A m F U hU hF hsmall hfamily hM1 hM2 hgrowth
  have KernelFiberHilbertOperatorBound
      (μ:Measure Ω)[IsProbabilityMeasure μ](q:Ω→Ω→ℝ)
      (hq:Measurable (fun p:Ω×Ω=>q p.1 p.2))(A F:ℝ)(hA:0≤A)(hF:0≤F)
      (hb:∀x y,|q x y|≤A)
      (hrow:∀x,(∫y,(q x y)^2∂μ)≤F^2)
      (hcol:∀y,(∫x,(q x y)^2∂μ)≤F^2):
      (∫x,∫y,(q x y)^2∂μ∂μ)≤F^2 ∧
      Real.sqrt (∫p:Ω×Ω,(q p.1 p.2)^2∂μ.prod μ)≤F ∧
      (∀f:Ω→ℝ,Measurable f→MemLp f 2 μ→
        (∫x,(∫y,q x y*f y∂μ)^2∂μ)≤F^2*(∫y,(f y)^2∂μ)) ∧
      (∀f g:Ω→ℝ,Measurable f→Measurable g→∀hf:MemLp f 2 μ,∀hg:MemLp g 2 μ,
        |∫x,∫y,q x y*f x*g y∂μ∂μ|≤F*‖hf.toLp f‖*‖hg.toLp g‖):=by
    have norm_square (f:Ω→ℝ)(hf:MemLp f 2 μ):‖hf.toLp f‖^2=∫y,(f y)^2∂μ:=by
      rw [←real_inner_self_eq_norm_sq,L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with y hy
      simp only [hy,real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
    have inner_integral (f g:Ω→ℝ)(hf:MemLp f 2 μ)(hg:MemLp g 2 μ):
        (∫y,f y*g y∂μ)=inner ℝ (hf.toLp f) (hg.toLp g):=by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with y hfy hgy
      simp only [hfy,hgy]
      change f y*g y=g y*f y
      ring
    have hqm(x):Measurable (q x):=hq.comp (measurable_const.prodMk measurable_id)
    have hqL(x):MemLp (q x) 2 μ:=MemLp.of_bound (hqm x).aestronglyMeasurable A
      (Filter.Eventually.of_forall fun y=>by simpa only [Real.norm_eq_abs] using hb x y)
    have hqn(x):‖(hqL x).toLp (q x)‖≤F:=by
      have hs:=hrow x
      rw [←norm_square (q x) (hqL x)] at hs
      nlinarith [norm_nonneg ((hqL x).toLp (q x))]
    let Q:=fun x=>∫y,(q x y)^2∂μ
    have hQm:Measurable Q:=(hq.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable
    have hQi:Integrable Q μ:=Integrable.of_bound hQm.aestronglyMeasurable (F^2)
      (Filter.Eventually.of_forall fun x=>by
        rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg fun y=>sq_nonneg (q x y))]
        exact hrow x)
    have hHS:(∫x,∫y,(q x y)^2∂μ∂μ)≤F^2:=by
      calc
        _≤∫_:Ω,F^2∂μ:=integral_mono hQi (integrable_const _) hrow
        _=F^2:=by simp
    have hprod:Integrable (fun p:Ω×Ω=>(q p.1 p.2)^2) (μ.prod μ):=
      Integrable.of_bound (hq.pow_const 2).aestronglyMeasurable (A^2)
        (Filter.Eventually.of_forall fun p=>by
          rw [Real.norm_eq_abs,abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (hb p.1 p.2) 2)
    have hHSnorm:Real.sqrt (∫p:Ω×Ω,(q p.1 p.2)^2∂μ.prod μ)≤F:=by
      apply (Real.sqrt_le_left hF).mpr
      rw [integral_prod _ hprod]
      exact hHS
    have transform(f:Ω→ℝ)(hfm:Measurable f)(hf:MemLp f 2 μ):
        let Tf:=fun x=>∫y,q x y*f y∂μ
        Measurable Tf ∧ ∃hL:MemLp Tf 2 μ, ‖hL.toLp Tf‖≤F*‖hf.toLp f‖:=by
      dsimp only
      let Tf:=fun x=>∫y,q x y*f y∂μ
      have hm:Measurable Tf:=(hq.mul (hfm.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable
      have hbnd(x):‖Tf x‖≤F*‖hf.toLp f‖:=by
        change |∫y,q x y*f y∂μ|≤F*‖hf.toLp f‖
        rw [inner_integral (q x) f (hqL x) hf]
        exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hqn x) (norm_nonneg _))
      have hL:MemLp Tf 2 μ:=MemLp.of_bound hm.aestronglyMeasurable (F*‖hf.toLp f‖) (Filter.Eventually.of_forall hbnd)
      refine ⟨hm,hL,?_⟩
      have hi:(∫x,(Tf x)^2∂μ)≤(F*‖hf.toLp f‖)^2:=by
        calc
          _≤∫_:Ω,(F*‖hf.toLp f‖)^2∂μ:=integral_mono hL.integrable_sq (integrable_const _)
            (fun x=>by simpa only [Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (norm_nonneg _) (hbnd x) 2)
          _=(F*‖hf.toLp f‖)^2:=by simp
      rw [←norm_square Tf hL] at hi
      nlinarith [norm_nonneg (hL.toLp Tf),mul_nonneg hF (norm_nonneg (hf.toLp f))]
    refine ⟨hHS,hHSnorm,?_,?_⟩
    · intro f hfm hf
      obtain ⟨hm,hL,hn⟩:=transform f hfm hf
      rw [←norm_square _ hL,←norm_square f hf]
      calc
        _≤(F*‖hf.toLp f‖)^2:=pow_le_pow_left₀ (norm_nonneg _) hn 2
        _=F^2*‖hf.toLp f‖^2:=mul_pow _ _ _
    · intro f g hfm hgm hf hg
      obtain ⟨hm,hL,hn⟩:=transform g hgm hg
      have he:(∫x,∫y,q x y*f x*g y∂μ∂μ)=∫x,f x*(∫y,q x y*g y∂μ)∂μ:=by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x=>by
          change (∫y,q x y*f x*g y∂μ)=f x*(∫y,q x y*g y∂μ)
          rw [←integral_const_mul]
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun y=>by ring
      rw [he,inner_integral f _ hf hL]
      calc
        _≤‖hf.toLp f‖*‖hL.toLp (fun x=>∫y,q x y*g y∂μ)‖:=abs_real_inner_le_norm _ _
        _≤‖hf.toLp f‖*(F*‖hg.toLp g‖):=mul_le_mul_of_nonneg_left hn (norm_nonneg _)
        _=F*‖hf.toLp f‖*‖hg.toLp g‖:=by ring
  classical
  let ν:=Measure.pi (fun _:Fin N=>μ)
  let R:=fun v (X:Fin N→Ω)=>∑i,∑j,if i=j then (0:ℝ) else q v (X i) (X j)
  have hNp:0<(N:ℝ):=Nat.cast_pos.mpr hN
  have hLp:0<L:=zero_lt_one.trans_le hL
  have hInv:1/L≤1:=(div_le_one hLp).mpr hL
  have hF1:F≤1:=hsmall.trans hInv
  have hFs:F^2≤1/L:=by
    have hsq:F^2≤F:=by nlinarith only [hF,hF1]
    exact hsq.trans hsmall
  have hraw (v:ℝ)(hv:U≤v):ν.real {X | 2*(N:ℝ)*v≤|R v X|}≤
      L*Real.exp (-(1/L)*min (min (4*v^2/F^2) (2*v/F))
        (min ((4*(N:ℝ)*v^2/F^2)^((3:ℝ)⁻¹)) ((2*(N:ℝ)*v/A v)^((2:ℝ)⁻¹)))):=by
    obtain ⟨hA,hq,hb,hc,hc',hfr,hfc⟩:=hfamily v hv
    have hvp:0<v:=zero_lt_one.trans_le (hU.trans hv)
    have ht:=hTail μ N hN (q v) hq (A v) F hA hF hb hc hc' hfr hfc (2*v) (by positivity)
    have he:{X:Fin N→Ω | 2*(N:ℝ)*v≤|R v X|}=
        {X:Fin N→Ω | 2*v≤|R v X/(N:ℝ)|}:=by
      ext X
      rw [Set.mem_setOf_eq,Set.mem_setOf_eq,abs_div,abs_of_pos hNp,le_div_iff₀ hNp]
      ring_nf
    change ν.real {X | 2*v≤|R v X/(N:ℝ)|}≤_ at ht
    rw [he]
    convert ht using 1 <;> ring_nf
  have hm:=DGRConditionalMasterLayerCake ν Xi hXi R A (fun _=>F) (fun _=>F)
    (fun _=>F) m (N:ℝ) L U hNp hL hU
    (fun v hv=>⟨(hfamily v hv).1,hF,hF,hF⟩) hM1 hM2
    (fun _ _=>⟨hFs,hFs,hsmall⟩) hgrowth hraw
  dsimp only
  refine ⟨?_,hm⟩
  intro v hv
  obtain ⟨hA,hq,hb,hc,hc',hfr,hfc⟩:=hfamily v hv
  obtain ⟨_,hHS,hnum,hbil⟩:=KernelFiberHilbertOperatorBound μ (q v) hq (A v) F hA.le hF.le hb hfr hfc
  exact ⟨hHS,hnum,hbil,hraw v hv⟩
