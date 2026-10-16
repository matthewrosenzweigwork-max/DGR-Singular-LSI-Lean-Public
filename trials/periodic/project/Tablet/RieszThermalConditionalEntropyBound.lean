module

public import Tablet.RieszThermalConditionalLogSobolev
public import Tablet.RieszCenteredRowStationarity
public import Tablet.ConditionalEntropyAggregation

@[expose] public section
open MeasureTheory
-- [TABLET NODE: RieszThermalConditionalEntropyBound]
theorem RieszThermalConditionalEntropyBound (d:ℕ)(hd:2≤d)(s a B l u:ℝ)
    (hs:0≤s)(hsd:s≤(d:ℝ)-2)(hL:s<(d:ℝ)/2)(ha:0<a)(hB:0≤B)
    (hl:0<l)(hl1:l≤1)(hu:1≤u) :
    ∃c:ℝ,0≤c ∧
      let G:=∫x,|RieszKernel d s a 0 x|∂(volume:Measure (UnitAddTorus (Fin d)))
      let M:=u*Real.exp (B*(c+u*G))
      let H:=M*G
      ∃σ:ℝ,0<σ ∧ ∀N:ℕ,2≤N→∀β:ℝ,0≤β→β≤B→
        ∀q:BoundedBackground d l u,∀ε:ℝ,0<ε→
          ∃r:BoundedBackground d (l*Real.exp (-2*B*H)) M,
            (∀x,|BackgroundPotential (RieszKernel d s a ε) r.density x|≤H) ∧
            (∀ᵐx∂volume,r.density x=q.density x*Real.exp
              (-β*BackgroundPotential (RieszKernel d s a ε) r.density x)/
              (∫z,q.density z*Real.exp (-β*BackgroundPotential (RieszKernel d s a ε) r.density z))) ∧
            let P:=CenteredCanonicalLaw (N:=N) (RieszKernel d s a ε) r.density β
            let K:=fun (i:Fin N)(X:Configuration d N)=>NormalizedTilt
              ((volume:Measure (UnitAddTorus (Fin d))).withDensity (fun z=>ENNReal.ofReal (r.density z)))
              (fun z=>Real.exp (-β/(N:ℝ)*(∑j:Fin N,if j=i then 0 else
                CenteredKernel (RieszKernel d s a ε) r.density z (X j))))
            IsProbabilityMeasure P ∧ (∀i X,IsProbabilityMeasure (K i X)) ∧
            ∀f:Configuration d N→ℝ,f∈SmoothCore d N→
              (∀i:Fin N,Integrable (fun X=>Entropy (K i X) (fun z=>f (Replacement X i z)^2)) P) ∧
              (∑i:Fin N,∫X,Entropy (K i X) (fun z=>f (Replacement X i z)^2)∂P)≤
                (2/σ)*PhysicalEnergy P f := by
-- BODY
  classical
  haveI : IsProbabilityMeasure (volume:Measure (AddCircle (1:ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle];simp;infer_instance
  haveI : IsProbabilityMeasure (volume:Measure (UnitAddTorus (Fin d))) := inferInstance
  obtain ⟨c,hc,σ,hσ,hthermal⟩:=RieszThermalConditionalLogSobolev d hd s a B l u hs hsd hL ha hB hl hl1 hu
  refine ⟨c,hc,σ,hσ,?_⟩
  intro N hN β hβ hβB q ε hε
  obtain ⟨r,hrb,hEL,hLSI⟩:=hthermal N hN β hβ hβB q ε hε
  refine ⟨r,hrb,hEL,?_⟩
  dsimp only
  let g:=RieszKernel d s a ε
  let G:=∫x,|RieszKernel d s a 0 x|∂(volume:Measure (UnitAddTorus (Fin d)))
  let M:=u*Real.exp (B*(c+u*G))
  let H:=M*G
  let h:=BackgroundPotential g r.density
  let Z:=∫z,q.density z*Real.exp (-β*h z)
  let P:=CenteredCanonicalLaw (N:=N) g r.density β
  let K:=fun (i:Fin N)(X:Configuration d N)=>NormalizedTilt
    ((volume:Measure (UnitAddTorus (Fin d))).withDensity (fun z=>ENNReal.ofReal (r.density z)))
    (fun z=>Real.exp (-β/(N:ℝ)*(∑j:Fin N,if j=i then 0 else CenteredKernel g r.density z (X j))))
  have hG:0≤G:=integral_nonneg fun x=>abs_nonneg _
  have hup:0<u:=lt_of_lt_of_le zero_lt_one hu
  have hH:0≤H:=mul_nonneg (mul_nonneg hup.le (Real.exp_pos _).le) hG
  obtain ⟨c₁,hc₁,hfound⟩:=RieszL1Foundation d hd s a hs (by linarith) ha
  have hF:=hfound ε hε.le
  have hgm:Measurable g:=hF.1
  have hhm:Measurable h:=by
    have hm : Measurable (fun x => ∫ y, g (x-y)*r.density y) :=
      ((hgm.comp (measurable_fst.sub measurable_snd)).mul (r.measurable.comp measurable_snd)).stronglyMeasurable.integral_prod_right.measurable
    change Measurable (fun x => ∫ y, r.density y * g (x-y))
    simpa only [mul_comm] using hm
  have hhb:∀ᵐx∂volume,|h x|≤H:=Filter.Eventually.of_forall hrb
  let ll:=l*Real.exp (-B*H)
  let uu:=u*Real.exp (B*H)
  have hll:0<ll:=mul_pos hl (Real.exp_pos _)
  have hwm:Measurable (fun x=>q.density x*Real.exp (-β*h x)):=q.measurable.mul (hhm.const_mul (-β)).exp
  have hwb:∀ᵐx∂volume,ll≤q.density x*Real.exp (-β*h x) ∧ q.density x*Real.exp (-β*h x)≤uu:=by
    filter_upwards [q.bounds,hhb] with x hx hh
    have hlo:-B*H≤-β*h x:=by
      have h1:=mul_le_mul_of_nonneg_left (abs_le.mp hh).2 hβ
      have h2:=mul_le_mul_of_nonneg_right hβB hH
      nlinarith
    have hhi:-β*h x≤B*H:=by
      have h1:=mul_le_mul_of_nonneg_left (abs_le.mp hh).1 hβ
      have h2:=mul_le_mul_of_nonneg_right hβB hH
      nlinarith
    exact ⟨mul_le_mul hx.1 (Real.exp_le_exp.mpr hlo) (Real.exp_pos _).le (hl.le.trans hx.1),
      mul_le_mul hx.2 (Real.exp_le_exp.mpr hhi) (Real.exp_pos _).le hup.le⟩
  have hZ:0<Z:=hll.trans_le (BoundedTiltBounds volume _ ll uu hll hwm hwb).2.1
  have hrow:=RieszCenteredRowStationarity d N hd hN s a ε l u (l*Real.exp (-2*B*H)) M β H Z
    hs (by linarith) ha hε q r hβ hH hZ hhm hhb hEL
  have hid:=CenteredConditionalIdentity d N hN l u (l*Real.exp (-2*B*H)) M β Z q r g hgm hZ hhm hEL
  have hKeq: K=(fun (i:Fin N)(X:Configuration d N)=>NormalizedTilt volume
    (fun z=>q.density z*Real.exp (-β*h z/(N:ℝ))*Real.exp (-ConditionalPotential g β X i z))) := by
    funext i X
    exact hid X i
  have hK:∀i X,IsProbabilityMeasure (K i X):=by rw[hKeq];exact hrow.1
  have hgl:∀ᵐx∂volume,-c₁≤g x:=Filter.Eventually.of_forall hF.2.2.2.2.1
  have hrecenter:=CenteredCanonicalRecenter d N hN l u (l*Real.exp (-2*B*H)) M β c₁ H Z q r g
    hgm hF.2.1 hβ hc₁ hgl hH hZ hhm hhb hEL
  let Pcan:=CanonicalLaw (N:=N) g q.density β
  haveI:IsProbabilityMeasure Pcan:=(GibbsNormalizerBounds d N hN l u q g hgm hF.2.1 c₁ β hc₁ hβ hgl).2.2.2
  let b:=fun X:Configuration d N=>Real.exp (-β/(N:ℝ)*∑i:Fin N,h (X i))
  have hbm:Measurable b:=
    (measurable_const.mul (Finset.measurable_fun_sum _ fun i _=>hhm.comp (measurable_pi_apply i))).exp
  have hbb:∀ᵐX∂Pcan,Real.exp (-β*H)≤b X ∧ b X≤Real.exp (β*H):=hrecenter.2
  have hbint:=BoundedTiltBounds Pcan b (Real.exp (-β*H)) (Real.exp (β*H)) (Real.exp_pos _) hbm hbb
  have hp:IsProbabilityMeasure P:=by
    rw [show P=NormalizedTilt Pcan b from hrecenter.1]
    exact (TiltNormalization Pcan b hbm (hbb.mono fun X hx=>(Real.exp_pos _).le.trans hx.1) hbint.1
      ((Real.exp_pos _).trans_le hbint.2.1)).1
  haveI:IsProbabilityMeasure P:=hp
  refine ⟨hp,hK,?_⟩
  intro f hf
  apply ConditionalEntropyAggregation d N P K hK ?_ σ hσ ?_ f hf
  · rw[hKeq]
    exact hrow.2
  · intro i X
    exact hLSI X i
