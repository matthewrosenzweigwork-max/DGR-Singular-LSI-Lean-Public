module

public import Tablet.RieszThermalReferenceUniform
public import Tablet.CenteredConditionalIdentity
public import Tablet.CenteredConditionalLogSobolev
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section
open MeasureTheory
open scoped ContDiff
-- [TABLET NODE: RieszThermalConditionalLogSobolev]
theorem RieszThermalConditionalLogSobolev (d:ℕ)(hd:2≤d)(s a B l u:ℝ)
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
            ∀(X:Configuration d N)(i:Fin N),
              let K:=NormalizedTilt ((volume:Measure (UnitAddTorus (Fin d))).withDensity
                (fun z=>ENNReal.ofReal (r.density z)))
                (fun z=>Real.exp (-β/(N:ℝ)*(∑j:Fin N,if j=i then 0 else
                  CenteredKernel (RieszKernel d s a ε) r.density z (X j))))
              ∀f:UnitAddTorus (Fin d)→ℝ,TorusSmooth f→
                Entropy K (fun z=>f z^2)≤(2/σ)*(∫z,‖TorusGradient f z‖^2∂K) := by
-- BODY
  classical
  haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1:ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simpa using (inferInstance : IsProbabilityMeasure AddCircle.haarAddCircle)
  haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin d=>
      (volume : Measure (AddCircle (1:ℝ))))))
  obtain ⟨c,hc,href⟩:=RieszThermalReferenceUniform d hd s a hs (by linarith) ha
  let G:=∫x,|RieszKernel d s a 0 x|∂(volume:Measure (UnitAddTorus (Fin d)))
  let M:=u*Real.exp (B*(c+u*G))
  let H:=M*G
  have hG:0≤G:=integral_nonneg (fun x=>abs_nonneg _)
  have hup:0<u:=by linarith
  have hM:0≤M:=mul_nonneg hup.le (Real.exp_pos _).le
  have hH:0≤H:=mul_nonneg hM hG
  obtain ⟨σ,hσ,hlocal⟩:=CenteredConditionalLogSobolev d hd s a B l u H
    hs hsd hL ha hB hl hup hH
  refine ⟨c,hc,σ,hσ,?_⟩
  intro N hN β hβ hβB q ε hε
  obtain ⟨r,hrb,hEL⟩:=href B hB l u q ε β hε hβ hβB
  refine ⟨r,?_,?_,?_⟩
  · simpa only [BackgroundPotential, convolution, ContinuousLinearMap.mul_apply', mul_comm] using hrb
  · simpa only [BackgroundPotential, convolution, ContinuousLinearMap.mul_apply', mul_comm] using hEL
  let g:=RieszKernel d s a ε
  let h:=BackgroundPotential g r.density
  obtain ⟨c₁,hc₁,hF⟩:=RieszL1Foundation d hd s a hs (by linarith) ha
  have hgm:Measurable g:=(hF ε hε.le).1
  have hhm:Measurable h:=by
    have hm : Measurable (fun x => ∫ y, g (x-y)*r.density y) :=
      ((hgm.comp (measurable_fst.sub measurable_snd)).mul (r.measurable.comp measurable_snd)).stronglyMeasurable.integral_prod_right.measurable
    change Measurable (fun x => ∫ y, r.density y * g (x-y))
    simpa only [mul_comm] using hm
  have hhb:∀ᵐx∂volume,|h x|≤H:=by
    simpa only [h, g, BackgroundPotential, convolution, ContinuousLinearMap.mul_apply', mul_comm] using
      (Filter.Eventually.of_forall hrb : ∀ᵐ x ∂volume, |∫ y, RieszKernel d s a ε (x-y)*r.density y| ≤ H)
  let ll:=l*Real.exp (-B*H)
  let uu:=u*Real.exp (B*H)
  have hll:0<ll:=mul_pos hl (Real.exp_pos _)
  have hwm:Measurable (fun x=>q.density x*Real.exp (-β*h x)):=q.measurable.mul (hhm.const_mul (-β)).exp
  have hwb:∀ᵐx∂volume,ll≤q.density x*Real.exp (-β*h x) ∧
      q.density x*Real.exp (-β*h x)≤uu:=by
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
  have hZ:0<∫x,q.density x*Real.exp (-β*h x):=
    hll.trans_le (BoundedTiltBounds volume _ ll uu hll hwm hwb).2.1
  have hEL' : ∀ᵐ x ∂volume, r.density x = q.density x * Real.exp (-β*h x) /
      (∫ z, q.density z * Real.exp (-β*h z)) := by
    simpa only [h, g, BackgroundPotential, convolution, ContinuousLinearMap.mul_apply', mul_comm] using hEL
  have hid:=CenteredConditionalIdentity d N hN l u (l*Real.exp (-2*B*H)) M β _ q r g hgm hZ hhm hEL'
  intro X i
  dsimp only
  rw[hid X i]
  exact hlocal q.density h q.measurable hhm q.bounds hhb N hN β hβ hβB ε hε X i
