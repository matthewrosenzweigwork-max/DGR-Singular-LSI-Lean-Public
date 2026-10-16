module

public import Tablet.RieszThermalConditionalEntropyBound
public import Tablet.RieszCenteredSquareEntropyLower
public import Tablet.CenteredUniformPoincare
public import Tablet.CenteredCanonicalLogSobolevTransport
public import Tablet.ConfigurationEntropyDefectRemoval
public import Tablet.InverseBoundedTiltLogSobolevTransport

@[expose] public section
open MeasureTheory
-- [TABLET NODE: UniformLogSobolevFromPartitionBounds]
theorem UniformLogSobolevFromPartitionBounds (d:ℕ) (hd:2≤d) (s a B l u:ℝ)
    (hs:0≤s) (hsd:s≤(d:ℝ)-2) (hL:s<(d:ℝ)/2) (ha:0<a) (hB:0≤B)
    (hl:0<l) (hl1:l≤1) (hu:1≤u)
    (hstatic:∀T M:ℝ,0≤T→1≤M→∃K:ℝ,1≤K ∧∀N:ℕ,2≤N→
      ∀t ε:ℝ,0≤t→t≤T→0≤ε→∀rl:ℝ,∀r:BoundedBackground d rl M,
      1≤(∫X,Real.exp (-t*CenteredPairEnergy (RieszKernel d s a ε) r.density X)
        ∂Measure.pi (fun _:Fin N=>(volume:Measure (UnitAddTorus (Fin d))).withDensity
          (fun z=>ENNReal.ofReal (r.density z)))) ∧
      (∫X,Real.exp (-t*CenteredPairEnergy (RieszKernel d s a ε) r.density X)
        ∂Measure.pi (fun _:Fin N=>(volume:Measure (UnitAddTorus (Fin d))).withDensity
          (fun z=>ENNReal.ofReal (r.density z))))≤K) :
    ∃rate:ℝ,0<rate ∧∀N:ℕ,2≤N→∀β:ℝ,0≤β→β≤B→
      ∀q:BoundedBackground d l u,∀ε:ℝ,0<ε→∀f:Configuration d N→ℝ,f∈SmoothCore d N→
        Entropy (CanonicalLaw (N:=N) (RieszKernel d s a ε) q.density β) (fun X=>f X^2)
        ≤(2/rate)*PhysicalEnergy (CanonicalLaw (N:=N) (RieszKernel d s a ε) q.density β) f := by
-- BODY
  classical
  have centered_defect_join (d N:ℕ) (P:Measure (Configuration d N))[IsProbabilityMeasure P]
      (sigma K lambdaRate:ℝ) (hsigma:0<sigma) (hK:1≤K) (hlambda:0<lambdaRate)
      (J:(Configuration d N→ℝ)→ℝ)
      (hupper:∀f:Configuration d N→ℝ,f∈SmoothCore d N→J f≤(2/sigma)*PhysicalEnergy P f)
      (hlower:∀f:Configuration d N→ℝ,f∈SmoothCore d N→
        Entropy P (fun X=>f X^2)≤2*J f+2*Real.log K*(∫X,f X^2∂P))
      (hpi:∀f:Configuration d N→ℝ,f∈SmoothCore d N→
        ProbabilityTheory.variance f P≤lambdaRate⁻¹*PhysicalEnergy P f) :
      let rho:=2/(16*(4/sigma)+(16*(2*Real.log K)+48)*lambdaRate⁻¹)
      0<rho ∧ ∀f:Configuration d N→ℝ,f∈SmoothCore d N→
        Entropy P (fun X=>f X^2)≤(2/rho)*PhysicalEnergy P f := by
    apply ConfigurationEntropyDefectRemoval d N P (4/sigma) (2*Real.log K) lambdaRate
      (div_nonneg (by norm_num) hsigma.le) (mul_nonneg (by norm_num) (Real.log_nonneg hK)) hlambda ?_ hpi
    intro f hf
    have h:=hlower f hf
    have hu:=mul_le_mul_of_nonneg_left (hupper f hf) (by norm_num : (0:ℝ)≤2)
    have hid:2*((2/sigma)*PhysicalEnergy P f)=(4/sigma)*PhysicalEnergy P f:=by ring
    rw[hid] at hu
    linarith
  haveI:IsProbabilityMeasure (volume:Measure (AddCircle (1:ℝ))):=by
    rw[AddCircle.volume_eq_smul_haarAddCircle];simp;infer_instance
  haveI:IsProbabilityMeasure (volume:Measure (UnitAddTorus (Fin d))):=inferInstance
  obtain ⟨c,hc,σ,hσ,hthermal⟩:=RieszThermalConditionalEntropyBound d hd s a B l u hs hsd hL ha hB hl hl1 hu
  let G:=∫x,|RieszKernel d s a 0 x|∂(volume:Measure (UnitAddTorus (Fin d)))
  let M:=u*Real.exp (B*(c+u*G))
  let H:=M*G
  have hG:0≤G:=integral_nonneg fun x=>abs_nonneg _
  have hM:1≤M:=one_le_mul_of_one_le_of_one_le hu (Real.one_le_exp_iff.mpr
    (mul_nonneg hB (add_nonneg hc (mul_nonneg (by linarith) hG))))
  have hH:0≤H:=mul_nonneg (by linarith) hG
  obtain ⟨lamBar,hlambda,hpi⟩:=CenteredUniformPoincare d hd s a B l u H hs hsd ha hB hl hl1 hu hH
  obtain ⟨K,hK,hpart⟩:=hstatic (3*B) M (by positivity) hM
  let den:=16*(4/σ)+(16*(2*Real.log K)+48)*lamBar⁻¹
  have hden:0<den:=by
    have hlog:0≤Real.log K:=Real.log_nonneg hK
    have hfirst:0<16*(4/σ):=by positivity
    have hsecond:0≤(16*(2*Real.log K)+48)*lamBar⁻¹:=by positivity
    exact add_pos_of_pos_of_nonneg hfirst hsecond
  let ρbar:=2/den
  have hρ:0<ρbar:=div_pos (by norm_num) hden
  let rate:=ρbar*Real.exp (-2*B*H)
  refine ⟨rate,mul_pos hρ (Real.exp_pos _),?_⟩
  intro N hN β hβ hβB q ε hε f hf
  obtain ⟨r,hrb,hEL,hP,hKrow,hrowupper⟩:=hthermal N hN β hβ hβB q ε hε
  let g:=RieszKernel d s a ε
  let h:=BackgroundPotential g r.density
  let Z:=∫z,q.density z*Real.exp (-β*h z)
  let P:=CenteredCanonicalLaw (N:=N) g r.density β
  let Kr:=fun (i:Fin N) (X:Configuration d N)=>NormalizedTilt
    ((volume:Measure (UnitAddTorus (Fin d))).withDensity (fun z=>ENNReal.ofReal (r.density z)))
    (fun z=>Real.exp (-β/(N:ℝ)*(∑j:Fin N,if j=i then 0 else CenteredKernel g r.density z (X j))))
  haveI:IsProbabilityMeasure P:=hP
  obtain ⟨c₁,hc₁,hfound⟩:=RieszL1Foundation d hd s a hs (by linarith) ha
  have hF:=hfound ε hε.le
  have hdef : h = (fun x => ∫ y, g (x-y)*r.density y) := by
    funext x
    simp only [h, BackgroundPotential, convolution, ContinuousLinearMap.mul_apply', mul_comm]
  have hhm:Measurable h:=by
    rw [hdef]
    exact ((hF.1.comp (measurable_fst.sub measurable_snd)).mul (r.measurable.comp measurable_snd)).stronglyMeasurable.integral_prod_right.measurable
  have hhb:∀ᵐx∂volume,|h x|≤H:=Filter.Eventually.of_forall hrb
  have hwm:Measurable (fun x=>q.density x*Real.exp (-β*h x)):=q.measurable.mul (hhm.const_mul (-β)).exp
  have hwb:∀ᵐx∂volume,l*Real.exp (-B*H)≤q.density x*Real.exp (-β*h x) ∧
      q.density x*Real.exp (-β*h x)≤u*Real.exp (B*H):=by
    filter_upwards[q.bounds,hhb] with x hx hh
    have hb: -B*H≤-β*h x ∧ -β*h x≤B*H:=by
      have h1:=mul_le_mul_of_nonneg_left (abs_le.mp hh).1 hβ
      have h2:=mul_le_mul_of_nonneg_left (abs_le.mp hh).2 hβ
      have h3:=mul_le_mul_of_nonneg_right hβB hH
      constructor <;> nlinarith
    exact ⟨mul_le_mul hx.1 (Real.exp_le_exp.mpr hb.1) (Real.exp_pos _).le (hl.le.trans hx.1),
      mul_le_mul hx.2 (Real.exp_le_exp.mpr hb.2) (Real.exp_pos _).le (by linarith)⟩
  have hZ:0<Z:=(mul_pos hl (Real.exp_pos _)).trans_le
    (BoundedTiltBounds volume _ _ _ (mul_pos hl (Real.exp_pos _)) hwm hwb).2.1
  let J:=fun f:Configuration d N→ℝ=>∑i:Fin N,∫X,Entropy (Kr i X) (fun z=>f (Replacement X i z)^2)∂P
  have hupp:∀f:Configuration d N→ℝ,f∈SmoothCore d N→J f≤(2/σ)*PhysicalEnergy P f:=by
    intro f hf;exact (hrowupper f hf).2
  have hlo:∀f:Configuration d N→ℝ,f∈SmoothCore d N→Entropy P (fun X=>f X^2)≤2*J f+2*Real.log K*(∫X,f X^2∂P):=by
    intro f hf
    have hcal:=(ConfigurationCalculus d N).2.2.2 f hf
    obtain ⟨R,hR⟩:=hcal.2.2.1
    have hv:=RieszCenteredSquareEntropyLower d N hd hN s a ε l u (l*Real.exp (-2*B*H)) M β H Z
      hs (by linarith) ha hε q r hβ hH hZ hhm hhb hEL f hcal.2.1 R hR
    have hp1:=hpart N hN β ε hβ (by linarith) hε.le _ r
    have hp3:=hpart N hN (3*β) ε (by positivity) (by nlinarith) hε.le _ r
    have hlog1:=Real.log_le_log (lt_of_lt_of_le zero_lt_one hp1.1) hp1.2
    have hlog3:=Real.log_le_log (lt_of_lt_of_le zero_lt_one hp3.1) hp3.2
    have hlogs:=add_le_add hlog1 hlog3
    have hmass:0≤∫X,f X^2∂P:=integral_nonneg fun X=>sq_nonneg _
    have hmul:=mul_le_mul_of_nonneg_right hlogs hmass
    exact hv.trans (by dsimp only; change 2*J f+_≤2*J f+_; nlinarith [hmul])
  have hpif:∀f:Configuration d N→ℝ,f∈SmoothCore d N→ProbabilityTheory.variance f P≤lamBar⁻¹*PhysicalEnergy P f:=by
    intro f hf;exact hpi N hN β hβ hβB q ε hε _ _ Z r hZ hhm hhb hEL f hf
  have ht:=centered_defect_join d N P σ K lamBar hσ hK hlambda J hupp hlo hpif
  have hcenter:∀f:Configuration d N→ℝ,f∈SmoothCore d N→Entropy P (fun X=>f X^2)≤(2/ρbar)*PhysicalEnergy P f:=ht.2
  exact (CenteredCanonicalLogSobolevTransport d N hd hN s a B l u _ _ β ε H Z ρbar
    hs (by linarith) ha hε hβ hβB hH hZ hρ q r hhm hhb hEL hcenter).2 f hf
