import Tablet.RieszL1Foundation
import Tablet.CenteredCanonicalRecenter
import Tablet.InverseBoundedTiltLogSobolevTransport
import Tablet.ConfigurationCalculus
open MeasureTheory
-- [TABLET NODE: CenteredCanonicalLogSobolevTransport]
theorem CenteredCanonicalLogSobolevTransport (d N:ℕ) (hd:2≤d) (hN:2≤N)
    (s a B l u rl ru β ε H Z rho:ℝ)
    (hs:0≤s) (hsd:s<(d:ℝ)) (ha:0<a) (hε:0<ε)
    (hβ:0≤β) (hβB:β≤B) (hH:0≤H) (hZ:0<Z) (hrho:0<rho)
    (q:BoundedBackground d l u) (r:BoundedBackground d rl ru)
    (hh:Measurable (BackgroundPotential (RieszKernel d s a ε) r.density))
    (hhb:∀ᵐx∂volume,|BackgroundPotential (RieszKernel d s a ε) r.density x|≤H)
    (hEL:∀ᵐx∂volume,r.density x=q.density x*Real.exp
      (-β*BackgroundPotential (RieszKernel d s a ε) r.density x)/Z)
    (hLSI:∀f:Configuration d N→ℝ,f∈SmoothCore d N→
      Entropy (CenteredCanonicalLaw (N := N) (RieszKernel d s a ε) r.density β) (fun X=>f X^2)
        ≤(2/rho)*PhysicalEnergy (CenteredCanonicalLaw (N := N) (RieszKernel d s a ε) r.density β) f) :
    0<rho*Real.exp (-2*B*H) ∧ ∀f:Configuration d N→ℝ,f∈SmoothCore d N→
      Entropy (CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β) (fun X=>f X^2)
        ≤(2/(rho*Real.exp (-2*B*H)))*PhysicalEnergy
          (CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β) f := by
-- BODY
  classical
  obtain ⟨c,hc,hfound⟩:=RieszL1Foundation d hd s a hs hsd ha
  have hF:=hfound ε hε.le
  let g:=RieszKernel d s a ε
  let h:=BackgroundPotential g r.density
  let P:=CanonicalLaw (N:=N) g q.density β
  let b:Configuration d N→ℝ:=fun X=>Real.exp (-β/(N:ℝ)*∑i:Fin N,h (X i))
  have hgl:∀ᵐx∂volume,-c≤g x:=Filter.Eventually.of_forall hF.2.2.2.2.1
  have hrec:=CenteredCanonicalRecenter d N hN l u rl ru β c H Z q r g hF.1 hF.2.1 hβ hc hgl hH hZ hh hhb hEL
  haveI:IsProbabilityMeasure P:=(GibbsNormalizerBounds d N hN l u q g hF.1 hF.2.1 c β hc hβ hgl).2.2.2
  have hbm:Measurable b:=by
    exact (measurable_const.mul (Finset.measurable_fun_sum _ fun i _=>hh.comp (measurable_pi_apply i))).exp
  have hbt:=BoundedTiltBounds P b (Real.exp (-β*H)) (Real.exp (β*H)) (Real.exp_pos _) hbm hrec.2
  have hZb:0<∫X,b X∂P:=(Real.exp_pos _).trans_le hbt.2.1
  haveI:IsProbabilityMeasure (NormalizedTilt P b):=(TiltNormalization P b hbm
    (hrec.2.mono fun X hx=>(Real.exp_pos _).le.trans hx.1) hbt.1 hZb).1
  refine ⟨mul_pos hrho (Real.exp_pos _),?_⟩
  intro f hf
  have hcal:=(ConfigurationCalculus d N).2.2.2 f hf
  obtain ⟨C,hC⟩:=hcal.2.2.1
  obtain ⟨D,hD⟩:=hcal.2.2.2.2.1
  have hei:Integrable (fun X=>‖CoordinateGradient f X‖^2) (NormalizedTilt P b):=by
    apply (integrable_const D).mono' hcal.2.2.2.1.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun X=>by
      simpa only[Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖CoordinateGradient f X‖)] using hD X
  have hhLSI:Entropy (NormalizedTilt P b) (fun X=>f X^2)≤(2/rho)*PhysicalEnergy (NormalizedTilt P b) f:=by
    rw[←hrec.1];exact hLSI f hf
  have ht:=InverseBoundedTiltLogSobolevTransport P b f (fun X=>‖CoordinateGradient f X‖^2)
    (Real.exp (-β*H)) (Real.exp (β*H)) (2/rho) (Real.exp_pos _)
    (div_nonneg (by norm_num) hrho.le) hbm hrec.2 hcal.2.1
    ⟨C,Filter.Eventually.of_forall hC⟩ hcal.2.2.2.1
    (Filter.Eventually.of_forall fun X=>sq_nonneg _) hei hhLSI
  have hcoef:Real.exp (β*H)/Real.exp (-β*H)*(2/rho)≤2/(rho*Real.exp (-2*B*H)):=by
    rw[←Real.exp_sub]
    have hid:β*H-(-β*H)=2*β*H:=by ring
    rw[hid]
    have he:Real.exp (2*β*H)≤Real.exp (2*B*H):=Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hβB hH])
    have hright:2/(rho*Real.exp (-2*B*H))=Real.exp (2*B*H)*(2/rho):=by
      rw[div_mul_eq_div_div,div_eq_mul_inv (2/rho),←Real.exp_neg];ring_nf
    rw[hright]
    exact mul_le_mul_of_nonneg_right he (div_nonneg (by norm_num) hrho.le)
  exact ht.trans (mul_le_mul_of_nonneg_right hcoef (integral_nonneg fun X=>sq_nonneg _))
