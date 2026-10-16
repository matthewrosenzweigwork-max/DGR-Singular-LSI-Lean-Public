import Tablet.ConfigurationCalculus
import Tablet.EntropyDefectRemoval
import Mathlib.Probability.Moments.Variance
open MeasureTheory
open scoped ContDiff
-- [TABLET NODE: ConfigurationEntropyDefectRemoval]
theorem ConfigurationEntropyDefectRemoval (d N:ℕ)(P:Measure (Configuration d N))
    [IsProbabilityMeasure P] (A B rate:ℝ)(hA:0≤A)(hB:0≤B)(hrate:0<rate)
    (hdef:∀f:Configuration d N→ℝ,f∈SmoothCore d N→
      Entropy P (fun X=>f X^2)≤A*PhysicalEnergy P f+B*(∫X,f X^2∂P))
    (hpi:∀f:Configuration d N→ℝ,f∈SmoothCore d N→
      ProbabilityTheory.variance f P≤rate⁻¹*PhysicalEnergy P f) :
    let ρ:=2/(16*A+(16*B+48)*rate⁻¹)
    0<ρ ∧ ∀f:Configuration d N→ℝ,f∈SmoothCore d N→
      Entropy P (fun X=>f X^2)≤(2/ρ)*PhysicalEnergy P f := by
-- BODY
  have hdata:∀f:Configuration d N→ℝ,f∈SmoothCore d N→
      Measurable f ∧ ∃C:ℝ,∀ᵐX∂P,|f X|≤C:=by
    intro f hf
    have hc:=(ConfigurationCalculus d N).2.2.2 f hf
    obtain ⟨C,hC⟩:=hc.2.2.1
    exact ⟨hc.2.1,C,Filter.Eventually.of_forall hC⟩
  have hcenter:∀f:Configuration d N→ℝ,f∈SmoothCore d N→
      (fun X=>f X-∫Y,f Y∂P)∈SmoothCore d N:=by
    intro f hf
    exact (show ContDiff ℝ ∞ (fun y=>f (ConfigurationLift d N y)) from hf).sub contDiff_const
  have hE:∀f:Configuration d N→ℝ,f∈SmoothCore d N→
      PhysicalEnergy P (fun X=>f X-∫Y,f Y∂P)=PhysicalEnergy P f:=by
    intro f hf
    have hg:CoordinateGradient (fun X=>f X-∫Y,f Y∂P)=CoordinateGradient f:=by
      funext X
      unfold CoordinateGradient
      simp only [fderiv_sub_const]
    unfold PhysicalEnergy
    rw[hg]
  have hp:∀f:Configuration d N→ℝ,f∈SmoothCore d N→
      (∫X,(f X-∫Y,f Y∂P)^2∂P)≤rate⁻¹*PhysicalEnergy P f:=by
    intro f hf
    rw[←ProbabilityTheory.variance_eq_integral ((hdata f hf).1.aemeasurable)]
    exact hpi f hf
  exact EntropyDefectRemoval P (fun f=>f∈SmoothCore d N) (PhysicalEnergy P) A B rate⁻¹
    hA hB (inv_pos.mpr hrate) hdata hcenter hE hdef hp
