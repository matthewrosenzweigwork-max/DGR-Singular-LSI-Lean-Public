module

public import Tablet.NormalizedTiltInverse
public import Tablet.BoundedDensityComparison

@[expose] public section
open MeasureTheory
-- [TABLET NODE: InverseBoundedTiltLogSobolevTransport]
theorem InverseBoundedTiltLogSobolevTransport {Ω:Type*}[MeasurableSpace Ω]
    (μ:Measure Ω)[IsProbabilityMeasure μ](w f e:Ω→ℝ)(l u C:ℝ)
    (hl:0<l)(hC:0≤C)(hw:Measurable w)(hb:∀ᵐx∂μ,l≤w x∧w x≤u)
    (hf:Measurable f)(hfb:∃B:ℝ,∀ᵐx∂NormalizedTilt μ w,|f x|≤B)
    (he:Measurable e)(hen:∀ᵐx∂NormalizedTilt μ w,0≤e x)
    (hei:Integrable e (NormalizedTilt μ w))
    (hLSI:Entropy (NormalizedTilt μ w) (fun x=>f x^2)≤C*(∫x,e x∂NormalizedTilt μ w)) :
    Entropy μ (fun x=>f x^2)≤(u/l)*C*(∫x,e x∂μ) := by
-- BODY
  have hlu:l≤u:=by obtain ⟨x,hx⟩:=hb.exists;exact hx.1.trans hx.2
  have hu:0<u:=hl.trans_le hlu
  have hn:∀ᵐx∂μ,0≤w x:=hb.mono fun x hx=>hl.le.trans hx.1
  have hbt:=BoundedTiltBounds μ w l u hl hw hb
  have hZ:0<∫x,w x∂μ:=hl.trans_le hbt.2.1
  haveI:IsProbabilityMeasure (NormalizedTilt μ w):=(TiltNormalization μ w hw hn hbt.1 hZ).1
  have hac:(NormalizedTilt μ w)≪μ:=withDensity_absolutelyContinuous μ _
  have hib:∀ᵐx∂NormalizedTilt μ w,(1/u)≤1/w x∧1/w x≤1/l:=by
    filter_upwards [hb.filter_mono hac.ae_le] with x hx
    exact ⟨one_div_le_one_div_of_le (hl.trans_le hx.1) hx.2,
      one_div_le_one_div_of_le hl hx.1⟩
  let ν := NormalizedTilt μ w
  let b : Ω → ℝ := fun x => 1 / w x
  have hbp : 0 < 1/u := one_div_pos.mpr hu
  have hbu : 0 ≤ 1/l := (one_div_pos.mpr hl).le
  have hbm : Measurable b := measurable_const.div hw
  have hd := BoundedDensityComparison ν b f e (1/u) (1/l) hbp hbm hib
    hf hfb he hen hei
  have hbZ : 0 < ∫x,b x∂ν := hbp.trans_le
    (BoundedTiltBounds ν b (1/u) (1/l) hbp hbm hib).2.1
  have hh : Entropy (NormalizedTilt ν b) (fun x=>f x^2) ≤
      ((1/l)/(1/u))*C*(∫x,e x∂NormalizedTilt ν b) := by
    calc
      _ ≤ ((1/l)/(∫x,b x∂ν))*Entropy ν (fun x=>f x^2) := hd.2.1
      _ ≤ ((1/l)/(∫x,b x∂ν))*(C*(∫x,e x∂ν)) :=
        mul_le_mul_of_nonneg_left hLSI (div_nonneg hbu hbZ.le)
      _ ≤ _ := by
        have hE := mul_le_mul_of_nonneg_left hd.2.2.1
          (mul_nonneg (div_nonneg hbu hbp.le) hC)
        have hfactor : ((1/l)/(1/u))*C*(((1/u)/(∫x,b x∂ν))*(∫x,e x∂ν)) =
            ((1/l)/(∫x,b x∂ν))*(C*(∫x,e x∂ν)) := by
          field_simp [hbp.ne']
        rwa [hfactor] at hE
  change Entropy (NormalizedTilt (NormalizedTilt μ w) (fun x=>1/w x))
    (fun x=>f x^2) ≤ ((1/l)/(1/u))*C*
      (∫x,e x∂NormalizedTilt (NormalizedTilt μ w) (fun x=>1/w x)) at hh
  rw[NormalizedTiltInverse μ w l u hl hw hb] at hh
  have hid:(1/l)/(1/u)=u/l:=by field_simp[hl.ne',hu.ne']
  rwa[hid] at hh
