module

public import Tablet.EntropyVariational
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic

@[expose] public section
open MeasureTheory
-- [TABLET NODE: EntropyFiniteCentering]
theorem EntropyFiniteCentering {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Measurable f) (hfb : ∃C:ℝ,∀ᵐ x∂μ,|f x|≤C) (a:ℝ) :
    Entropy μ (fun x=>(f x+a)^2) ≤
      16*Entropy μ (fun x=>f x^2)+48*(∫ x,f x^2∂μ) := by
-- BODY
  have entropy_phi_le_square (u : ℝ) (hu : 0 ≤ u) :
    u*Real.log u-u+1 ≤ (u-1)^2 := by
    by_cases hz:u=0
    · simp [hz]
    have hp:0<u:=lt_of_le_of_ne hu (Ne.symm hz)
    have hh:=mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hp) hu
    nlinarith

  have entropy_phi_large (x b : ℝ) (hb : |b| ≤ 1) (hx : 1 ≤ x^2) :
    (x+b)^2*Real.log ((x+b)^2)-(x+b)^2+1 ≤
      16*x^2*(1+max (Real.log (x^2)) 0) := by
    have hb2 : b^2 ≤ 1 := by
      have h := (sq_le_sq₀ (abs_nonneg b) (show (0:ℝ)≤1 by norm_num)).mpr hb
      simpa using h
    have hu : (x+b)^2 ≤ 4*x^2 := by nlinarith [sq_nonneg (x-b)]
    have hxl : 0 ≤ Real.log (x^2) := Real.log_nonneg hx
    rw [max_eq_left hxl]
    by_cases hz:(x+b)^2=0
    · rw [hz]
      simp only [Real.log_zero, zero_mul, sub_zero, zero_add]
      nlinarith [mul_nonneg (sq_nonneg x) hxl]
    have hup:0<(x+b)^2:=lt_of_le_of_ne (sq_nonneg _) (Ne.symm hz)
    have hxp:0<x^2:=by linarith
    have hl := Real.log_le_log hup hu
    rw [Real.log_mul (by norm_num : (4:ℝ)≠0) hxp.ne'] at hl
    have h4 : Real.log (4:ℝ) ≤ 3 := by
      have h4 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
      norm_num at h4 ⊢
      exact h4
    have hlog : Real.log ((x+b)^2) ≤ 3+Real.log (x^2) := by linarith
    have hmul := mul_le_mul_of_nonneg_left hlog (sq_nonneg (x+b))
    have hmul2 := mul_le_mul_of_nonneg_right hu (show 0≤3+Real.log (x^2) by linarith)
    nlinarith [mul_nonneg (sq_nonneg x) hxl, sq_nonneg (x+b)]

  have entropy_phi_translate_one (x : ℝ) :
    (1+x)^2*Real.log ((1+x)^2)-(1+x)^2+1 ≤
      16*x^2*(1+max (Real.log (x^2)) 0) := by
    by_cases hx : x^2 ≤ 1
    · have hxabs : |x| ≤ 1 := by
        exact (sq_le_sq₀ (abs_nonneg x) (show (0:ℝ)≤1 by norm_num)).mp (by simpa using hx)
      have hxlo := (abs_le.mp hxabs).1
      have hxhi := (abs_le.mp hxabs).2
      have h2 : (x+2)^2 ≤ 9 := by nlinarith
      have hm := mul_le_mul_of_nonneg_left h2 (sq_nonneg x)
      have hp := entropy_phi_le_square ((1+x)^2) (sq_nonneg _)
      have heq : (((1+x)^2)-1)^2 = x^2*(x+2)^2 := by ring
      rw [heq] at hp
      have hpos : 0 ≤ x^2*max (Real.log (x^2)) 0 :=
        mul_nonneg (sq_nonneg x) (le_max_right _ _)
      nlinarith
    · have h := entropy_phi_large x 1 (by norm_num) (le_of_lt (lt_of_not_ge hx))
      simpa [add_comm] using h

  have entropy_phi_translate_bounded (x b : ℝ) (hb:|b|≤1) :
    (x+b)^2*Real.log ((x+b)^2)-(x+b)^2+1 ≤
      16*(1+x^2+x^2*max (Real.log (x^2)) 0) := by
    by_cases hx:x^2≤1
    · have hb2 : b^2≤1 := by
        have h := (sq_le_sq₀ (abs_nonneg b) (show (0:ℝ)≤1 by norm_num)).mpr hb
        simpa using h
      have hu : (x+b)^2≤4 := by nlinarith [sq_nonneg (x-b)]
      have hp:=entropy_phi_le_square ((x+b)^2) (sq_nonneg _)
      have hsq : (((x+b)^2)-1)^2≤9 := by nlinarith [sq_nonneg (x+b)]
      have hpos : 0≤x^2*max (Real.log (x^2)) 0 :=
        mul_nonneg (sq_nonneg x) (le_max_right _ _)
      nlinarith [sq_nonneg x]
    · have h:=entropy_phi_large x b hb (le_of_lt (lt_of_not_ge hx))
      nlinarith

  have positive_log_control
    (μ : Measure Ω) [IsProbabilityMeasure μ] (u : Ω → ℝ)
    (hu : Measurable u) (hn : ∀ᵐ x ∂μ, 0 ≤ u x)
    (hi : Integrable u μ) (hlog : Integrable (fun x => u x * Real.log (u x)) μ)
    (hpos : Integrable (fun x => u x * max (Real.log (u x)) 0) μ)
    (hm : 0 < ∫ x, u x ∂μ) (hm1 : (∫ x, u x ∂μ) ≤ 1) :
    (∫ x, u x * max (Real.log (u x)) 0 ∂μ) ≤ Entropy μ u + ∫ x, u x ∂μ := by
    let m := ∫ x,u x∂μ
    have hml : Real.log m ≤ 0 := Real.log_nonpos hm.le hm1
    have hphi := (EntropyVariational μ u hu hn hi hlog).1 m hm
    have hid (z:ℝ) : z*Real.log (z/m)=z*Real.log z-z*Real.log m := by
      by_cases hz:z=0
      · simp [hz]
      rw [Real.log_div hz hm.ne']; ring
    have hin : Integrable (fun x => u x*Real.log (u x/m)) μ :=
      (hlog.sub (hi.mul_const (Real.log m))).congr
        (Filter.Eventually.of_forall fun x => (hid (u x)).symm)
    have hp : ∀ᵐ x∂μ, u x*max (Real.log (u x)) 0 ≤ u x*Real.log (u x/m)+m := by
      filter_upwards [hn,hphi.1] with x hx hpx
      by_cases hl:Real.log (u x) ≤ 0
      · rw [max_eq_right hl]; nlinarith
      · rw [max_eq_left (le_of_not_ge hl),hid]
        nlinarith [mul_nonpos_of_nonneg_of_nonpos hx hml]
    have hh := integral_mono_ae hpos (hin.add (integrable_const m)) hp
    have heq : (∫ x,u x*Real.log (u x/m)+m ∂μ)=Entropy μ u+m := by
      rw [integral_add hin (integrable_const m)]
      have hidf : (fun x => u x*Real.log (u x/m)) =
          (fun x => u x*Real.log (u x)-u x*Real.log m) := funext fun x => hid (u x)
      rw [hidf,integral_sub hlog (hi.mul_const (Real.log m)),integral_mul_const]
      simp [Entropy,m]
    change (∫ x,u x*max (Real.log (u x)) 0∂μ) ≤ (∫ x,u x*Real.log (u x/m)+m ∂μ) at hh
    rw [heq] at hh
    exact hh

  have bounded_composition_integrable
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (hfb : ∃ C : ℝ, ∀ᵐ x∂μ, |f x|≤C)
    (h : ℝ → ℝ) (hh : Continuous h) : Integrable (fun x => h (f x)) μ := by
    obtain ⟨C,hC⟩:=hfb
    obtain ⟨K,hK⟩:=(isCompact_Icc (a := -|C|) (b := |C|)).bddAbove_image
      (f:=fun z:ℝ=> ‖h z‖) hh.norm.continuousOn
    apply Integrable.of_bound (hh.measurable.comp hf).aestronglyMeasurable K
    filter_upwards [hC] with x hx
    apply hK
    apply Set.mem_image_of_mem
    exact abs_le.mp (hx.trans (le_abs_self C))

  have bounded_square_moments
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (hfb : ∃ C : ℝ, ∀ᵐ x∂μ, |f x|≤C) :
    Integrable f μ ∧ Integrable (fun x=>f x^2) μ ∧
    Integrable (fun x=>f x^2*Real.log (f x^2)) μ ∧
    Integrable (fun x=>f x^2*max (Real.log (f x^2)) 0) μ := by
    refine ⟨bounded_composition_integrable μ f hf hfb id continuous_id,?_,?_,?_⟩
    · exact bounded_composition_integrable μ f hf hfb (fun z=>z^2) (continuous_id.pow 2)
    · exact bounded_composition_integrable μ f hf hfb (fun z=>z^2*Real.log (z^2))
        (Real.continuous_mul_log.comp (continuous_id.pow 2))
    · have hc : Continuous (fun z:ℝ=>z^2*max (Real.log (z^2)) 0) := by
        have heq : (fun z:ℝ=>z^2*max (Real.log (z^2)) 0)=
          (fun z:ℝ=>max (z^2*Real.log (z^2)) 0) := by
          funext z
          rw [mul_max_of_nonneg _ _ (sq_nonneg z),mul_zero]
        rw [heq]
        exact (Real.continuous_mul_log.comp (continuous_id.pow 2)).max continuous_const
      exact bounded_composition_integrable μ f hf hfb _ hc

  have entropy_scaling
    (μ : Measure Ω) (u : Ω → ℝ) (hi : Integrable u μ)
    (hlog : Integrable (fun x=>u x*Real.log (u x)) μ) (k : ℝ) :
    Entropy μ (fun x=>k*u x)=k*Entropy μ u := by
    have hid (z:ℝ) : (k*z)*Real.log (k*z)=
        k*(z*Real.log z)+(k*z)*Real.log k := by
      by_cases hk:k=0
      · simp [hk]
      by_cases hz:z=0
      · simp [hz]
      rw [Real.log_mul hk hz];ring
    have hidf : (fun x=>(k*u x)*Real.log (k*u x))=
        (fun x=>k*(u x*Real.log (u x))+(k*u x)*Real.log k) := funext fun x=>hid (u x)
    unfold Entropy
    rw [hidf,integral_add (hlog.const_mul k) ((hi.const_mul k).mul_const (Real.log k)),
      integral_const_mul,integral_mul_const,integral_const_mul,hid]
    ring

  have bounded_affine
    (μ : Measure Ω) (f : Ω → ℝ)
    (hfb : ∃ C : ℝ, ∀ᵐ x∂μ, |f x|≤C) (c a : ℝ) :
    ∃ C : ℝ, ∀ᵐ x∂μ, |c*f x+a|≤C := by
    obtain ⟨C,hC⟩:=hfb
    refine ⟨|c| * C+|a|,hC.mono fun x hx=>?_⟩
    calc
      |c*f x+a| ≤ |c*f x|+|a| := abs_add_le _ _
      _ = |c| * |f x|+|a| := by rw [abs_mul]
      _ ≤ |c| * C+|a| := by gcongr

  have normalized_center_one_entropy
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ᵐ x∂μ, |f x|≤C)
    (hm : 0 < ∫ x,f x^2∂μ) (hm1 : (∫ x,f x^2∂μ)≤1) :
    Entropy μ (fun x=>(1+f x)^2) ≤
      16*Entropy μ (fun x=>f x^2)+32*(∫ x,f x^2∂μ) := by
    have hb:=bounded_square_moments μ f hf hfb
    have hshift : ∃C:ℝ, ∀ᵐ x∂μ, |1+f x|≤C := by
      simpa [add_comm] using bounded_affine μ f hfb 1 1
    have hs:=bounded_square_moments μ (fun x=>1+f x) (measurable_const.add hf) hshift
    have hev:=(EntropyVariational μ (fun x=>(1+f x)^2)
      ((measurable_const.add hf).pow_const 2) (Filter.Eventually.of_forall fun x=>sq_nonneg _)
      hs.2.1 hs.2.2.1).1 1 (by norm_num)
    have hpos:=positive_log_control μ (fun x=>f x^2) (hf.pow_const 2)
      (Filter.Eventually.of_forall fun x=>sq_nonneg _) hb.2.1 hb.2.2.1 hb.2.2.2 hm hm1
    have hiR : Integrable (fun x=>16*f x^2*(1+max (Real.log (f x^2)) 0)) μ :=
      ((hb.2.1.add hb.2.2.2).const_mul 16).congr
        (Filter.Eventually.of_forall fun x=>by
          change 16*(f x^2+f x^2*max (Real.log (f x^2)) 0)=16*f x^2*(1+max (Real.log (f x^2)) 0)
          ring)
    have hh:=integral_mono_ae hev.2.1 hiR
      (Filter.Eventually.of_forall fun x=>by simpa using entropy_phi_translate_one (f x))
    have heq : (∫ x,16*f x^2*(1+max (Real.log (f x^2)) 0)∂μ)=
        16*((∫ x,f x^2∂μ)+(∫ x,f x^2*max (Real.log (f x^2)) 0∂μ)) := by
      have hfun : (fun x=>16*f x^2*(1+max (Real.log (f x^2)) 0)) =
        (fun x=>16*(f x^2+f x^2*max (Real.log (f x^2)) 0)) := by funext x;ring
      rw [hfun,integral_const_mul,integral_add hb.2.1 hb.2.2.2]
    have hh' : Entropy μ (fun x=>(1+f x)^2) ≤
      16*((∫ x,f x^2∂μ)+(∫ x,f x^2*max (Real.log (f x^2)) 0∂μ)) := by
      have h:=hev.2.2.trans hh
      simpa only [div_one,heq] using h
    linarith

  have normalized_center_bounded_entropy
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ᵐ x∂μ, |f x|≤C)
    (hm : (∫ x,f x^2∂μ)=1) (b:ℝ) (hbb:|b|≤1) :
    Entropy μ (fun x=>(f x+b)^2) ≤
      16*Entropy μ (fun x=>f x^2)+48 := by
    have hb:=bounded_square_moments μ f hf hfb
    have hshift : ∃C:ℝ, ∀ᵐ x∂μ, |f x+b|≤C := by
      simpa using bounded_affine μ f hfb 1 b
    have hs:=bounded_square_moments μ (fun x=>f x+b) (hf.add measurable_const) hshift
    have hev:=(EntropyVariational μ (fun x=>(f x+b)^2)
      ((hf.add measurable_const).pow_const 2) (Filter.Eventually.of_forall fun x=>sq_nonneg _)
      hs.2.1 hs.2.2.1).1 1 (by norm_num)
    have hpos:=positive_log_control μ (fun x=>f x^2) (hf.pow_const 2)
      (Filter.Eventually.of_forall fun x=>sq_nonneg _) hb.2.1 hb.2.2.1 hb.2.2.2
      (by rw [hm];norm_num) (by rw [hm])
    have hiR : Integrable (fun x=>16*(1+f x^2+f x^2*max (Real.log (f x^2)) 0)) μ :=
      (((integrable_const (1:ℝ)).add hb.2.1).add hb.2.2.2).const_mul 16
    have hh:=integral_mono_ae hev.2.1 hiR
      (Filter.Eventually.of_forall fun x=>by simpa using entropy_phi_translate_bounded (f x) b hbb)
    have heq : (∫ x,16*(1+f x^2+f x^2*max (Real.log (f x^2)) 0)∂μ)=
        16*(1+(∫ x,f x^2∂μ)+(∫ x,f x^2*max (Real.log (f x^2)) 0∂μ)) := by
      have hbase : Integrable (fun x=>1+f x^2) μ := (integrable_const (1:ℝ)).add hb.2.1
      rw [integral_const_mul,integral_add hbase hb.2.2.2,
        integral_add (integrable_const (1:ℝ)) hb.2.1]
      simp
    have hh' : Entropy μ (fun x=>(f x+b)^2) ≤
        16*(1+(∫ x,f x^2∂μ)+(∫ x,f x^2*max (Real.log (f x^2)) 0∂μ)) := by
      have h:=hev.2.2.trans hh
      simpa only [div_one,heq] using h
    rw [hm] at hpos hh'
    linarith

  have entropy_congr_ae
    (μ : Measure Ω) (u w : Ω → ℝ) (h : u=ᵐ[μ] w) : Entropy μ u=Entropy μ w := by
    unfold Entropy
    rw [integral_congr_ae h,integral_congr_ae (h.mono fun x hx=>by rw [hx])]

  have entropy_square_scaling
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ)
    (hf : Measurable f) (hfb : ∃C:ℝ,∀ᵐ x∂μ,|f x|≤C) (k:ℝ) :
    Entropy μ (fun x=>(k*f x)^2)=k^2*Entropy μ (fun x=>f x^2) := by
    have hb:=bounded_square_moments μ f hf hfb
    have hfun : (fun x=>(k*f x)^2)=(fun x=>k^2*(f x^2)) := by funext x;ring
    rw [hfun]
    exact entropy_scaling μ (fun x=>f x^2) hb.2.1 hb.2.2.1 (k^2)

  let v := ∫ x,f x^2∂μ
  have hvn : 0≤v:=integral_nonneg fun x=>sq_nonneg _
  have hb:=bounded_square_moments μ f hf hfb
  by_cases hv:v=0
  · have hzero: ∀ᵐ x∂μ,f x=0 := by
      have hz:=(integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall fun x=>sq_nonneg (f x)) hb.2.1).mp hv
      exact hz.mono fun x hx=>sq_eq_zero_iff.mp hx
    have he1 : Entropy μ (fun x=>(f x+a)^2)=0 := by
      rw [entropy_congr_ae μ _ (fun _=>a^2) (hzero.mono fun x hx=>by simp [hx])]
      simp [Entropy]
    have he2 : Entropy μ (fun x=>f x^2)=0 := by
      rw [entropy_congr_ae μ _ (fun _=>0) (hzero.mono fun x hx=>by simp [hx])]
      simp [Entropy]
    change _ ≤ 16*Entropy μ (fun x=>f x^2)+48*v
    rw [he1,he2,hv];norm_num
  have hvp:0<v:=lt_of_le_of_ne hvn (Ne.symm hv)
  by_cases ha2:a^2>v
  · have ha:a≠0:=by intro h;rw [h] at ha2;norm_num at ha2;linarith
    let g:=fun x=>f x/a
    have hg:Measurable g:=hf.div_const a
    have hgb:∃C:ℝ,∀ᵐ x∂μ,|g x|≤C:=by
      simpa [g,div_eq_mul_inv,mul_comm] using bounded_affine μ f hfb (a⁻¹) 0
    have hm:(∫ x,g x^2∂μ)=v/a^2:=by
      dsimp [g,v]
      simp_rw [div_pow]
      rw [integral_div]
    have hap:0<a^2:=sq_pos_of_ne_zero ha
    have he:=normalized_center_one_entropy μ g hg hgb
      (by rw [hm];exact div_pos hvp hap) (by rw [hm];exact (div_le_one hap).mpr (le_of_lt ha2))
    have heG:Entropy μ (fun x=>f x^2)=a^2*Entropy μ (fun x=>g x^2):=by
      have hfun:(fun x=>f x^2)=(fun x=>(a*g x)^2):=by
        funext x;dsimp [g];congr 1;field_simp
      rw [hfun]
      exact entropy_square_scaling μ g hg hgb a
    have hsb:∃C:ℝ,∀ᵐ x∂μ,|1+g x|≤C:=by
      simpa [add_comm] using bounded_affine μ g hgb 1 1
    have heF:Entropy μ (fun x=>(f x+a)^2)=a^2*Entropy μ (fun x=>(1+g x)^2):=by
      have hfun:(fun x=>(f x+a)^2)=(fun x=>(a*(1+g x))^2):=by
        funext x;dsimp [g];congr 1;field_simp <;> ring
      rw [hfun]
      exact entropy_square_scaling μ _ (measurable_const.add hg) hsb a
    have hmv:a^2*(∫ x,g x^2∂μ)=v:=by rw [hm];field_simp
    have heMul:=mul_le_mul_of_nonneg_left he (sq_nonneg a)
    change _ ≤16*Entropy μ (fun x=>f x^2)+48*v
    rw [heF,heG]
    nlinarith
  · let k:=Real.sqrt v
    have hk:0<k:=Real.sqrt_pos.mpr hvp
    have hk2:k^2=v:=Real.sq_sqrt hvn
    let g:=fun x=>f x/k
    have hg:Measurable g:=hf.div_const k
    have hgb:∃C:ℝ,∀ᵐ x∂μ,|g x|≤C:=by
      simpa [g,div_eq_mul_inv,mul_comm] using bounded_affine μ f hfb (k⁻¹) 0
    have hm:(∫ x,g x^2∂μ)=1:=by
      dsimp [g]
      simp_rw [div_pow]
      rw [integral_div,hk2]
      change v/v=1
      exact div_self hvp.ne'
    let b:=a/k
    have hb2:b^2≤1:=by
      dsimp [b]
      rw [div_pow,hk2]
      exact (div_le_one hvp).mpr (le_of_not_gt ha2)
    have hbb:|b|≤1:=
      (sq_le_sq₀ (abs_nonneg b) (by norm_num : (0:ℝ)≤1)).mp (by simpa using hb2)
    have he:=normalized_center_bounded_entropy μ g hg hgb hm b hbb
    have heG:Entropy μ (fun x=>f x^2)=k^2*Entropy μ (fun x=>g x^2):=by
      have hfun:(fun x=>f x^2)=(fun x=>(k*g x)^2):=by
        funext x;dsimp [g];congr 1;field_simp
      rw [hfun]
      exact entropy_square_scaling μ g hg hgb k
    have hsb:∃C:ℝ,∀ᵐ x∂μ,|g x+b|≤C:=by
      simpa using bounded_affine μ g hgb 1 b
    have heF:Entropy μ (fun x=>(f x+a)^2)=k^2*Entropy μ (fun x=>(g x+b)^2):=by
      have hfun:(fun x=>(f x+a)^2)=(fun x=>(k*(g x+b))^2):=by
        funext x;dsimp [g,b];congr 1;field_simp <;> ring
      rw [hfun]
      exact entropy_square_scaling μ _ (hg.add measurable_const) hsb k
    have heMul:=mul_le_mul_of_nonneg_left he (sq_nonneg k)
    change _ ≤16*Entropy μ (fun x=>f x^2)+48*v
    rw [heF,heG,←hk2]
    nlinarith
