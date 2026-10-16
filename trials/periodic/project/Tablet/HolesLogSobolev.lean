module

public import Tablet.RieszAtomicPotentialBounds
public import Tablet.GroundedDefectiveLogSobolev
public import Tablet.HolesPoincare
public import Tablet.EntropyDefectRemoval
public import Tablet.BoundedDensityComparison
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.WithLp

@[expose] public section
open MeasureTheory
open scoped ContDiff
-- [TABLET NODE: HolesLogSobolev]
theorem HolesLogSobolev (d:ℕ)(hd:2≤d)(s a B:ℝ)(hs:0≤s)
    (hsd:s≤(d:ℝ)-2)(hL:s<(d:ℝ)/2)(ha:0<a)(hB:0≤B) :
    ∃rate:ℝ,0<rate ∧
      ∀(n:ℕ)(w:Fin n→ℝ)(y:Fin n→UnitAddTorus (Fin d)),
      (∀j,0≤w j)→(∑j,w j)≤B→∀ε:ℝ,0<ε→
      let U:=AtomicPotential (RieszKernel d s a ε) w y
      let ν:=NormalizedTilt volume (fun x=>Real.exp (-U x))
      (∀f:UnitAddTorus (Fin d)→ℝ,TorusSmooth f→
        Entropy ν (fun x=>f x^2)≤(2/rate)*(∫x,‖TorusGradient f x‖^2∂ν)) ∧
      (∀(b:UnitAddTorus (Fin d)→ℝ)(l u:ℝ),Measurable b→0<l→
        (∀ᵐx,l≤b x ∧ b x≤u)→∀f:UnitAddTorus (Fin d)→ℝ,TorusSmooth f→
        Entropy (NormalizedTilt volume (fun x=>b x*Real.exp (-U x))) (fun x=>f x^2)≤
          (u/l)*(2/rate)*(∫x,‖TorusGradient f x‖^2∂NormalizedTilt volume (fun x=>b x*Real.exp (-U x)))) := by
-- BODY
  classical
  have torus_entropy_defect_removal (d:ℕ) (ν:Measure (UnitAddTorus (Fin d)))
      [IsProbabilityMeasure ν] (A B rate:ℝ) (hA:0≤A) (hB:0≤B) (hrate:0<rate)
      (hdef:∀f:UnitAddTorus (Fin d)→ℝ,TorusSmooth f→
        Entropy ν (fun x=>f x^2)≤A*(∫x,‖TorusGradient f x‖^2∂ν)+B*(∫x,f x^2∂ν))
      (hpi:∀f:UnitAddTorus (Fin d)→ℝ,TorusSmooth f→
        ProbabilityTheory.variance f ν≤rate⁻¹*(∫x,‖TorusGradient f x‖^2∂ν)) :
      let ρ:=2/(16*A+(16*B+48)*rate⁻¹)
      0<ρ ∧ ∀f:UnitAddTorus (Fin d)→ℝ,TorusSmooth f→
        Entropy ν (fun x=>f x^2)≤(2/ρ)*(∫x,‖TorusGradient f x‖^2∂ν) := by
    classical
    have quotient (d : ℕ) : IsOpenQuotientMap (TorusLift d) := by
      have hc : IsOpenQuotientMap ((↑) : ℝ → AddCircle (1 : ℝ)) :=
        QuotientAddGroup.isOpenQuotientMap_mk
      have hp : IsOpenQuotientMap
          (Pi.map (fun _ : Fin d => ((↑) : ℝ → AddCircle (1 : ℝ)))) :=
        IsOpenQuotientMap.piMap (fun _ => hc)
      exact hp.comp (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isOpenQuotientMap
    
    have continuous {d : ℕ} {f : UnitAddTorus (Fin d) → ℝ}
        (hf : TorusSmooth f) : Continuous f := by
      apply (quotient d).continuous_comp_iff.mp
      exact hf.continuous
    
    let E := fun f:UnitAddTorus (Fin d)→ℝ => ∫x,‖TorusGradient f x‖^2∂ν
    have hdata:∀f:UnitAddTorus (Fin d)→ℝ,TorusSmooth f→
        Measurable f ∧ ∃C:ℝ,∀ᵐ x∂ν,|f x|≤C := by
      intro f hf
      have cf:=continuous hf
      obtain ⟨C,hC⟩:=isCompact_univ.bddAbove_image (f:=fun x=>‖f x‖) cf.norm.continuousOn
      refine ⟨cf.measurable,C,Filter.Eventually.of_forall fun x=>?_⟩
      exact hC (Set.mem_image_of_mem _ (Set.mem_univ x))
    have hcenter:∀f:UnitAddTorus (Fin d)→ℝ,TorusSmooth f→
        TorusSmooth (fun x=>f x-∫y,f y∂ν):=fun f hf=>hf.sub contDiff_const
    have hE:∀f:UnitAddTorus (Fin d)→ℝ,TorusSmooth f→
        E (fun x=>f x-∫y,f y∂ν)=E f:=by
      intro f hf
      have hg:TorusGradient (fun x=>f x-∫y,f y∂ν)=TorusGradient f:=by
        funext x
        unfold TorusGradient
        simp only [fderiv_sub_const]
      dsimp only [E]
      rw[hg]
    have hpi':∀f:UnitAddTorus (Fin d)→ℝ,TorusSmooth f→
        (∫x,(f x-∫y,f y∂ν)^2∂ν)≤rate⁻¹*E f:=by
      intro f hf
      rw[←ProbabilityTheory.variance_eq_integral (continuous hf).measurable.aemeasurable]
      exact hpi f hf
    exact EntropyDefectRemoval ν TorusSmooth E A B rate⁻¹ hA hB (inv_pos.mpr hrate)
      hdata hcenter hE hdef hpi'
  have background_torus_lsi (d:ℕ) (V:UnitAddTorus (Fin d)→ℝ) (hV:TorusSmooth V)
      (rate:ℝ) (hrate:0<rate)
      (htight:∀f:UnitAddTorus (Fin d)→ℝ,TorusSmooth f→
        Entropy (NormalizedTilt volume (fun x=>Real.exp (-V x))) (fun x=>f x^2)≤
          (2/rate)*(∫x,‖TorusGradient f x‖^2∂NormalizedTilt volume (fun x=>Real.exp (-V x)))) :
      ∀(b:UnitAddTorus (Fin d)→ℝ)(l u:ℝ),Measurable b→0<l→
        (∀ᵐx,l≤b x ∧ b x≤u)→∀f:UnitAddTorus (Fin d)→ℝ,TorusSmooth f→
        Entropy (NormalizedTilt volume (fun x=>b x*Real.exp (-V x))) (fun x=>f x^2)≤
          (u/l)*(2/rate)*(∫x,‖TorusGradient f x‖^2∂NormalizedTilt volume (fun x=>b x*Real.exp (-V x))) := by
    classical
    have quotient (d : ℕ) : IsOpenQuotientMap (TorusLift d) := by
      have hc : IsOpenQuotientMap ((↑) : ℝ → AddCircle (1 : ℝ)) :=
        QuotientAddGroup.isOpenQuotientMap_mk
      have hp : IsOpenQuotientMap
          (Pi.map (fun _ : Fin d => ((↑) : ℝ → AddCircle (1 : ℝ)))) :=
        IsOpenQuotientMap.piMap (fun _ => hc)
      exact hp.comp (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isOpenQuotientMap
    
    have continuous {d : ℕ} {f : UnitAddTorus (Fin d) → ℝ}
        (hf : TorusSmooth f) : Continuous f := by
      apply (quotient d).continuous_comp_iff.mp
      exact hf.continuous
    
    have lift_translation_eq {d : ℕ} (y z : EuclideanSpace ℝ (Fin d))
        (h : TorusLift d y = TorusLift d z) (x : EuclideanSpace ℝ (Fin d)) :
        TorusLift d (x + (z-y)) = TorusLift d x := by
      funext j
      have hj := congrFun h j
      change (y j : AddCircle (1 : ℝ)) = (z j : AddCircle (1 : ℝ)) at hj
      simp only [TorusLift, PiLp.add_apply, PiLp.sub_apply]
      rw [AddCircle.coe_add, AddCircle.coe_sub, ← hj, sub_self, add_zero]
    
    have lift_fderiv_eq {d : ℕ} (f : UnitAddTorus (Fin d) → ℝ)
        (y z : EuclideanSpace ℝ (Fin d)) (h : TorusLift d y = TorusLift d z) :
        fderiv ℝ (fun x => f (TorusLift d x)) y =
          fderiv ℝ (fun x => f (TorusLift d x)) z := by
      let q := fun x => f (TorusLift d x)
      have hfun : (fun x => q (x+(z-y))) = q := by
        funext x
        exact congrArg f (lift_translation_eq y z h x)
      have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := q) (x := y) (z-y)
      rw [hfun] at hd
      simpa using hd
    
    have gradient_on_lift {d : ℕ} (f : UnitAddTorus (Fin d) → ℝ)
        (y : EuclideanSpace ℝ (Fin d)) (j : Fin d) :
        TorusGradient f (TorusLift d y) j =
          fderiv ℝ (fun x => f (TorusLift d x)) y (EuclideanSpace.single j 1) := by
      let z : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2
        (fun j => (AddCircle.equivIco (1 : ℝ) 0 (TorusLift d y j) : ℝ))
      have hz : TorusLift d z = TorusLift d y := by
        funext j
        simp [TorusLift, z]
      change fderiv ℝ (fun x => f (TorusLift d x)) z (EuclideanSpace.single j 1) = _
      rw [lift_fderiv_eq f z y hz]
    
    have gradient_smooth {d : ℕ} {f : UnitAddTorus (Fin d) → ℝ}
        (hf : TorusSmooth f) (j : Fin d) : TorusSmooth (fun x => TorusGradient f x j) := by
      change ContDiff ℝ ∞ (fun y => TorusGradient f (TorusLift d y) j)
      simp_rw [gradient_on_lift]
      exact (hf.fderiv_right (by simp)).clm_apply contDiff_const
    
    have tilt_multiply {Ω : Type} [MeasurableSpace Ω]
        (μ : Measure Ω) (w b : Ω → ℝ) (l u : ℝ)
        (hw : Measurable w) (hwp : ∀ᵐ x ∂μ, 0 ≤ w x)
        (hwi : Integrable w μ) (hZ : 0 < ∫ x, w x ∂μ)
        (hb : Measurable b) (hl : 0 < l)
        (hbb : ∀ᵐ x ∂μ, l ≤ b x ∧ b x ≤ u) :
        NormalizedTilt μ (fun x => b x * w x) =
          NormalizedTilt (NormalizedTilt μ w) b := by
      have hbn : ∀ᵐ x ∂μ, 0 ≤ b x := hbb.mono fun x hx => hl.le.trans hx.1
      have hbabs : ∀ᵐ x ∂μ, ‖b x‖ ≤ max |l| |u| := by
        filter_upwards [hbb, hbn] with x hx hp
        rw [Real.norm_eq_abs, abs_of_nonneg hp]
        exact hx.2.trans ((le_abs_self u).trans (le_max_right _ _))
      have hbwi : Integrable (fun x => b x * w x) μ := hwi.bdd_mul hb.aestronglyMeasurable hbabs
      have hZbw : 0 < ∫ x, b x * w x ∂μ := by
        have hlow : l * ∫ x, w x ∂μ ≤ ∫ x, b x * w x ∂μ := by
          rw [← integral_const_mul]
          apply integral_mono_ae (hwi.const_mul l) hbwi
          filter_upwards [hbb, hwp] with x hx hp
          exact mul_le_mul_of_nonneg_right hx.1 hp
        exact (mul_pos hl hZ).trans_le hlow
      have ht := (TiltNormalization μ w hw hwp hwi hZ).2 b hb (by
        simpa only [mul_comm] using hbwi)
      simp only [NormalizedTilt] at ht ⊢
      rw [ht.2]
      rw [← withDensity_mul μ (by fun_prop) (by fun_prop)]
      apply withDensity_congr_ae
      filter_upwards [hwp, hbn] with x hx hbpos
      simp only [Pi.mul_apply]
      rw [← ENNReal.ofReal_mul (div_nonneg hx hZ.le)]
      congr 1
      field_simp [ne_of_gt hZ, ne_of_gt hZbw]
      <;> ring

    let ν:=NormalizedTilt volume (fun x=>Real.exp (-V x))
    have hweight : Continuous (fun x => Real.exp (-V x)) :=
      Real.continuous_exp.comp (continuous hV).neg
    have hwi : Integrable (fun x => Real.exp (-V x)) volume :=
      hweight.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hZ : 0 < ∫ x, Real.exp (-V x) := integral_exp_pos hwi
    have ht := TiltNormalization volume (fun x => Real.exp (-V x)) hweight.measurable
      (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)) hwi hZ
    haveI : IsProbabilityMeasure ν := ht.1
    intro b l u hb hl hbounds f hf
    have hac : ν.AbsolutelyContinuous volume := withDensity_absolutelyContinuous _ _
    have hboundsν := hbounds.filter_mono hac.ae_le
    have cg : Continuous (TorusGradient f) :=
      (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).continuous_symm.comp
        (continuous_pi (fun j => continuous (gradient_smooth hf j)))
    have hfbound : ∃ C : ℝ, ∀ᵐ x ∂ν, |f x| ≤ C := by
      obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn (continuous hf).continuousOn
      refine ⟨C, Filter.Eventually.of_forall (fun x => ?_)⟩
      simpa only [Real.norm_eq_abs] using hC x (Set.mem_univ x)
    have hei : Integrable (fun x => ‖TorusGradient f x‖^2) ν :=
      (cg.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hc := BoundedDensityComparison ν b f (fun x => ‖TorusGradient f x‖^2)
      l u hl hb hboundsν (continuous hf).measurable hfbound (cg.norm.pow 2).measurable
        (Filter.Eventually.of_forall (fun x => sq_nonneg _)) hei
    have hw' := BoundedTiltBounds ν b l u hl hb hboundsν
    have hZb : 0 < ∫ x,b x ∂ν := hl.trans_le hw'.2.1
    have hcomp := tilt_multiply volume (fun x => Real.exp (-V x)) b l u
      hweight.measurable (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le))
      hwi hZ hb hl hbounds
    rw [hcomp]
    calc
      Entropy (NormalizedTilt ν b) (fun x=>f x^2) ≤
          (u / (∫ x,b x ∂ν)) * Entropy ν (fun x=>f x^2) := hc.2.1
      _ ≤ (u / (∫ x,b x ∂ν)) * ((2/rate) * ∫ x, ‖TorusGradient f x‖^2 ∂ν) := by
        apply mul_le_mul_of_nonneg_left (htight f hf)
        exact div_nonneg (by
          have hlu : l ≤ u := by
            obtain ⟨x,hx⟩ := hboundsν.exists
            exact hx.1.trans hx.2
          exact hl.le.trans hlu) hZb.le
      _ ≤ (u/l)*(2/rate) * (∫ x, ‖TorusGradient f x‖^2 ∂NormalizedTilt ν b) := by
        have hE := hc.2.2.1
        have hlu : l ≤ u := by obtain ⟨x,hx⟩ := hboundsν.exists; exact hx.1.trans hx.2
        have hfac : 0 ≤ (u/l)*(2/rate) := mul_nonneg (div_nonneg (hl.le.trans hlu) hl.le)
          (div_nonneg (by norm_num) hrate.le)
        have h := mul_le_mul_of_nonneg_left hE hfac
        have hid : (u/l)*(2/rate) * ((l/(∫ x,b x ∂ν))*∫ x, ‖TorusGradient f x‖^2 ∂ν) =
            (u/(∫ x,b x ∂ν))*((2/rate) * ∫ x, ‖TorusGradient f x‖^2 ∂ν) := by
          field_simp [ne_of_gt hl]
          <;> ring
        rw [hid] at h
        exact h
  have quotient (d : ℕ) : IsOpenQuotientMap (TorusLift d) := by
    have hc : IsOpenQuotientMap ((↑) : ℝ → AddCircle (1 : ℝ)) :=
      QuotientAddGroup.isOpenQuotientMap_mk
    have hp : IsOpenQuotientMap
        (Pi.map (fun _ : Fin d => ((↑) : ℝ → AddCircle (1 : ℝ)))) :=
      IsOpenQuotientMap.piMap (fun _ => hc)
    exact hp.comp (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isOpenQuotientMap
  
  have continuous {d : ℕ} {f : UnitAddTorus (Fin d) → ℝ}
      (hf : TorusSmooth f) : Continuous f := by
    apply (quotient d).continuous_comp_iff.mp
    exact hf.continuous
  
  obtain ⟨c,M,A,θ,C,hc,hM,hA,hθ,hC,hStrict,hEndpoint,hPotential⟩:=
    RieszAtomicPotentialBounds d hd s a B hs hsd hL ha hB
  obtain ⟨D,F,hD,hF,hDefective⟩:=GroundedDefectiveLogSobolev d (by omega)
    A θ C (M*B) c hA hθ hC (mul_nonneg hM hB) hc
  obtain ⟨lambdaRate,hlambdaRate,hPoincare⟩:=HolesPoincare d hd s a B hs hsd ha hB
  let rate:=2/(16*D+(16*F+48)*lambdaRate⁻¹)
  have hlambdaRateinv:0<lambdaRate⁻¹:=inv_pos.mpr hlambdaRate
  have hden:0<16*D+(16*F+48)*lambdaRate⁻¹:=by nlinarith
  have hr:0<rate:=div_pos (by norm_num) hden
  refine ⟨rate,hr,?_⟩
  intro n w y hw hmass ε hε
  let U:=AtomicPotential (RieszKernel d s a ε) w y
  let ν:=NormalizedTilt volume (fun x=>Real.exp (-U x))
  obtain ⟨hUs,hUlow,hULap,hSource,hUform⟩:=hPotential n w y hw hmass ε hε
  have hdU:=hDefective U hUs hUlow hULap hUform
  have hpU:∀f:UnitAddTorus (Fin d)→ℝ,TorusSmooth f→
      ProbabilityTheory.variance f ν≤lambdaRate⁻¹*(∫x,‖TorusGradient f x‖^2∂ν):=
    (hPoincare n w y hw hmass ε hε).1
  have hweight:Continuous (fun x=>Real.exp (-U x)):=Real.continuous_exp.comp (continuous hUs).neg
  have hwi:Integrable (fun x=>Real.exp (-U x)) volume:=
    hweight.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hZ:0<∫x,Real.exp (-U x):=integral_exp_pos hwi
  have ht:=TiltNormalization volume (fun x=>Real.exp (-U x)) hweight.measurable
    (Filter.Eventually.of_forall (fun x=>(Real.exp_pos _).le)) hwi hZ
  haveI:IsProbabilityMeasure ν:=ht.1
  have hTight:=torus_entropy_defect_removal d ν D F lambdaRate hD.le hF hlambdaRate hdU hpU
  refine ⟨hTight.2,?_⟩
  exact background_torus_lsi d U hUs rate hr hTight.2
