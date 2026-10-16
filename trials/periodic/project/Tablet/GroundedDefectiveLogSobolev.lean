module

public import Tablet.TorusGroundStateTransform
public import Tablet.TorusHaarLogSobolev
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

@[expose] public section
open MeasureTheory
open scoped ContDiff
-- [TABLET NODE: GroundedDefectiveLogSobolev]
theorem GroundedDefectiveLogSobolev (d:ℕ) (hd:0<d) (A θ C L c:ℝ)
    (hA:0≤A) (hθ:0≤θ) (hC:0≤C) (hL:0≤L) (hc:0≤c) :
    ∃D F:ℝ,0<D ∧ 0≤F ∧ ∀V:UnitAddTorus (Fin d)→ℝ,
      TorusSmooth V → (∀x,-c≤V x) → (∀x,TorusLaplacian V x≤L) →
      (∀u:UnitAddTorus (Fin d)→ℝ,TorusSmooth u→
        (∫x,V x*u x^2)≤A*(∫x,‖TorusGradient u x‖^2)+
          θ*(∫x,(L-TorusLaplacian V x)*u x^2)+C*(∫x,u x^2)) →
      ∀f:UnitAddTorus (Fin d)→ℝ,TorusSmooth f→
        let ν:=NormalizedTilt volume (fun x=>Real.exp (-V x))
        Entropy ν (fun x=>f x^2)≤D*(∫x,‖TorusGradient f x‖^2∂ν)+F*(∫x,f x^2∂ν) := by
-- BODY
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
  
  haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1:ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simpa using (inferInstance : IsProbabilityMeasure AddCircle.haarAddCircle)
  haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin d=>
      (volume : Measure (AddCircle (1:ℝ))))))
  obtain ⟨H,hH,hHaar⟩ := TorusHaarLogSobolev d hd
  let D:=H+A+2*θ
  let F:=(H+A)*L/2+θ*L+C+c
  refine ⟨D,F,by dsimp[D]; linarith,by dsimp[F]; positivity,?_⟩
  intro V hV hlow hLap hform f hf
  let m:Measure (UnitAddTorus (Fin d)):=volume
  let Z:=∫x,Real.exp (-V x)∂m
  let ν:=NormalizedTilt m (fun x=>Real.exp (-V x))
  let ψ:=fun x=>f x*Real.exp (-V x/2)/Real.sqrt Z
  obtain ⟨hZ,hprob,hψ,hmass,hent,henergy,hsource⟩ :=
    TorusGroundStateTransform d V f hV hf L hL hLap
  have cV:=continuous hV
  have cψ:=continuous hψ
  have ci {g:UnitAddTorus (Fin d)→ℝ}(hg:Continuous g):Integrable g m:=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hw:Continuous (fun x=>Real.exp (-V x)):=Real.continuous_exp.comp cV.neg
  have hZi:Z≤Real.exp c:=by
    have he:=integral_mono (ci hw) (integrable_const (Real.exp c))
      (fun x=>Real.exp_le_exp.mpr (by have hh:=hlow x; linarith))
    simpa [m] using he
  have hlog:Real.log Z≤c:=(Real.log_le_iff_le_exp hZ).mpr hZi
  have hvi:Integrable (fun x=>V x*ψ x^2) m:=ci (cV.mul (cψ.pow 2))
  have hpsi:Integrable (fun x=>ψ x^2) m:=ci (cψ.pow 2)
  have hpotential : Integrable (fun x => (V x+Real.log Z)*ψ x^2) m :=
    ci ((cV.add continuous_const).mul (cψ.pow 2))
  have hpot : (∫x,(V x+Real.log Z)*ψ x^2∂m)≤
      (∫x,V x*ψ x^2∂m)+c*(∫x,ψ x^2∂m):=by
    have hi:=integral_mono hpotential
      (hvi.add (hpsi.const_mul c)) (fun x=>by
        have hh:=mul_le_mul_of_nonneg_right hlog (sq_nonneg (ψ x))
        change (V x+Real.log Z)*ψ x^2 ≤ V x*ψ x^2+c*ψ x^2
        nlinarith)
    change (∫x,(V x+Real.log Z)*ψ x^2∂m)≤∫x,V x*ψ x^2+c*ψ x^2∂m at hi
    rw[integral_add hvi (hpsi.const_mul c),integral_const_mul] at hi
    exact hi
  have hhaar:=hHaar ψ hψ
  have hfm:=hform ψ hψ
  have hfirst : Entropy ν (fun x=>f x^2)≤
      (H+A)*(∫x,‖TorusGradient ψ x‖^2∂m)+
      θ*(∫x,(L-TorusLaplacian V x)*ψ x^2∂m)+(C+c)*(∫x,ψ x^2∂m):=by
    rw[hent]
    linarith
  have he:=mul_le_mul_of_nonneg_left henergy (by linarith : 0≤H+A)
  have hs:=mul_le_mul_of_nonneg_left hsource hθ
  rw[hmass] at hfirst
  dsimp only [D,F]
  nlinarith
