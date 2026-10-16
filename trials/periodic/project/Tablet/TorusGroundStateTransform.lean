import Tablet.TorusGroundState
import Tablet.Entropy
import Mathlib.Topology.Constructions
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
open MeasureTheory
open scoped ContDiff
-- [TABLET NODE: TorusGroundStateTransform]
theorem TorusGroundStateTransform (d:ℕ) (V f : UnitAddTorus (Fin d)→ℝ)
    (hV:TorusSmooth V) (hf:TorusSmooth f) (L:ℝ) (hL:0≤L)
    (hLap:∀x,TorusLaplacian V x≤L) :
    let m := (volume : Measure (UnitAddTorus (Fin d)))
    let Z := ∫ x,Real.exp (-V x)∂m
    let ν := NormalizedTilt m (fun x=>Real.exp (-V x))
    let ψ := fun x=>f x*Real.exp (-V x/2)/Real.sqrt Z
    0<Z ∧ IsProbabilityMeasure ν ∧ TorusSmooth ψ ∧
    (∫x,ψ x^2∂m)=(∫x,f x^2∂ν) ∧
    Entropy ν (fun x=>f x^2)=Entropy m (fun x=>ψ x^2)+
      (∫x,(V x+Real.log Z)*ψ x^2∂m) ∧
    (∫x,‖TorusGradient ψ x‖^2∂m)≤(∫x,‖TorusGradient f x‖^2∂ν)+
      L/2*(∫x,f x^2∂ν) ∧
    (∫x,(L-TorusLaplacian V x)*ψ x^2∂m)≤
      2*(∫x,‖TorusGradient f x‖^2∂ν)+L*(∫x,f x^2∂ν) := by
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
  
  have gradient_mul {d : ℕ} {f h : UnitAddTorus (Fin d) → ℝ}
      (hf : TorusSmooth f) (hh : TorusSmooth h) (x : UnitAddTorus (Fin d))
      (j : Fin d) : TorusGradient (fun x => f x * h x) x j =
        TorusGradient f x j * h x + f x * TorusGradient h x j := by
    obtain ⟨y, rfl⟩ := (quotient d).surjective x
    simp_rw [gradient_on_lift]
    have hd := (hf.differentiable (by simp) y).hasFDerivAt.mul
      (hh.differentiable (by simp) y).hasFDerivAt
    change HasFDerivAt (fun x => f (TorusLift d x) * h (TorusLift d x)) _ y at hd
    rw [hd.fderiv]
    simp
    ring
  
  have laplacian_gradient_sum {d : ℕ} (f : UnitAddTorus (Fin d) → ℝ)
      (x : UnitAddTorus (Fin d)) :
      TorusLaplacian f x = ∑ j, TorusGradient (fun x => TorusGradient f x j) x j := by
    let y : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2
      (fun j => (AddCircle.equivIco (1 : ℝ) 0 (x j) : ℝ))
    have hy : TorusLift d y = x := by
      ext j
      simp [TorusLift, y]
    calc
      TorusLaplacian f x = ∑ j, fderiv ℝ
          (fun z => fderiv ℝ (fun w => f (TorusLift d w)) z
            (EuclideanSpace.single j 1)) y (EuclideanSpace.single j 1) := rfl
      _ = ∑ j, TorusGradient (fun x => TorusGradient f x j) (TorusLift d y) j := by
        simp_rw [gradient_on_lift]
      _ = _ := by rw [hy]
  
  let m := (volume : Measure (UnitAddTorus (Fin d)))
  let Z := ∫ x,Real.exp (-V x)∂m
  let ν := NormalizedTilt m (fun x=>Real.exp (-V x))
  let c:=Real.sqrt Z
  let ψ:=fun x=>f x*Real.exp (-V x/2)/c
  have hw : Continuous (fun x=>Real.exp (-V x)) := Real.continuous_exp.comp (continuous hV).neg
  have hwi : Integrable (fun x=>Real.exp (-V x)) m :=
    hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hZ:0<Z:=integral_exp_pos hwi
  have hc:0<c:=Real.sqrt_pos.mpr hZ
  have hc2:c^2=Z:=Real.sq_sqrt hZ.le
  have hψ:TorusSmooth ψ:=by
    change ContDiff ℝ ∞ (fun y=>f (TorusLift d y)*Real.exp (-V (TorusLift d y)/2)/c)
    exact (hf.mul (hV.neg.div_const 2).exp).div_const c
  have cont_grad {g : UnitAddTorus (Fin d) → ℝ} (hg : TorusSmooth g) :
      Continuous (TorusGradient g) := by
    exact (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).continuous_symm.comp
      (continuous_pi (fun j => continuous (gradient_smooth hg j)))
  have cont_lap : Continuous (TorusLaplacian V) := by
    change Continuous (fun x => TorusLaplacian V x)
    simp_rw [laplacian_gradient_sum]
    exact continuous_finsetSum _ (fun j _ =>
      continuous (gradient_smooth (gradient_smooth hV j) j))
  have ci {g : UnitAddTorus (Fin d) → ℝ} (hg : Continuous g) :
      MeasureTheory.Integrable g m :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have cf := continuous hf
  have cV := continuous hV
  have cψ := continuous hψ
  have cgψ := cont_grad hψ
  have cgV := cont_grad hV
  have hψ2 (x) : ψ x^2 = f x^2 * Real.exp (-V x) / Z := by
    have he : Real.exp (-V x / 2)^2 = Real.exp (-V x) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    dsimp [ψ]
    rw [div_pow, mul_pow, he, hc2]
  have ht := TiltNormalization m (fun x => Real.exp (-V x)) hw.measurable
    (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)) hwi hZ
  have hm := ht.2 (fun x => f x^2) (cf.pow 2).measurable
    (ci ((cf.pow 2).mul hw))
  have hmass : (∫x,ψ x^2∂m) = (∫x,f x^2∂ν) := by
    simp_rw [hψ2]
    rw [integral_div, hm.2]
  have cfl : Continuous (fun x => f x^2 * Real.log (f x^2)) :=
    Real.continuous_mul_log.comp (cf.pow 2)
  have cψl : Continuous (fun x => ψ x^2 * Real.log (ψ x^2)) :=
    Real.continuous_mul_log.comp (cψ.pow 2)
  have clp : Continuous (fun x => (V x+Real.log Z)*ψ x^2) :=
    (cV.add continuous_const).mul (cψ.pow 2)
  have hl := ht.2 (fun x => f x^2 * Real.log (f x^2)) cfl.measurable
    (ci (cfl.mul hw))
  have hpoint (x) : (f x^2 * Real.log (f x^2))*Real.exp (-V x)/Z =
      ψ x^2 * Real.log (ψ x^2) + (V x+Real.log Z)*ψ x^2 := by
    by_cases hx : f x=0
    · simp [hψ2,hx]
    · have hf2 : f x^2 ≠ 0 := pow_ne_zero _ hx
      have hlog : Real.log (ψ x^2) = Real.log (f x^2)-V x-Real.log Z := by
        rw [hψ2, Real.log_div (mul_ne_zero hf2 (Real.exp_ne_zero _)) hZ.ne',
          Real.log_mul hf2 (Real.exp_ne_zero _), Real.log_exp]
        ring
      rw [hlog,hψ2]
      ring
  have hent : Entropy ν (fun x=>f x^2) = Entropy m (fun x=>ψ x^2)+
      ∫x,(V x+Real.log Z)*ψ x^2∂m := by
    unfold Entropy
    rw [hl.2, ← hmass, ← integral_div]
    rw [show (fun x => f x^2 * Real.log (f x^2) * Real.exp (-V x)/Z) =
      (fun x => ψ x^2 * Real.log (ψ x^2) + (V x+Real.log Z)*ψ x^2) from funext hpoint]
    rw [integral_add (ci cψl) (ci clp)]
    ring
  let G := fun x => ‖TorusGradient ψ x‖^2
  let Q := fun x => (1/4:ℝ)*‖TorusGradient V x‖^2*ψ x^2
  let K := fun x => G x+Q x-(1/2:ℝ)*TorusLaplacian V x*ψ x^2
  have hGi : Integrable G m := ci (cgψ.norm.pow 2)
  have hQi : Integrable Q m := ci ((continuous_const.mul (cgV.norm.pow 2)).mul (cψ.pow 2))
  have hKi : Integrable K m := (hGi.add hQi).sub
    (ci ((continuous_const.mul cont_lap).mul (cψ.pow 2)))
  have hψi : Integrable (fun x=>ψ x^2) m := ci (cψ.pow 2)
  have hsi : Integrable (fun x=>(L-TorusLaplacian V x)*ψ x^2) m :=
    ci ((continuous_const.sub cont_lap).mul (cψ.pow 2))
  have hid : (∫x,‖TorusGradient f x‖^2∂ν) = (∫x,K x∂m) :=
    (TorusGroundState d V f hV hf).2
  have hQ0 (x) : 0≤Q x := by
    dsimp [Q]
    positivity
  have hbound : (∫x,G x∂m) ≤ (∫x,K x∂m)+L/2*(∫x,ψ x^2∂m) := by
    have hp : ∀x,G x≤K x+(L/2)*ψ x^2 := by
      intro x
      have hv:=mul_nonneg (sub_nonneg.mpr (hLap x)) (sq_nonneg (ψ x))
      have hq:=hQ0 x
      dsimp [K]
      nlinarith
    have hi:=integral_mono_ae hGi (hKi.add (hψi.const_mul (L/2)))
      (Filter.Eventually.of_forall hp)
    change (∫x,G x∂m) ≤ (∫x,K x+(L/2)*ψ x^2∂m) at hi
    rw [integral_add hKi (hψi.const_mul (L/2)),integral_const_mul] at hi
    exact hi
  have hsbound : (∫x,(L-TorusLaplacian V x)*ψ x^2∂m) ≤
      2*(∫x,K x∂m)+L*(∫x,ψ x^2∂m) := by
    have hp : ∀x,(L-TorusLaplacian V x)*ψ x^2≤2*K x+L*ψ x^2 := by
      intro x
      have hg:0≤G x:=sq_nonneg _
      have hq:=hQ0 x
      dsimp [K]
      nlinarith
    have hi:=integral_mono_ae hsi ((hKi.const_mul 2).add (hψi.const_mul L))
      (Filter.Eventually.of_forall hp)
    change (∫x,(L-TorusLaplacian V x)*ψ x^2∂m) ≤
      (∫x,2*K x+L*ψ x^2∂m) at hi
    rw [integral_add (hKi.const_mul 2) (hψi.const_mul L),integral_const_mul,
      integral_const_mul] at hi
    exact hi
  rw [←hid,hmass] at hbound hsbound
  exact ⟨hZ,ht.1,hψ,hmass,hent,hbound,hsbound⟩
