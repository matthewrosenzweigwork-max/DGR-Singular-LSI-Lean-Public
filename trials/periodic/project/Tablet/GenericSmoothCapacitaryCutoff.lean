import Tablet.CapacitaryPotentialCutoff
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.LocalExtr.Basic
open MeasureTheory Filter Set
open scoped ContDiff Topology
-- [TABLET NODE: GenericSmoothCapacitaryCutoff]
theorem GenericSmoothCapacitaryCutoff : ∃(ψ:ℝ→ℝ)(D:ℝ),0<D ∧ ContDiff ℝ ∞ ψ ∧
    ∀(d:ℕ)(V:UnitAddTorus (Fin d)→ℝ),TorusSmooth V→
    ∀(K L:ℝ),0≤K→0≤L→(∀x,0≤V x)→(∫x,V x)≤K→
    (∀x,TorusLaplacian V x≤L)→∀T:ℝ,0<T→
    let χ:=fun x=>ψ (V x/T)
    TorusSmooth χ ∧ (∀x,0≤χ x ∧ χ x≤1) ∧
    (∀x,V x≤T/2→χ x=1) ∧ (∀x,T≤V x→χ x=0) ∧
    (∫x,(χ x-1)^2)≤4*K/T ∧ (∫x,‖TorusGradient χ x‖^2)≤D^2*L/T := by
-- BODY
  classical
  have quotient (d : ℕ) : IsOpenQuotientMap (TorusLift d) := by
      have hc : IsOpenQuotientMap ((↑) : ℝ → AddCircle (1 : ℝ)) :=
        QuotientAddGroup.isOpenQuotientMap_mk
      have hp : IsOpenQuotientMap
          (Pi.map (fun _ : Fin d => ((↑) : ℝ → AddCircle (1 : ℝ)))) :=
        IsOpenQuotientMap.piMap (fun _ => hc)
      exact hp.comp (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isOpenQuotientMap
  have torus_smooth_continuous {d : ℕ} {f : UnitAddTorus (Fin d) → ℝ}
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
  have gradient_energy_continuous {d:ℕ}{V:UnitAddTorus (Fin d)→ℝ}(hV:TorusSmooth V) :
      Continuous (fun x=>‖TorusGradient V x‖^2) := by
    have hg : Continuous (TorusGradient V) := by
      apply (PiLp.continuous_toLp 2 (fun _:Fin d=>ℝ)).comp
      apply continuous_pi
      intro j
      exact torus_smooth_continuous (gradient_smooth hV j)
    exact hg.norm.pow 2
  have smooth_capacity_bump : ∃(ψ:ℝ→ℝ)(D:ℝ),0<D ∧ ContDiff ℝ ∞ ψ ∧
      (∀z,0≤ψ z ∧ ψ z≤1) ∧ (∀z,|z|≤1/2→ψ z=1) ∧
      (∀z,1≤|z|→ψ z=0) ∧ (∀z,|deriv ψ z|≤D) ∧
      (∀z,1≤|z|→deriv ψ z=0) := by
    let ψ : ContDiffBump (0:ℝ) := ⟨1/2,1,by norm_num,by norm_num⟩
    have hs : ContDiff ℝ ∞ (ψ:ℝ→ℝ) := ψ.contDiff
    obtain ⟨C,hC⟩ := ψ.hasCompactSupport.deriv.exists_bound_of_continuous
      (hs.continuous_deriv (by simp))
    refine ⟨ψ,max C 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),hs,
      fun z=>⟨ψ.nonneg,ψ.le_one⟩,?_,?_,?_,?_⟩
    · intro z hz
      apply ψ.one_of_mem_closedBall
      simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero,ψ] using hz
    · intro z hz
      apply ψ.zero_of_le_dist
      simpa only [Real.dist_eq,sub_zero,ψ] using hz
    · intro z
      have hb : |deriv (ψ:ℝ→ℝ) z|≤C := by simpa only [Real.norm_eq_abs] using hC z
      exact hb.trans (le_max_left _ _)
    · intro z hz
      have hzero : ψ z=0 := ψ.zero_of_le_dist (by simpa only [Real.dist_eq,sub_zero,ψ] using hz)
      have hmin : IsLocalMin (ψ:ℝ→ℝ) z := by
        apply Eventually.of_forall
        intro y
        rw [hzero]
        exact ψ.nonneg
      exact hmin.deriv_eq_zero
  have smooth_composed_cutoff {d:ℕ}(V:UnitAddTorus (Fin d)→ℝ)(hV:TorusSmooth V)
      (hpos:∀x,0≤V x)(T:ℝ)(hT:0<T)(ψ:ℝ→ℝ)(hψ:ContDiff ℝ ∞ ψ)
      (hbound:∀z,0≤ψ z ∧ ψ z≤1)(hone:∀z,|z|≤1/2→ψ z=1)
      (hzero:∀z,1≤|z|→ψ z=0)(D:ℝ)(hD:0≤D)(hder:∀z,|deriv ψ z|≤D)
      (hderzero:∀z,1≤|z|→deriv ψ z=0) :
      let χ:=fun x=>ψ (V x/T)
      TorusSmooth χ ∧ (∀x,0≤χ x ∧ χ x≤1) ∧
      (∀x,V x≤T/2→χ x=1) ∧ (∀x,T≤V x→χ x=0) ∧
      (∀x,TorusGradient χ x=(deriv ψ (V x/T)/T) • TorusGradient V x) ∧
      (∀x,‖TorusGradient χ x‖^2 ≤ (D/T)^2 *
        ({x|V x<T}.indicator (fun x=>‖TorusGradient V x‖^2)) x) := by
    let χ:=fun x=>ψ (V x/T)
    have hc : TorusSmooth χ := hψ.comp (hV.div_const T)
    have hratio (x) : 0≤V x/T := div_nonneg (hpos x) hT.le
    have hz (x)(hx:T≤V x) : 1≤|V x/T| := by
      rw [abs_of_nonneg (hratio x)]
      exact (one_le_div hT).mpr hx
    have hg (x) : TorusGradient χ x=(deriv ψ (V x/T)/T) • TorusGradient V x := by
      obtain ⟨y,rfl⟩ := (quotient d).surjective x
      ext j
      rw [gradient_on_lift]
      have hdV := (hV.differentiable (by simp) y).hasFDerivAt.mul_const T⁻¹
      simp only [←div_eq_mul_inv] at hdV
      have hd := ((hψ.differentiable (by simp) (V (TorusLift d y)/T)).hasDerivAt).comp_hasFDerivAt y hdV
      change HasFDerivAt (fun z=>χ (TorusLift d z)) _ y at hd
      rw [hd.fderiv]
      simp only [PiLp.smul_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,χ]
      rw [gradient_on_lift]
      ring
    refine ⟨hc,fun x=>hbound _,?_,fun x hx=>hzero _ (hz x hx),hg,?_⟩
    · intro x hx
      apply hone
      rw [abs_of_nonneg (hratio x)]
      apply (div_le_iff₀ hT).mpr
      linarith
    · intro x
      rw [hg]
      by_cases hx:V x<T
      · have hmem : x∈{x|V x<T} := hx
        rw [Set.indicator_of_mem hmem,norm_smul,Real.norm_eq_abs,abs_div,abs_of_pos hT,mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity)
          (div_le_div_of_nonneg_right (hder _) hT.le) 2) (sq_nonneg _)
      · have hd0 := hderzero (V x/T) (hz x (le_of_not_gt hx))
        have hnot : x∉{x|V x<T} := hx
        simp only [hd0,zero_div,zero_smul,norm_zero,zero_pow (by norm_num : 2≠0),Set.indicator_of_notMem hnot,mul_zero,le_refl]

  have smooth_cutoff_integral_bounds {d:ℕ}(V:UnitAddTorus (Fin d)→ℝ)(hV:TorusSmooth V)
      (K L T D:ℝ)(hK:0≤K)(hL:0≤L)(hT:0<T)(hD:0≤D)
      (hpos:∀x,0≤V x)(hmean:(∫x,V x)≤K)(hLap:∀x,TorusLaplacian V x≤L)
      (χ:UnitAddTorus (Fin d)→ℝ)(hχ:TorusSmooth χ)(hbound:∀x,0≤χ x ∧ χ x≤1)
      (hone:∀x,V x≤T/2→χ x=1)
      (hgrad:∀x,‖TorusGradient χ x‖^2 ≤ (D/T)^2 *
        ({x|V x<T}.indicator (fun x=>‖TorusGradient V x‖^2)) x) :
      (∫x,(χ x-1)^2)≤4*K/T ∧ (∫x,‖TorusGradient χ x‖^2)≤D^2*L/T := by
    have hVcont := torus_smooth_continuous hV
    have hgcont := gradient_energy_continuous hV
    have hgi : Integrable (fun x=>‖TorusGradient V x‖^2) volume :=
      hgcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hs : MeasurableSet {x|V x<T} := (isOpen_lt hVcont continuous_const).measurableSet
    have hcap := CapacitaryPotentialCutoff d V hV K L hK hL hpos hmean hLap T hT
    constructor
    · have hmincont : Continuous (fun x=>(min (V x/T) 1)^2) :=
        ((hVcont.div_const T).min continuous_const).pow 2
      have hmini : Integrable (fun x=>(min (V x/T) 1)^2) volume :=
        hmincont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      have hpoint (x) : (χ x-1)^2≤4*(min (V x/T) 1)^2 := by
        by_cases hx:V x≤T/2
        · rw [hone x hx]
          simp only [sub_self,zero_pow (by norm_num : 2≠0)]
          positivity
        · have hr : 1/2≤V x/T := by
            apply (le_div_iff₀ hT).mpr
            linarith [lt_of_not_ge hx]
          have hm : 1/2≤min (V x/T) 1 := le_min hr (by norm_num)
          have hb := hbound x
          nlinarith [sq_nonneg (min (V x/T) 1-1/2)]
      have hmono := integral_mono_of_nonneg
        (Eventually.of_forall fun x=>sq_nonneg (χ x-1)) (hmini.const_mul 4)
        (Eventually.of_forall hpoint)
      rw [integral_const_mul] at hmono
      have hh := mul_le_mul_of_nonneg_left hcap.2 (show 0≤(4:ℝ) by norm_num)
      have he : 4*(K/T)=4*K/T := by ring
      exact hmono.trans (hh.trans_eq he)
    · have hmono := integral_mono_of_nonneg
        (Eventually.of_forall fun x=>sq_nonneg ‖TorusGradient χ x‖)
        ((hgi.indicator hs).const_mul ((D/T)^2)) (Eventually.of_forall hgrad)
      rw [integral_const_mul,integral_indicator hs] at hmono
      have hh := mul_le_mul_of_nonneg_left hcap.1 (sq_nonneg (D/T))
      have he : (D/T)^2*(L*T)=D^2*L/T := by field_simp
      exact hmono.trans (hh.trans_eq he)

  obtain ⟨ψ,D,hD,hψ,hbound,hone,hzero,hder,hderzero⟩ := smooth_capacity_bump
  refine ⟨ψ,D,hD,hψ,?_⟩
  intro d V hV K L hK hL hpos hmean hLap T hT
  let χ:=fun x=>ψ (V x/T)
  have hc := smooth_composed_cutoff V hV hpos T hT ψ hψ hbound hone hzero D hD.le hder hderzero
  have hi := smooth_cutoff_integral_bounds V hV K L T D hK hL hT hD.le hpos hmean hLap χ
    hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.2.2
  exact ⟨hc.1,hc.2.1,hc.2.2.1,hc.2.2.2.1,hi.1,hi.2⟩
