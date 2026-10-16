module

public import Tablet.CapacitaryPotentialCutoff
public import Tablet.TiltNormalization
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.WithLp

@[expose] public section
open MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 6000000
-- [TABLET NODE: ClipCutoffApproximation]
theorem ClipCutoffApproximation (d : ℕ) (V f : UnitAddTorus (Fin d) → ℝ)
    (hV : TorusSmooth V) (hf : TorusSmooth f) (K L R T : ℝ)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hR : 0 < R) (hT : 0 < T)
    (hpos : ∀ x, 0 ≤ V x) (hmean : (∫ x, V x) ≤ K)
    (hLap : ∀ x, TorusLaplacian V x ≤ L) :
    let ν := NormalizedTilt MeasureTheory.volume (fun x => Real.exp (-V x))
    let h := fun x => max (-R) (min (f x) R)
    let χ := fun x => max (1 - V x / T) 0
    let F := fun x => χ x * h x
    let W := fun x => χ x • (if |f x| < R then TorusGradient f x else 0) -
      (h x / T) • (if V x < T then TorusGradient V x else 0)
    MeasureTheory.MemLp F 2 MeasureTheory.volume ∧
    MeasureTheory.MemLp W 2 MeasureTheory.volume ∧
    (∃ u : ℕ → UnitAddTorus (Fin d) → ℝ,
      (∀ n, TorusSmooth (u n)) ∧
      Filter.Tendsto (fun n => ∫ x, (u n x - F x)^2) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun n => ∫ x, ‖TorusGradient (u n) x - W x‖^2)
        Filter.atTop (nhds 0)) ∧
    (∫ x, (h x - F x)^2 ∂ν) ≤ R^2 * Real.exp K * K / T ∧
    (∫ x, ‖W x‖^2) ≤
      2 * Real.exp T * (∫ x, ‖TorusGradient f x‖^2 ∂ν) + 2 * R^2 * L / T := by
-- BODY
  classical
  let delta (n : ℕ) : ℝ := 1/((n:ℝ)+1)
  let radius (b δ : ℝ) : ℝ := Real.sqrt ((b-δ)^2+δ^4)
  let sigma (b δ : ℝ) : ℝ := (1+(b-δ)/radius b δ)/2
  let soft (b δ : ℝ) : ℝ := (radius b δ+(b-δ))/2

  have delta_pos (n : ℕ) : 0 < delta n := by unfold delta; positivity
  have delta_le (n : ℕ) : delta n ≤ 1 := by
    unfold delta
    rw [div_le_one (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have delta_limit : Filter.Tendsto delta Filter.atTop (nhds (0:ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat

  have radius_pos (b δ : ℝ) (hδ : 0 < δ) : 0 < radius b δ := by
    apply Real.sqrt_pos.mpr
    nlinarith [sq_nonneg (b-δ), pow_pos hδ 4]
  have radius_abs (b δ : ℝ) (hδ : 0 < δ) : |b-δ| ≤ radius b δ := by
    apply (sq_le_sq₀ (abs_nonneg _) (radius_pos b δ hδ).le).mp
    dsimp only [radius]
    rw [sq_abs, Real.sq_sqrt (by positivity)]
    exact le_add_of_nonneg_right (pow_nonneg hδ.le 4)
  have sigma_bounds (b δ : ℝ) (hδ : 0 < δ) : 0 ≤ sigma b δ ∧ sigma b δ ≤ 1 := by
    have hp := radius_pos b δ hδ
    have hb := abs_le.mp (radius_abs b δ hδ)
    have hl : -1 ≤ (b-δ)/radius b δ := (le_div_iff₀ hp).mpr (by linarith [hb.1])
    have hu : (b-δ)/radius b δ ≤ 1 := (div_le_one hp).mpr hb.2
    dsimp [sigma]
    constructor <;> linarith
  have radius_upper (b δ : ℝ) (hδ : 0 < δ) : radius b δ ≤ |b-δ|+δ^2 := by
    apply (sq_le_sq₀ (radius_pos b δ hδ).le (by positivity)).mp
    dsimp only [radius]
    rw [Real.sq_sqrt (by positivity)]
    nlinarith [sq_abs (b-δ), mul_nonneg (abs_nonneg (b-δ)) (sq_nonneg δ)]
  have soft_nonneg (b δ : ℝ) (hδ : 0 < δ) : 0 ≤ soft b δ := by
    have ha := radius_abs b δ hδ
    dsimp [soft]
    linarith [neg_abs_le (b-δ)]
  have soft_upper (b δ : ℝ) (hδ : 0 < δ) (hle : δ ≤ 1) : soft b δ ≤ |b|+1 := by
    have hu := radius_upper b δ hδ
    have ha : |b-δ| ≤ |b|+δ := by simpa [abs_of_pos hδ] using abs_sub b δ
    have hb : b ≤ |b| := le_abs_self b
    have hd2 : δ^2 ≤ 1 := by nlinarith
    dsimp [soft]
    linarith

  have radius_limit (b : ℝ) : Filter.Tendsto (fun n => radius b (delta n)) Filter.atTop (nhds |b|) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp
      (((tendsto_const_nhds (x:=b)).sub delta_limit).pow 2 |>.add (delta_limit.pow 4))
    simpa [radius, Function.comp_def, Real.sqrt_sq_eq_abs] using h
  have soft_limit (b : ℝ) : Filter.Tendsto (fun n => soft b (delta n)) Filter.atTop (nhds (max b 0)) := by
    have h := ((radius_limit b).add ((tendsto_const_nhds (x:=b)).sub delta_limit)).div_const 2
    have he : (|b|+b)/2=max b 0 := by
      by_cases hb : 0 ≤ b
      · rw [abs_of_nonneg hb,max_eq_left hb]; ring
      · rw [abs_of_neg (lt_of_not_ge hb),max_eq_right (le_of_not_ge hb)]; ring
    simpa [soft,he] using h
  have radius_zero (δ : ℝ) (hδ : 0 < δ) : radius 0 δ = δ*Real.sqrt (1+δ^2) := by
    unfold radius
    have he : (0-δ)^2+δ^4=δ^2*(1+δ^2) := by ring
    rw [he, Real.sqrt_mul (sq_nonneg δ), Real.sqrt_sq_eq_abs, abs_of_pos hδ]
  have sigma_zero (δ : ℝ) (hδ : 0 < δ) : sigma 0 δ=(1-1/Real.sqrt (1+δ^2))/2 := by
    dsimp only [sigma]
    rw [radius_zero δ hδ]
    have hd : δ ≠ 0 := ne_of_gt hδ
    have hr : Real.sqrt (1+δ^2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    field_simp
    <;> ring
  have sigma_limit (b : ℝ) : Filter.Tendsto (fun n => sigma b (delta n)) Filter.atTop
      (nhds (if 0 < b then (1:ℝ) else 0)) := by
    by_cases hb : b=0
    · subst b
      simp_rw [sigma_zero _ (delta_pos _)]
      have hr := Real.continuous_sqrt.continuousAt.tendsto.comp
        ((tendsto_const_nhds (x := (1:ℝ))).add (delta_limit.pow 2))
      have h := ((tendsto_const_nhds (x := (1:ℝ))).sub
        ((tendsto_const_nhds (x := (1:ℝ))).div hr (by norm_num))).div_const 2
      simpa [Function.comp_def] using h
    · have h := ((tendsto_const_nhds (x := (1:ℝ))).add
        (((tendsto_const_nhds (x := b)).sub delta_limit).div (radius_limit b) (abs_ne_zero.mpr hb))).div_const 2
      by_cases hp : 0 < b
      · simpa [sigma,hp,abs_of_pos hp,hb] using h
      · have hn : b < 0 := lt_of_le_of_ne (le_of_not_gt hp) hb
        simpa [sigma,hp,abs_of_neg hn,div_neg,hb] using h

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

  have soft_comp_facts {d : ℕ} (v : UnitAddTorus (Fin d) → ℝ)
      (hv : TorusSmooth v) (δ : ℝ) (hδ : 0 < δ) :
      TorusSmooth (fun x=>soft (v x) δ) ∧
      ∀ x, TorusGradient (fun x=>soft (v x) δ) x = sigma (v x) δ • TorusGradient v x := by
    have hp (x) : 0 < (v x-δ)^2+δ^4 := by positivity
    have hs : TorusSmooth (fun x=>soft (v x) δ) := by
      change ContDiff ℝ ∞ (fun y=>soft (v (TorusLift d y)) δ)
      simpa [soft,radius] using ((((hv.sub contDiff_const).pow 2).add contDiff_const).sqrt
        (fun y=>ne_of_gt (hp (TorusLift d y)))).add (hv.sub contDiff_const) |>.div_const 2
    refine ⟨hs,?_⟩
    intro x
    obtain ⟨y,rfl⟩ := (quotient d).surjective x
    ext j
    simp_rw [gradient_on_lift]
    have hdv := (hv.differentiable (by simp) y).hasFDerivAt
    have hdb := hdv.sub (hasFDerivAt_const δ y)
    have hdq := (hdb.pow 2).add (hasFDerivAt_const (δ^4) y)
    have hd := ((hdq.sqrt (ne_of_gt (hp (TorusLift d y)))).add hdb).mul_const (1/2:ℝ)
    have he : (fun z=>(Real.sqrt ((v (TorusLift d z)-δ)^2+δ^4)+(v (TorusLift d z)-δ))*(1/2))=
        (fun z=>soft (v (TorusLift d z)) δ) := by funext z; simp [soft,radius];ring
    simp only [Pi.add_apply,Pi.sub_apply] at hd
    rw [he] at hd
    rw [hd.fderiv]
    simp [gradient_on_lift]
    dsimp [sigma,radius]
    field_simp
    <;> ring

  have gradient_add {d : ℕ} {f h : UnitAddTorus (Fin d) → ℝ}
      (hf : TorusSmooth f) (hh : TorusSmooth h) (x : UnitAddTorus (Fin d)) :
      TorusGradient (fun x=>f x+h x) x = TorusGradient f x+TorusGradient h x := by
    obtain ⟨y,rfl⟩ := (quotient d).surjective x
    ext j
    simp_rw [gradient_on_lift]
    have hd := (hf.differentiable (by simp) y).hasFDerivAt.add
      (hh.differentiable (by simp) y).hasFDerivAt
    change HasFDerivAt (fun z=>f (TorusLift d z)+h (TorusLift d z)) _ y at hd
    rw [hd.fderiv]
    simp [gradient_on_lift]
  have gradient_sub {d : ℕ} {f h : UnitAddTorus (Fin d) → ℝ}
      (hf : TorusSmooth f) (hh : TorusSmooth h) (x : UnitAddTorus (Fin d)) :
      TorusGradient (fun x=>f x-h x) x = TorusGradient f x-TorusGradient h x := by
    obtain ⟨y,rfl⟩ := (quotient d).surjective x
    ext j
    simp_rw [gradient_on_lift]
    have hd := (hf.differentiable (by simp) y).hasFDerivAt.sub
      (hh.differentiable (by simp) y).hasFDerivAt
    change HasFDerivAt (fun z=>f (TorusLift d z)-h (TorusLift d z)) _ y at hd
    rw [hd.fderiv]
    simp [gradient_on_lift]
  have gradient_const {d : ℕ} (c : ℝ) (x : UnitAddTorus (Fin d)) :
      TorusGradient (fun _=>c) x = 0 := by
    ext j
    simp [TorusGradient]
  have gradient_div {d : ℕ} {f : UnitAddTorus (Fin d) → ℝ}
      (hf : TorusSmooth f) (c : ℝ) (x : UnitAddTorus (Fin d)) :
      TorusGradient (fun x=>f x/c) x = (1/c) • TorusGradient f x := by
    obtain ⟨y,rfl⟩ := (quotient d).surjective x
    ext j
    simp_rw [gradient_on_lift]
    have hd := (hf.differentiable (by simp) y).hasFDerivAt.mul_const c⁻¹
    change HasFDerivAt (fun z=>f (TorusLift d z)*c⁻¹) _ y at hd
    have he : (fun z=>f (TorusLift d z)*c⁻¹)=(fun z=>f (TorusLift d z)/c) := by funext z; simp [div_eq_mul_inv]
    rw [he] at hd
    rw [hd.fderiv]
    simp [gradient_on_lift]

  have potential_normalizer (d : ℕ) (V : UnitAddTorus (Fin d) → ℝ)
      (hV : TorusSmooth V) (K : ℝ) (hpos : ∀ x, 0 ≤ V x) (hmean : (∫ x,V x) ≤ K) :
      let Z := ∫ x, Real.exp (-V x)
      Real.exp (-K) ≤ Z ∧ Z ≤ 1 ∧ 0 < Z ∧
      (∀ x, Real.exp (-V x)/Z ≤ Real.exp K) ∧
      (∀ t x, V x ≤ t → Real.exp (-t) ≤ Real.exp (-V x)/Z) := by
    classical
    haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
      rw [AddCircle.volume_eq_smul_haarAddCircle]
      simpa using (inferInstance : IsProbabilityMeasure AddCircle.haarAddCircle)
    haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) :=
      inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin d =>
        (volume : Measure (AddCircle (1 : ℝ))))))
    let Z := ∫ x, Real.exp (-V x)
    have hVi : Integrable V volume :=
      (continuous hV).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hwi : Integrable (fun x => Real.exp (-V x)) volume :=
      (Real.continuous_exp.comp (continuous hV).neg).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hj : Real.exp (-(∫ x,V x)) ≤ Z := by
      have h := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn
        isClosed_univ (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) hVi.neg hwi
      simpa only [Pi.neg_apply, integral_neg] using h
    have hzl : Real.exp (-K) ≤ Z :=
      (Real.exp_le_exp.mpr (neg_le_neg hmean)).trans hj
    have hZ : 0 < Z := (Real.exp_pos _).trans_le hzl
    have hzu : Z ≤ 1 := by
      have h := integral_mono hwi (integrable_const (1:ℝ))
        (fun x => Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hpos x)))
      simpa using h
    refine ⟨hzl,hzu,hZ,?_,?_⟩
    · intro x
      rw [div_le_iff₀ hZ]
      calc
        Real.exp (-V x) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hpos x))
        _ = Real.exp K * Real.exp (-K) := by rw [← Real.exp_add]; simp
        _ ≤ Real.exp K * Z := mul_le_mul_of_nonneg_left hzl (Real.exp_pos _).le
    · intro t x hx
      rw [le_div_iff₀ hZ]
      calc
        Real.exp (-t)*Z ≤ Real.exp (-t) := mul_le_of_le_one_right (Real.exp_pos _).le hzu
        _ ≤ Real.exp (-V x) := Real.exp_le_exp.mpr (neg_le_neg hx)

  have clip_scalar (t R : ℝ) (hR : 0 < R) :
      max (t+R) 0-max (R-t) 0-t=max (-R) (min t R) := by
    by_cases hl : t ≤ -R
    · rw [max_eq_right (by linarith), max_eq_left (by linarith),min_eq_left (by linarith),max_eq_left hl]
      ring
    · by_cases hu : R ≤ t
      · rw [max_eq_left (by linarith),max_eq_right (by linarith),min_eq_right hu,max_eq_right (by linarith)]
        ring
      · rw [max_eq_left (by linarith),max_eq_left (by linarith),min_eq_left (le_of_not_ge hu),max_eq_right (le_of_not_ge hl)]
        ring
  have clip_coefficient (t R : ℝ) (hR : 0 < R) :
      (if 0 < R+t then (1:ℝ) else 0)+(if 0 < R-t then (1:ℝ) else 0)-1=
        if |t| < R then 1 else 0 := by
    by_cases ht : |t| < R
    · have hb := abs_lt.mp ht
      simp [ht,show 0<R+t by linarith,show 0<R-t by linarith]
    · by_cases hs : 0 ≤ t
      · have ha : R ≤ t := by rw [abs_of_nonneg hs] at ht; exact le_of_not_gt ht
        simp [ht,show 0<R+t by linarith,show ¬0<R-t by linarith]
      · have ha : t ≤ -R := by rw [abs_of_neg (lt_of_not_ge hs)] at ht; linarith
        simp [ht,show ¬0<R+t by linarith,show 0<R-t by linarith]
  have clip_bounds (t R : ℝ) (hR : 0 < R) : |max (-R) (min t R)| ≤ R := by
    apply abs_le.mpr
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_right _ _)
  have chi_bounds (v T : ℝ) (hT : 0 < T) (hv : 0 ≤ v) :
      0 ≤ max (1-v/T) 0 ∧ max (1-v/T) 0 ≤ 1 := by
    constructor
    · exact le_max_right _ _
    · exact max_le (sub_le_self _ (div_nonneg hv hT.le)) (by norm_num)
  have chi_scalar (v T : ℝ) (hT : 0 < T) : max (T-v) 0/T=max (1-v/T) 0 := by
    rw [← max_div_div_right hT.le (T-v) 0]
    simp only [zero_div]
    congr 1
    field_simp

  have smooth_clip_graph (d : ℕ) (V f : UnitAddTorus (Fin d) → ℝ)
      (hV : TorusSmooth V) (hf : TorusSmooth f) (R T : ℝ)
      (hR : 0 < R) (hT : 0 < T) (hpos : ∀ x, 0 ≤ V x) :
      let h := fun x=>max (-R) (min (f x) R)
      let χ := fun x=>max (1-V x/T) 0
      let F := fun x=>χ x*h x
      let W := fun x=>χ x • (if |f x|<R then TorusGradient f x else 0)-
        (h x/T) • (if V x<T then TorusGradient V x else 0)
      MemLp F 2 volume ∧ MemLp W 2 volume ∧
      ∃ u : ℕ → UnitAddTorus (Fin d) → ℝ,
        (∀ n,TorusSmooth (u n)) ∧
        Filter.Tendsto (fun n=>∫ x,(u n x-F x)^2) Filter.atTop (nhds 0) ∧
        Filter.Tendsto (fun n=>∫ x,‖TorusGradient (u n) x-W x‖^2) Filter.atTop (nhds 0) := by
    classical
    haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1:ℝ))) := by
      rw [AddCircle.volume_eq_smul_haarAddCircle]
      simpa using (inferInstance : IsProbabilityMeasure AddCircle.haarAddCircle)
    haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) :=
      inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _:Fin d=>
        (volume : Measure (AddCircle (1:ℝ))))))
    let h := fun x=>max (-R) (min (f x) R)
    let χ := fun x=>max (1-V x/T) 0
    let F := fun x=>χ x*h x
    let W := fun x=>χ x • (if |f x|<R then TorusGradient f x else 0)-
        (h x/T) • (if V x<T then TorusGradient V x else 0)
    have cf := continuous hf
    have cV := continuous hV
    have cgf : Continuous (TorusGradient f) :=
      (PiLp.homeomorph 2 (fun _:Fin d=>ℝ)).continuous_symm.comp
        (continuous_pi (fun j=>continuous (gradient_smooth hf j)))
    have cgV : Continuous (TorusGradient V) :=
      (PiLp.homeomorph 2 (fun _:Fin d=>ℝ)).continuous_symm.comp
        (continuous_pi (fun j=>continuous (gradient_smooth hV j)))
    obtain ⟨Cf,hCf⟩ := isCompact_univ.bddAbove_image cf.norm.continuousOn
    obtain ⟨CV,hCV⟩ := isCompact_univ.bddAbove_image cV.norm.continuousOn
    obtain ⟨Df,hDf⟩ := isCompact_univ.bddAbove_image cgf.norm.continuousOn
    obtain ⟨DV,hDV⟩ := isCompact_univ.bddAbove_image cgV.norm.continuousOn
    have bf x : |f x| ≤ Cf := by simpa using hCf ⟨x,Set.mem_univ _,rfl⟩
    have bV x : |V x| ≤ CV := by simpa using hCV ⟨x,Set.mem_univ _,rfl⟩
    have bgf x : ‖TorusGradient f x‖ ≤ Df := hDf ⟨x,Set.mem_univ _,rfl⟩
    have bgV x : ‖TorusGradient V x‖ ≤ DV := hDV ⟨x,Set.mem_univ _,rfl⟩
    have hCf0 : 0 ≤ Cf := (abs_nonneg (f 0)).trans (bf 0)
    have hCV0 : 0 ≤ CV := (abs_nonneg (V 0)).trans (bV 0)
    have hDf0 : 0 ≤ Df := (norm_nonneg _).trans (bgf 0)
    have hDV0 : 0 ≤ DV := (norm_nonneg _).trans (bgV 0)
    have ch : Continuous h := continuous_const.max (cf.min continuous_const)
    have cχ : Continuous χ := (continuous_const.sub (cV.div_const T)).max continuous_const
    have bh x : |h x| ≤ R := clip_bounds _ _ hR
    have bχ x : 0 ≤ χ x ∧ χ x ≤ 1 := chi_bounds _ _ hT (hpos x)
    have bF x : |F x| ≤ R := by
      change |χ x*h x| ≤ R
      rw [abs_mul,abs_of_nonneg (bχ x).1]
      exact (mul_le_mul_of_nonneg_left (bh x) (bχ x).1).trans (mul_le_of_le_one_left hR.le (bχ x).2)
    have mW : Measurable W := by
      exact cχ.measurable.smul (cgf.measurable.ite (measurableSet_lt cf.abs.measurable measurable_const) measurable_const) |>.sub
        ((ch.div_const T).measurable.smul (cgV.measurable.ite (measurableSet_lt cV.measurable measurable_const) measurable_const))
    have bW x : ‖W x‖ ≤ Df+(R/T)*DV := by
      have b1 : ‖if |f x|<R then TorusGradient f x else 0‖ ≤ Df := by split_ifs <;> simp_all
      have b2 : ‖if V x<T then TorusGradient V x else 0‖ ≤ DV := by split_ifs <;> simp_all
      calc
        ‖W x‖ ≤ ‖χ x • (if |f x|<R then TorusGradient f x else 0)‖+
          ‖(h x/T) • (if V x<T then TorusGradient V x else 0)‖ := norm_sub_le _ _
        _ ≤ Df+(R/T)*DV := by
          simp only [norm_smul,Real.norm_eq_abs,abs_div,abs_of_pos hT,abs_of_nonneg (bχ x).1]
          exact add_le_add ((mul_le_mul_of_nonneg_left b1 (bχ x).1).trans
            (mul_le_of_le_one_left hDf0 (bχ x).2))
            (mul_le_mul (div_le_div_of_nonneg_right (bh x) hT.le) b2 (norm_nonneg _) (by positivity))
    have hFLp : MemLp F 2 volume := MemLp.of_bound (cχ.mul ch).aestronglyMeasurable R
      (Filter.Eventually.of_forall fun x=>by simpa only [Real.norm_eq_abs] using bF x)
    have hWLp : MemLp W 2 volume := MemLp.of_bound mW.aestronglyMeasurable (Df+(R/T)*DV)
      (Filter.Eventually.of_forall bW)
    let a := fun n x=>soft (f x+R) (delta n)-soft (R-f x) (delta n)-f x
    let b := fun n x=>soft (T-V x) (delta n)/T
    let u := fun n x=>b n x*a n x
    let ca := fun n x=>sigma (f x+R) (delta n)+sigma (R-f x) (delta n)-1
    let cb := fun n x=>sigma (T-V x) (delta n)/T
    have hfp : TorusSmooth (fun x=>f x+R) := hf.add contDiff_const
    have hfm : TorusSmooth (fun x=>R-f x) := contDiff_const.sub hf
    have hvb : TorusSmooth (fun x=>T-V x) := contDiff_const.sub hV
    have ha n : TorusSmooth (a n) :=
      ((soft_comp_facts (fun x=>f x+R) hfp _ (delta_pos n)).1.sub
        (soft_comp_facts (fun x=>R-f x) hfm _ (delta_pos n)).1).sub hf
    have hb n : TorusSmooth (b n) :=
      (soft_comp_facts (fun x=>T-V x) hvb _ (delta_pos n)).1.div_const T
    have hu n : TorusSmooth (u n) := (hb n).mul (ha n)
    have grada n x : TorusGradient (a n) x=ca n x • TorusGradient f x := by
      change TorusGradient (fun x=>soft (f x+R) (delta n)-soft (R-f x) (delta n)-f x) x=_
      rw [gradient_sub (f:=fun x=>soft (f x+R) (delta n)-soft (R-f x) (delta n)) ((soft_comp_facts (fun x=>f x+R) hfp _ (delta_pos n)).1.sub
        (soft_comp_facts (fun x=>R-f x) hfm _ (delta_pos n)).1) hf,
        gradient_sub (f:=fun x=>soft (f x+R) (delta n)) (h:=fun x=>soft (R-f x) (delta n)) (soft_comp_facts (fun x=>f x+R) hfp _ (delta_pos n)).1
          (soft_comp_facts (fun x=>R-f x) hfm _ (delta_pos n)).1]
      rw [(soft_comp_facts (fun x=>f x+R) hfp _ (delta_pos n)).2,
        (soft_comp_facts (fun x=>R-f x) hfm _ (delta_pos n)).2,
        gradient_add (h:=fun _=>R) hf contDiff_const,gradient_sub (f:=fun _=>R) contDiff_const hf,gradient_const]
      ext j
      simp [ca]
      ring
    have gradb n x : TorusGradient (b n) x=-(cb n x) • TorusGradient V x := by
      change TorusGradient (fun x=>soft (T-V x) (delta n)/T) x=_
      rw [gradient_div (f:=fun x=>soft (T-V x) (delta n)) (soft_comp_facts (fun x=>T-V x) hvb _ (delta_pos n)).1,
        (soft_comp_facts (fun x=>T-V x) hvb _ (delta_pos n)).2,
        gradient_sub (f:=fun _=>T) contDiff_const hV,gradient_const]
      ext j
      simp [cb]
      ring
    have gradu n x : TorusGradient (u n) x=(b n x*ca n x) • TorusGradient f x-
        (a n x*cb n x) • TorusGradient V x := by
      ext j
      rw [gradient_mul (hb n) (ha n),grada,gradb]
      simp
      ring
    have la x : Filter.Tendsto (fun n=>a n x) Filter.atTop (nhds (h x)) := by
      have hh := ((soft_limit (f x+R)).sub (soft_limit (R-f x))).sub_const (f x)
      simpa only [a,h,clip_scalar _ R hR] using hh
    have lb x : Filter.Tendsto (fun n=>b n x) Filter.atTop (nhds (χ x)) := by
      have hh := (soft_limit (T-V x)).div_const T
      simpa only [b,χ,chi_scalar _ T hT] using hh
    have lca x : Filter.Tendsto (fun n=>ca n x) Filter.atTop (nhds (if |f x|<R then (1:ℝ) else 0)) := by
      have hh := ((sigma_limit (f x+R)).add (sigma_limit (R-f x))).sub_const 1
      simpa only [ca,add_comm (f x) R,clip_coefficient _ R hR] using hh
    have lcb x : Filter.Tendsto (fun n=>cb n x) Filter.atTop (nhds ((if V x<T then (1:ℝ) else 0)/T)) := by
      simpa only [cb,sub_pos] using (sigma_limit (T-V x)).div_const T
    have lu x : Filter.Tendsto (fun n=>u n x) Filter.atTop (nhds (F x)) := (lb x).mul (la x)
    have lgu x : Filter.Tendsto (fun n=>TorusGradient (u n) x) Filter.atTop (nhds (W x)) := by
      simp_rw [gradu]
      have hh := (((lb x).mul (lca x)).smul_const (TorusGradient f x)).sub
        (((la x).mul (lcb x)).smul_const (TorusGradient V x))
      convert hh using 1
      dsimp [W]
      split_ifs <;> simp [div_eq_mul_inv]
    let A : ℝ := 3*Cf+2*R+2
    let B : ℝ := (T+CV+1)/T
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have ba n x : |a n x| ≤ A := by
      have h1 := soft_upper (f x+R) (delta n) (delta_pos n) (delta_le n)
      have h2 := soft_upper (R-f x) (delta n) (delta_pos n) (delta_le n)
      have h1a : |f x+R| ≤ Cf+R := (abs_add_le _ _).trans (by simpa [abs_of_pos hR] using add_le_add_right (bf x) R)
      have h2a : |R-f x| ≤ R+Cf := (abs_sub _ _).trans (by simpa [abs_of_pos hR] using add_le_add_left (bf x) R)
      have hab := abs_sub (soft (f x+R) (delta n)-soft (R-f x) (delta n)) (f x)
      have hab2 := abs_sub (soft (f x+R) (delta n)) (soft (R-f x) (delta n))
      rw [abs_of_nonneg (soft_nonneg _ _ (delta_pos n)),abs_of_nonneg (soft_nonneg _ _ (delta_pos n))] at hab2
      dsimp [a,A]
      linarith [bf x]
    have bb n x : 0 ≤ b n x ∧ b n x ≤ B := by
      constructor
      · exact div_nonneg (soft_nonneg _ _ (delta_pos n)) hT.le
      · have hh := soft_upper (T-V x) (delta n) (delta_pos n) (delta_le n)
        have hab : |T-V x| ≤ T+CV := (abs_sub _ _).trans (by simpa [abs_of_pos hT] using add_le_add_left (bV x) T)
        exact div_le_div_of_nonneg_right (by linarith) hT.le
    have bca n x : |ca n x| ≤ 1 := by
      have h1 := sigma_bounds (f x+R) (delta n) (delta_pos n)
      have h2 := sigma_bounds (R-f x) (delta n) (delta_pos n)
      apply abs_le.mpr
      dsimp [ca]
      constructor <;> linarith
    have bcb n x : 0 ≤ cb n x ∧ cb n x ≤ 1/T := by
      have hh := sigma_bounds (T-V x) (delta n) (delta_pos n)
      exact ⟨div_nonneg hh.1 hT.le,div_le_div_of_nonneg_right hh.2 hT.le⟩
    have bu n x : |u n x| ≤ B*A := by
      change |b n x*a n x| ≤ B*A
      rw [abs_mul,abs_of_nonneg (bb n x).1]
      exact mul_le_mul (bb n x).2 (ba n x) (abs_nonneg _) hB
    let D : ℝ := B*Df+(A/T)*DV
    have hD : 0 ≤ D := by dsimp [D]; positivity
    have bgu n x : ‖TorusGradient (u n) x‖ ≤ D := by
      rw [gradu]
      calc
        _ ≤ ‖(b n x*ca n x) • TorusGradient f x‖+‖(a n x*cb n x) • TorusGradient V x‖ := norm_sub_le _ _
        _ ≤ B*Df+(A/T)*DV := by
          simp only [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (bb n x).1,abs_of_nonneg (bcb n x).1]
          have h1 : b n x*|ca n x| ≤ B := (mul_le_mul_of_nonneg_left (bca n x) (bb n x).1).trans (by simpa using (bb n x).2)
          have h2 : |a n x| * cb n x ≤ A/T := by
            have hh := mul_le_mul (ba n x) (bcb n x).2 (bcb n x).1 hA
            simpa [div_eq_mul_inv] using hh
          exact add_le_add (mul_le_mul h1 (bgf x) (norm_nonneg _) hB)
            (mul_le_mul h2 (bgV x) (norm_nonneg _) (by positivity))
    have cgu n : Continuous (TorusGradient (u n)) :=
      (PiLp.homeomorph 2 (fun _:Fin d=>ℝ)).continuous_symm.comp
        (continuous_pi (fun j=>continuous (gradient_smooth (hu n) j)))
    have bd1 n : ∀ᵐ x ∂volume, ‖(u n x-F x)^2‖ ≤ (B*A+R)^2 := by
      apply Filter.Eventually.of_forall
      intro x
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have hb : |u n x-F x| ≤ B*A+R := (abs_sub _ _).trans (add_le_add (bu n x) (bF x))
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hb 2
    have bd2 n : ∀ᵐ x ∂volume, ‖‖TorusGradient (u n) x-W x‖^2‖ ≤ (D+(Df+(R/T)*DV))^2 := by
      apply Filter.Eventually.of_forall
      intro x
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (add_le_add (bgu n x) (bW x))) 2
    have lim1 x : Filter.Tendsto (fun n=>(u n x-F x)^2) Filter.atTop (nhds (0:ℝ)) := by
      simpa using ((lu x).sub_const (F x)).pow 2
    have lim2 x : Filter.Tendsto (fun n=>‖TorusGradient (u n) x-W x‖^2) Filter.atTop (nhds (0:ℝ)) := by
      simpa using ((lgu x).sub_const (W x)).norm.pow 2
    have hi1 := tendsto_integral_of_dominated_convergence (fun _ : UnitAddTorus (Fin d)=>(B*A+R)^2)
      (fun n=>(((continuous (hu n)).sub (cχ.mul ch)).pow 2).aestronglyMeasurable)
      (integrable_const _) bd1 (Filter.Eventually.of_forall lim1)
    have hi2 := tendsto_integral_of_dominated_convergence (fun _ : UnitAddTorus (Fin d)=>(D+(Df+(R/T)*DV))^2)
      (fun n=>(((cgu n).measurable.sub mW).norm.pow_const 2).aestronglyMeasurable)
      (integrable_const _) bd2 (Filter.Eventually.of_forall lim2)
    refine ⟨hFLp,hWLp,u,hu,?_,?_⟩
    · simpa using hi1
    · simpa only [integral_zero,Pi.sub_apply,h,χ,F,W] using hi2

  have clip_cutoff_estimates (d : ℕ) (V f : UnitAddTorus (Fin d) → ℝ)
      (hV : TorusSmooth V) (hf : TorusSmooth f) (K L R T : ℝ)
      (hK : 0 ≤ K) (hL : 0 ≤ L) (hR : 0 < R) (hT : 0 < T)
      (hpos : ∀ x, 0 ≤ V x) (hmean : (∫ x,V x) ≤ K)
      (hLap : ∀ x,TorusLaplacian V x ≤ L) :
      let ν := NormalizedTilt volume (fun x=>Real.exp (-V x))
      let h := fun x=>max (-R) (min (f x) R)
      let χ := fun x=>max (1-V x/T) 0
      let F := fun x=>χ x*h x
      let W := fun x=>χ x • (if |f x|<R then TorusGradient f x else 0)-
        (h x/T) • (if V x<T then TorusGradient V x else 0)
      (∫ x,(h x-F x)^2 ∂ν) ≤ R^2*Real.exp K*K/T ∧
      (∫ x,‖W x‖^2) ≤ 2*Real.exp T*(∫ x,‖TorusGradient f x‖^2 ∂ν)+2*R^2*L/T := by
    classical
    haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1:ℝ))) := by
      rw [AddCircle.volume_eq_smul_haarAddCircle]
      simpa using (inferInstance : IsProbabilityMeasure AddCircle.haarAddCircle)
    haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) :=
      inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _:Fin d=>
        (volume : Measure (AddCircle (1:ℝ))))))
    let ν := NormalizedTilt volume (fun x=>Real.exp (-V x))
    let h := fun x=>max (-R) (min (f x) R)
    let χ := fun x=>max (1-V x/T) 0
    let F := fun x=>χ x*h x
    let W := fun x=>χ x • (if |f x|<R then TorusGradient f x else 0)-
        (h x/T) • (if V x<T then TorusGradient V x else 0)
    let w := fun x=>Real.exp (-V x)
    let Z := ∫ x,w x
    let ρ := fun x=>w x/Z
    have cz := potential_normalizer d V hV K hpos hmean
    have hZ : 0 < Z := cz.2.2.1
    have cV := continuous hV
    have cf := continuous hf
    have ch : Continuous h := continuous_const.max (cf.min continuous_const)
    have cχ : Continuous χ := (continuous_const.sub (cV.div_const T)).max continuous_const
    have cw : Continuous w := Real.continuous_exp.comp cV.neg
    have cρ : Continuous ρ := cw.div_const Z
    have wi : Integrable w volume := cw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have tnorm := TiltNormalization volume w cw.measurable
      (Filter.Eventually.of_forall fun x=>(Real.exp_pos _).le) wi hZ
    haveI : IsProbabilityMeasure ν := tnorm.1
    have transport (g : UnitAddTorus (Fin d) → ℝ) (cg : Continuous g) :
        (∫ x,g x ∂ν)=∫ x,g x*ρ x := by
      have h := (tnorm.2 g cg.measurable
        ((cg.mul cw).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).2
      rw [h,← integral_div]
      congr 1
      funext x
      dsimp [ρ,Z]
      ring
    have rhopos x : 0 ≤ ρ x := div_nonneg (Real.exp_pos _).le hZ.le
    have rhoupper x : ρ x ≤ Real.exp K := cz.2.2.2.1 x
    have rholo x (hx : V x<T) : Real.exp (-T) ≤ ρ x := cz.2.2.2.2 T x hx.le
    have cap := CapacitaryPotentialCutoff d V hV K L hK hL hpos hmean hLap T hT
    have cg (v : UnitAddTorus (Fin d) → ℝ) (hv : TorusSmooth v) : Continuous (TorusGradient v) :=
      (PiLp.homeomorph 2 (fun _:Fin d=>ℝ)).continuous_symm.comp
        (continuous_pi (fun j=>continuous (gradient_smooth hv j)))
    have cgfi : Integrable (fun x=>‖TorusGradient f x‖^2*ρ x) volume :=
      (((cg f hf).norm.pow 2).mul cρ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have cgVi : Integrable (fun x=>‖TorusGradient V x‖^2) volume :=
      ((cg V hV).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hset : MeasurableSet {x | V x<T} := measurableSet_lt cV.measurable measurable_const
    let eV := fun x=>({x | V x<T}:Set _).indicator (fun x=>‖TorusGradient V x‖^2) x
    have eVi : Integrable eV volume := cgVi.indicator hset
    have hWi : Integrable (fun x=>‖W x‖^2) volume :=
      (smooth_clip_graph d V f hV hf R T hR hT hpos).2.1.norm.integrable_sq
    constructor
    · have cm : Continuous (fun x=>(min (V x/T) 1)^2) := ((cV.div_const T).min continuous_const).pow 2
      have ce : Continuous (fun x=>(h x-F x)^2) := (ch.sub (cχ.mul ch)).pow 2
      rw [transport _ ce]
      have hp x : (h x-F x)^2*ρ x ≤ (R^2*Real.exp K)*(min (V x/T) 1)^2 := by
        have hb := clip_bounds (f x) R hR
        have he : 1-χ x=min (V x/T) 1 := by
          dsimp [χ]
          by_cases hh : V x/T ≤ 1
          · rw [max_eq_left (by linarith),min_eq_left hh];ring
          · rw [max_eq_right (by linarith),min_eq_right (le_of_not_ge hh)];ring
        have hid : (h x-F x)^2=(h x)^2*(min (V x/T) 1)^2 := by
          have hh : h x-F x=h x*(1-χ x) := by dsimp [F];ring
          rw [hh,he,mul_pow]
        have hhs : (h x)^2 ≤ R^2 := by simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hb 2
        rw [hid]
        have hs : (min (V x/T) 1)^2 ≥ 0 := sq_nonneg _
        calc
          (h x)^2*(min (V x/T) 1)^2*ρ x ≤ R^2*(min (V x/T) 1)^2*Real.exp K :=
            mul_le_mul (mul_le_mul_of_nonneg_right hhs hs) (rhoupper x) (rhopos x) (mul_nonneg (sq_nonneg _) hs)
          _ = _ := by ring
      calc
        (∫ x,(h x-F x)^2*ρ x) ≤ ∫ x,(R^2*Real.exp K)*(min (V x/T) 1)^2 :=
          integral_mono ((ce.mul cρ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
            (((continuous_const.mul cm)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hp
        _ = (R^2*Real.exp K)*(∫ x,(min (V x/T) 1)^2) := integral_const_mul _ _
        _ ≤ (R^2*Real.exp K)*(K/T) := mul_le_mul_of_nonneg_left cap.2 (by positivity)
        _ = R^2*Real.exp K*K/T := by ring
    · have first x : ‖χ x • (if |f x|<R then TorusGradient f x else 0)‖^2 ≤
          Real.exp T*(‖TorusGradient f x‖^2*ρ x) := by
        by_cases hx : V x<T
        · have hχ := chi_bounds (V x) T hT (hpos x)
          have hn : ‖if |f x|<R then TorusGradient f x else 0‖ ≤ ‖TorusGradient f x‖ := by split_ifs <;> simp
          have hl : 1 ≤ Real.exp T*ρ x := by
            calc
              1 = Real.exp T*Real.exp (-T) := by rw [← Real.exp_add];simp
              _ ≤ Real.exp T*ρ x := mul_le_mul_of_nonneg_left (rholo x hx) (Real.exp_pos _).le
          have hb : ‖χ x • (if |f x|<R then TorusGradient f x else 0)‖ ≤ ‖TorusGradient f x‖ := by
            rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hχ.1]
            exact (mul_le_mul_of_nonneg_left hn hχ.1).trans (mul_le_of_le_one_left (norm_nonneg _) hχ.2)
          calc
            _ ≤ ‖TorusGradient f x‖^2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
            _ ≤ Real.exp T*(‖TorusGradient f x‖^2*ρ x) := by nlinarith [mul_le_mul_of_nonneg_right hl (sq_nonneg ‖TorusGradient f x‖)]
        · have hh : χ x=0 := by
            dsimp [χ]
            rw [max_eq_right]
            exact sub_nonpos.mpr ((le_div_iff₀ hT).mpr (by linarith))
          rw [hh,zero_smul,norm_zero,zero_pow (by norm_num)]
          exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (sq_nonneg _) (rhopos x))
      have second x : ‖(h x/T) • (if V x<T then TorusGradient V x else 0)‖^2 ≤ (R/T)^2*eV x := by
        by_cases hx : V x<T
        · simp only [hx,ite_true,norm_smul,Real.norm_eq_abs,eV,Set.indicator_of_mem (show x∈{x|V x<T} from hx),abs_div,abs_of_pos hT,mul_pow]
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right (clip_bounds _ R hR) hT.le) 2) (sq_nonneg _)
        · simp [hx,eV]
      have hp x : ‖W x‖^2 ≤ 2*Real.exp T*(‖TorusGradient f x‖^2*ρ x)+2*(R/T)^2*eV x := by
        let a := χ x • (if |f x|<R then TorusGradient f x else 0)
        let b := (h x/T) • (if V x<T then TorusGradient V x else 0)
        have hb : ‖W x‖^2 ≤ 2*‖a‖^2+2*‖b‖^2 := by
          have hh := pow_le_pow_left₀ (norm_nonneg (a-b)) (norm_sub_le a b) 2
          change ‖a-b‖^2 ≤ _
          nlinarith [sq_nonneg (‖a‖-‖b‖)]
        exact hb.trans (by nlinarith [first x,second x])
      have htr : (∫ x,‖TorusGradient f x‖^2 ∂ν)=(∫ x,‖TorusGradient f x‖^2*ρ x) :=
        transport (fun x=>‖TorusGradient f x‖^2) ((cg f hf).norm.pow 2)
      rw [htr]
      calc
        (∫ x,‖W x‖^2) ≤ ∫ x,2*Real.exp T*(‖TorusGradient f x‖^2*ρ x)+2*(R/T)^2*eV x :=
          integral_mono hWi ((cgfi.const_mul _).add (eVi.const_mul _)) hp
        _ = 2*Real.exp T*(∫ x,‖TorusGradient f x‖^2*ρ x)+2*(R/T)^2*(∫ x,eV x) := by
          rw [integral_add (cgfi.const_mul _) (eVi.const_mul _),integral_const_mul,integral_const_mul]
        _ ≤ 2*Real.exp T*(∫ x,‖TorusGradient f x‖^2*ρ x)+2*(R/T)^2*(L*T) := by
          apply add_le_add le_rfl
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          simpa only [eV,integral_indicator hset] using cap.1
        _ = 2*Real.exp T*(∫ x,‖TorusGradient f x‖^2*ρ x)+2*R^2*L/T := by
          field_simp [ne_of_gt hT]
          <;> ring

  have hgraph := smooth_clip_graph d V f hV hf R T hR hT hpos
  have hest := clip_cutoff_estimates d V f hV hf K L R T hK hL hR hT hpos hmean hLap
  exact ⟨hgraph.1,hgraph.2.1,hgraph.2.2,hest⟩
