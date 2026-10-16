module

public import Tablet.TorusIntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section
open MeasureTheory
open scoped ContDiff
-- [TABLET NODE: CapacitaryPotentialCutoff]
theorem CapacitaryPotentialCutoff (d : ℕ) (V : UnitAddTorus (Fin d) → ℝ)
    (hV : TorusSmooth V) (K L : ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hpos : ∀ x, 0 ≤ V x) (hmean : (∫ x, V x ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d)))) ≤ K)
    (hLap : ∀ x, TorusLaplacian V x ≤ L) (T : ℝ) (hT : 0 < T) :
    (∫ x in {x | V x < T}, ‖TorusGradient V x‖ ^ 2 ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d)))) ≤ L * T ∧
    (∫ x, (min (V x / T) 1) ^ 2 ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d)))) ≤ K / T := by
-- BODY
  classical
  have cutoff_smooth_estimate (d : ℕ) (V : UnitAddTorus (Fin d) → ℝ)
      (hV : TorusSmooth V) (L T δ : ℝ) (hL : 0 ≤ L) (hT : 0 < T) (hδ : 0 < δ)
      (hpos : ∀ x, 0 ≤ V x) (hLap : ∀ x, TorusLaplacian V x ≤ L) :
      let a := fun x => (1 + (T-V x) / Real.sqrt ((T-V x)^2+δ^2)) / 2
      (∫ x, a x * ‖TorusGradient V x‖^2) ≤ L*(T+δ/2) := by
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
    
    haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
      rw [AddCircle.volume_eq_smul_haarAddCircle]
      simpa using (inferInstance : IsProbabilityMeasure AddCircle.haarAddCircle)
    haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) :=
      inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin d =>
        (volume : Measure (AddCircle (1 : ℝ))))))
    let b := fun x => T - V x
    let r := fun x => Real.sqrt ((b x)^2+δ^2)
    let χ := fun x => (r x+b x)/2
    let a := fun x => (1+b x/r x)/2
    have hrpos (x) : 0 < (b x)^2+δ^2 := by nlinarith [sq_nonneg (b x)]
    have hr (x) : 0 < r x := Real.sqrt_pos.2 (hrpos x)
    have hr2 (x) : (r x)^2 = (b x)^2+δ^2 := Real.sq_sqrt (hrpos x).le
    have hrabs (x) : |b x| ≤ r x := by
      apply (sq_le_sq₀ (abs_nonneg _) (hr x).le).mp
      rw [sq_abs, hr2]
      nlinarith [sq_nonneg δ]
    have χbounds (x) : 0 ≤ χ x ∧ χ x ≤ T+δ/2 := by
      have hru : r x ≤ |b x|+δ := by
        apply (sq_le_sq₀ (hr x).le (by positivity)).mp
        rw [hr2]
        nlinarith [sq_abs (b x), mul_nonneg (abs_nonneg (b x)) hδ.le]
      have hb : b x ≤ T := sub_le_self _ (hpos x)
      constructor
      · dsimp [χ]
        linarith [neg_abs_le (b x), hrabs x]
      · dsimp [χ]
        by_cases hx : 0 ≤ b x
        · rw [abs_of_nonneg hx] at hru
          linarith
        · rw [abs_of_neg (lt_of_not_ge hx)] at hru
          linarith
    have habounds (x) : 0 ≤ a x ∧ a x ≤ 1 := by
      have hb : -(r x) ≤ b x ∧ b x ≤ r x := abs_le.mp (hrabs x)
      dsimp [a]
      constructor
      · apply div_nonneg _ (by norm_num)
        have hneg : -1 ≤ b x/r x := (le_div_iff₀ (hr x)).2 (by nlinarith [hb.1])
        linarith
      · rw [div_le_iff₀ (by norm_num : (0:ℝ)<2)]
        have h := (div_le_one (hr x)).2 hb.2
        linarith
    have hb : TorusSmooth b := contDiff_const.sub hV
    have hχ : TorusSmooth χ := by
      exact (((hb.pow 2).add contDiff_const).sqrt
        (fun y => ne_of_gt (hrpos (TorusLift d y)))).add hb |>.div_const 2
    have grad (x) (j : Fin d) : TorusGradient χ x j = -a x * TorusGradient V x j := by
      obtain ⟨y,rfl⟩ := (quotient d).surjective x
      simp_rw [gradient_on_lift]
      have hdV := (hV.differentiable (by simp) y).hasFDerivAt
      have hdb := (hasFDerivAt_const T y).sub hdV
      have hdq := (hdb.pow 2).add (hasFDerivAt_const (δ^2) y)
      have hd := ((hdq.sqrt (ne_of_gt (hrpos (TorusLift d y)))).add hdb).mul_const (1/2 : ℝ)
      have heq : (fun z => (Real.sqrt ((T-V (TorusLift d z))^2+δ^2)+(T-V (TorusLift d z)))*(1/2)) =
          (fun z => χ (TorusLift d z)) := by
        funext z
        simp [χ,r,b,div_eq_mul_inv]
      simp only [Pi.add_apply, Pi.sub_apply] at hd
      rw [heq] at hd
      rw [hd.fderiv]
      simp
      dsimp [a,r,b]
      field_simp
      <;> ring
    have hip := TorusIntegrationByParts d χ V hχ hV
    simp_rw [grad] at hip
    have hs (x) : -(∑ j : Fin d, -a x * TorusGradient V x j * TorusGradient V x j) =
        a x * ‖TorusGradient V x‖^2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [← integral_neg] at hip
    simp_rw [hs] at hip
    have hg : Continuous (TorusGradient V) :=
      (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).continuous_symm.comp
        (continuous_pi (fun j => continuous (gradient_smooth hV j)))
    have ha : Continuous a := by
      exact (continuous_const.add ((continuous hb).div
        ((continuous hb).pow 2 |>.add continuous_const |>.sqrt)
        (fun x => ne_of_gt (hr x)))).div_const 2
    have hai : Integrable (fun x => a x * ‖TorusGradient V x‖^2) volume :=
      (ha.mul (hg.norm.pow 2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hχi : Integrable χ volume :=
      (continuous hχ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hχL : Integrable (fun x => χ x * L) volume := hχi.mul_const L
    have cl : Continuous (TorusLaplacian V) := by
      change Continuous (fun x => TorusLaplacian V x)
      simp_rw [laplacian_gradient_sum]
      exact continuous_finsetSum _ (fun j _ => continuous (gradient_smooth (gradient_smooth hV j) j))
    have hproduct : Integrable (fun x => χ x * TorusLaplacian V x) volume :=
      ((continuous hχ).mul cl).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    calc
      (∫ x, a x * ‖TorusGradient V x‖^2) = ∫ x, χ x * TorusLaplacian V x := hip.symm
      _ ≤ ∫ x, χ x * L := integral_mono hproduct hχL
        (fun x => mul_le_mul_of_nonneg_left (hLap x) (χbounds x).1)
      _ ≤ ∫ _ : UnitAddTorus (Fin d), (T+δ/2)*L :=
        integral_mono hχL (integrable_const _) (fun x =>
          mul_le_mul_of_nonneg_right (χbounds x).2 hL)
      _ = L*(T+δ/2) := by simp [mul_comm]

  have cutoff_weight_bounds (b δ : ℝ) (hδ : 0 < δ) :
      0 ≤ (1+b/Real.sqrt (b^2+δ^2))/2 ∧ (1+b/Real.sqrt (b^2+δ^2))/2 ≤ 1 := by
    have hp : 0 < b^2+δ^2 := by nlinarith [sq_nonneg b]
    have hr : 0 < Real.sqrt (b^2+δ^2) := Real.sqrt_pos.2 hp
    have ha : |b| ≤ Real.sqrt (b^2+δ^2) := by
      apply (sq_le_sq₀ (abs_nonneg _) hr.le).mp
      rw [sq_abs, Real.sq_sqrt hp.le]
      nlinarith [sq_nonneg δ]
    have hb := abs_le.mp ha
    have hl : -1 ≤ b/Real.sqrt (b^2+δ^2) :=
      (le_div_iff₀ hr).2 (by nlinarith [hb.1])
    have hu := (div_le_one hr).2 hb.2
    constructor <;> linarith

  have cutoff_weight_limit (b : ℝ) :
      Filter.Tendsto (fun n : ℕ => (1+b/Real.sqrt (b^2+(1/((n:ℝ)+1))^2))/2)
        Filter.atTop (nhds (if 0 < b then 1 else if b=0 then (1/2:ℝ) else 0)) := by
    have hδ : Filter.Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) Filter.atTop (nhds (0:ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    by_cases hb : b=0
    · subst b
      simpa using (tendsto_const_nhds (x := (1/2:ℝ)))
    · have hden := Real.continuous_sqrt.continuousAt.tendsto.comp
        ((tendsto_const_nhds (x := b^2)).add (hδ.pow 2))
      have hden' : Filter.Tendsto (fun n : ℕ => Real.sqrt (b^2+(1/((n:ℝ)+1))^2))
          Filter.atTop (nhds |b|) := by simpa [Function.comp_def, Real.sqrt_sq_eq_abs] using hden
      have h := ((tendsto_const_nhds (x := (1:ℝ))).add
        ((tendsto_const_nhds (x := b)).div hden' (abs_ne_zero.mpr hb))).div_const 2
      by_cases hbp : 0 < b
      · simpa [hbp, hb, abs_of_pos hbp] using h
      · have hbn : b < 0 := lt_of_le_of_ne (le_of_not_gt hbp) hb
        simpa [hbp, hb, abs_of_neg hbn] using h

  have cutoff_limit_estimate (d : ℕ) (V : UnitAddTorus (Fin d) → ℝ)
      (hV : TorusSmooth V) (L T : ℝ) (hL : 0 ≤ L) (hT : 0 < T)
      (hpos : ∀ x, 0 ≤ V x) (hLap : ∀ x, TorusLaplacian V x ≤ L)
      (cV : Continuous V) (cg : Continuous (TorusGradient V)) :
      (∫ x in {x | V x < T}, ‖TorusGradient V x‖^2) ≤ L*T := by
    let δ := fun n : ℕ => 1/((n:ℝ)+1)
    let a := fun n (x : UnitAddTorus (Fin d)) => (1+(T-V x)/Real.sqrt ((T-V x)^2+(δ n)^2))/2
    let a0 := fun x => if V x < T then (1:ℝ) else if V x=T then 1/2 else 0
    let e := fun x => ‖TorusGradient V x‖^2
    have hδ (n) : 0 < δ n := by dsimp [δ]; positivity
    have hab (n x) : 0 ≤ a n x ∧ a n x ≤ 1 := cutoff_weight_bounds _ _ (hδ n)
    have ca (n) : Continuous (a n) := by
      have hr (x) : Real.sqrt ((T-V x)^2+(δ n)^2) ≠ 0 := by
        apply ne_of_gt
        apply Real.sqrt_pos.2
        nlinarith [sq_nonneg (T-V x), hδ n]
      exact (continuous_const.add ((continuous_const.sub cV).div
        (((continuous_const.sub cV).pow 2).add continuous_const).sqrt hr)).div_const 2
    have cei : Integrable e volume :=
      (cg.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have caei (n) : Integrable (fun x => a n x*e x) volume :=
      ((ca n).mul (cg.norm.pow 2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hbound (n) : ∀ᵐ x ∂volume, ‖a n x*e x‖ ≤ e x := by
      apply Filter.Eventually.of_forall
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hab n x).1 (sq_nonneg _))]
      simpa using mul_le_mul_of_nonneg_right (hab n x).2 (sq_nonneg ‖TorusGradient V x‖)
    have hlim (x) : Filter.Tendsto (fun n => a n x*e x) Filter.atTop (nhds (a0 x*e x)) := by
      have h := (cutoff_weight_limit (T-V x)).mul_const (e x)
      simpa only [a, δ, a0, sub_pos, sub_eq_zero, eq_comm] using h
    have hdct := tendsto_integral_of_dominated_convergence e
      (fun n => (caei n).aestronglyMeasurable) cei hbound
        (Filter.Eventually.of_forall hlim)
    have hle : (∫ x, a0 x*e x) ≤ L*T := by
      have hc : Filter.Tendsto (fun n => L*(T+δ n/2)) Filter.atTop (nhds (L*T)) := by
        have hz : Filter.Tendsto δ Filter.atTop (nhds (0:ℝ)) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have h := (tendsto_const_nhds (x := L)).mul ((tendsto_const_nhds (x := T)).add
          (hz.div_const 2))
        simpa [δ] using h
      apply le_of_tendsto_of_tendsto hdct hc
      exact Filter.Eventually.of_forall (fun n => cutoff_smooth_estimate d V hV L T (δ n) hL hT (hδ n) hpos hLap)
    have a0b (x) : 0 ≤ a0 x ∧ a0 x ≤ 1 := by dsimp [a0]; split_ifs <;> norm_num
    have ha0i : Integrable (fun x => a0 x*e x) volume := by
      have ha0m : Measurable a0 := by
        exact measurable_const.ite (measurableSet_lt cV.measurable measurable_const)
          (measurable_const.ite (measurableSet_eq_fun cV.measurable measurable_const) measurable_const)
      apply cei.bdd_mul ha0m.aestronglyMeasurable
      apply Filter.Eventually.of_forall
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg (a0b x).1]
      exact (a0b x).2
    have hset : MeasurableSet {x | V x < T} := measurableSet_lt cV.measurable measurable_const
    rw [← integral_indicator hset]
    calc
      (∫ x, ({x | V x<T} : Set _).indicator e x) ≤ ∫ x, a0 x*e x := by
        apply integral_mono (cei.indicator hset) ha0i
        intro x
        by_cases hx : V x<T
        · simp [Set.indicator_of_mem, hx, a0]
        · simp only [Set.indicator_of_notMem (show x ∉ {x | V x<T} from hx)]
          exact mul_nonneg (a0b x).1 (sq_nonneg _)
      _ ≤ L*T := hle

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
  
  have cg : Continuous (TorusGradient V) :=
    (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).continuous_symm.comp
      (continuous_pi (fun j => continuous (gradient_smooth hV j)))
  constructor
  · exact cutoff_limit_estimate d V hV L T hL hT hpos hLap (continuous hV) cg
  · have cp : Continuous (fun x => (min (V x/T) 1)^2) :=
      (((continuous hV).div_const T).min continuous_const).pow 2
    have hpi : Integrable (fun x => (min (V x/T) 1)^2) volume :=
      cp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hVi : Integrable V volume :=
      (continuous hV).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    calc
      (∫ x, (min (V x/T) 1)^2) ≤ ∫ x, V x/T := by
        apply integral_mono hpi (hVi.div_const T)
        intro x
        change (min (V x/T) 1)^2 ≤ V x/T
        have hx : 0 ≤ V x/T := div_nonneg (hpos x) hT.le
        by_cases h : V x/T ≤ 1
        · rw [min_eq_left h]
          nlinarith
        · rw [min_eq_right (le_of_not_ge h)]
          norm_num
          exact le_of_not_ge h
      _ = (∫ x,V x)/T := integral_div T V
      _ ≤ K/T := div_le_div_of_nonneg_right hmean hT.le
