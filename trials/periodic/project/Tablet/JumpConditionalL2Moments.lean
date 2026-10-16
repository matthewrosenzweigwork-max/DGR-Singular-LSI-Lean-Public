import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Tablet.JumpOperator
import Tablet.BoundedBackground
import Tablet.TiltNormalization
import Mathlib.MeasureTheory.Group.Integral
import Tablet.ReplacementJointBalance

open MeasureTheory ProbabilityTheory

-- [TABLET NODE: JumpConditionalL2Moments]
theorem JumpConditionalL2Moments (d N : ℕ) (hN : 2 ≤ N) (l u β : ℝ)
    (q : BoundedBackground d l u) (hβ : 0 ≤ β)
    (G : UnitAddTorus (Fin d) → ℝ) (hG : Measurable G)
    (hGi : Integrable G volume) (hGn : ∀ x, 0 ≤ G x)
    (hGe : ∀ x, G (-x) = G x) :
    let P := CanonicalLaw (N := N) G q.density β
    let Z := fun (X : Configuration d N) (i : Fin N) =>
      ∫ z, Real.exp (-ConditionalPotential G β X i z) * q.density z
    let ν := fun (X : Configuration d N) (i : Fin N) =>
      NormalizedTilt volume (fun z => q.density z * Real.exp (-ConditionalPotential G β X i z))
    ∀ f, MemLp f 2 P → ∀ i,
      Integrable (fun X => ∫ z, (f (Replacement X i z))^2 *
        (q.density z * Real.exp (-ConditionalPotential G β X i z))) P ∧
      Integrable (fun X => ∫ z, f (Replacement X i z) *
        (q.density z * Real.exp (-ConditionalPotential G β X i z))) P ∧
      ∀ᵐ X ∂P,
      MemLp (fun z => f (Replacement X i z)) 2 (ν X i) ∧
      Z X i * variance (fun z => f (Replacement X i z)) (ν X i) =
        (∫ z, (f (Replacement X i z))^2 *
          (q.density z * Real.exp (-ConditionalPotential G β X i z))) -
        (∫ z, f (Replacement X i z) *
          (q.density z * Real.exp (-ConditionalPotential G β X i z)))^2 / Z X i := by
-- BODY
  classical
  have dominated_marginal_pullback {α Ω : Type} [MeasurableSpace α] [MeasurableSpace Ω]
    {μ : Measure α} {J : Measure Ω} (r : Ω → α) (hr : AEMeasurable r J)
      (hdom : J.map r ≤ μ) (f : α → ℝ) (hf : MemLp f 2 μ) :
      MemLp (f ∘ r) 2 J ∧
        (∫ x, f (r x) ^ 2 ∂J) ≤ ∫ a, f a ^ 2 ∂μ := by
    have hfr : MemLp f 2 (J.map r) := MemLp.mono_measure hdom hf
    refine ⟨hfr.comp_of_map hr, ?_⟩
    rw [← integral_map hr hfr.integrable_sq.aestronglyMeasurable]
    exact integral_mono_measure hdom (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
      hf.integrable_sq

  have weighted_integrable_fubini {Ω B : Type} [MeasurableSpace Ω] [MeasurableSpace B]
    {μ : Measure Ω} {ν : Measure B} [SFinite μ] [SFinite ν] (w : Ω × B → ℝ) (hw : Measurable w)
      (hwn : ∀ᵐ p ∂μ.prod ν, 0 ≤ w p) (h : Ω × B → ℝ)
      (hh : Integrable h ((μ.prod ν).withDensity (fun p => ENNReal.ofReal (w p)))) :
      Integrable (fun p => w p * h p) (μ.prod ν) ∧
        (∫ p, h p ∂((μ.prod ν).withDensity (fun p => ENNReal.ofReal (w p)))) =
          ∫ X, (∫ z, w (X, z) * h (X, z) ∂ν) ∂μ ∧
        (∀ᵐ X ∂μ, Integrable (fun z => w (X, z) * h (X, z)) ν) := by
    have hfin : ∀ᵐ p ∂μ.prod ν, ENNReal.ofReal (w p) < ⊤ :=
      Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
    have hreal : (fun p => (ENNReal.ofReal (w p)).toReal • h p) =ᵐ[μ.prod ν]
        (fun p => w p * h p) := by
      filter_upwards [hwn] with p hp
      simp only [ENNReal.toReal_ofReal hp, smul_eq_mul]
    have hint : Integrable (fun p => w p * h p) (μ.prod ν) :=
      ((integrable_withDensity_iff_integrable_smul' hw.ennreal_ofReal hfin).mp hh).congr hreal
    refine ⟨hint, ?_, hint.prod_right_ae⟩
    calc
      _ = ∫ p, (ENNReal.ofReal (w p)).toReal • h p ∂μ.prod ν :=
        integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal hfin _
      _ = ∫ p, w p * h p ∂μ.prod ν := integral_congr_ae hreal
      _ = ∫ X, (∫ z, w (X, z) * h (X, z) ∂ν) ∂μ := integral_prod _ hint

  have weighted_square_fubini {Ω B : Type} [MeasurableSpace Ω] [MeasurableSpace B]
    {μ : Measure Ω} {ν : Measure B} [SFinite μ] [SFinite ν] (w : Ω × B → ℝ) (hw : Measurable w)
      (hwn : ∀ᵐ p ∂μ.prod ν, 0 ≤ w p) (h : Ω × B → ℝ)
      (hh : MemLp h 2 ((μ.prod ν).withDensity (fun p => ENNReal.ofReal (w p)))) :
      Integrable (fun p => w p * h p ^ 2) (μ.prod ν) ∧
        (∫ p, h p ^ 2 ∂((μ.prod ν).withDensity (fun p => ENNReal.ofReal (w p)))) =
          ∫ X, (∫ z, w (X, z) * h (X, z) ^ 2 ∂ν) ∂μ ∧
        (∀ᵐ X ∂μ, Integrable (fun z => w (X, z) * h (X, z) ^ 2) ν) := by
    have hfin : ∀ᵐ p ∂μ.prod ν, ENNReal.ofReal (w p) < ⊤ :=
      Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
    have hreal : (fun p => (ENNReal.ofReal (w p)).toReal • h p ^ 2) =ᵐ[μ.prod ν]
        (fun p => w p * h p ^ 2) := by
      filter_upwards [hwn] with p hp
      simp only [ENNReal.toReal_ofReal hp, smul_eq_mul]
    have hint : Integrable (fun p => w p * h p ^ 2) (μ.prod ν) :=
      ((integrable_withDensity_iff_integrable_smul' hw.ennreal_ofReal hfin).mp
        hh.integrable_sq).congr hreal
    refine ⟨hint, ?_, hint.prod_right_ae⟩
    calc
      _ = ∫ p, (ENNReal.ofReal (w p)).toReal • h p ^ 2 ∂μ.prod ν :=
        integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal hfin _
      _ = ∫ p, w p * h p ^ 2 ∂μ.prod ν := integral_congr_ae hreal
      _ = ∫ X, (∫ z, w (X, z) * h (X, z) ^ 2 ∂ν) ∂μ := integral_prod _ hint

  have conditionalNormalizer_bounds  (d N : ℕ) (hN : 2 ≤ N) (l u β : ℝ)
      (q : BoundedBackground d l u) (hβ : 0 ≤ β)
      (G : UnitAddTorus (Fin d) → ℝ) (hG : Measurable G)
      (hGi : Integrable G volume) (hGn : ∀ x, 0 ≤ G x)
      (X : Configuration d N) (i : Fin N) :
      let U := ConditionalPotential G β X i
      let Z := ∫ z, Real.exp (-U z) * q.density z
      Measurable U ∧ Integrable U volume ∧ (∀ z, 0 ≤ U z) ∧
        Integrable (fun z => U z * q.density z) volume ∧
        Integrable (fun z => Real.exp (-U z) * q.density z) volume ∧
        Real.exp (-β*u*(∫ z,G z)) ≤ Z ∧ Z ≤ 1 ∧
        IsProbabilityMeasure (NormalizedTilt volume (fun z => q.density z * Real.exp (-U z))) := by
    classical
    dsimp only
    let U := ConditionalPotential G β X i
    have hnpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
    have hnne : (N : ℝ) ≠ 0 := ne_of_gt hnpos
    have hcoef : 0 ≤ β/(N : ℝ) := div_nonneg hβ hnpos.le
    have hUmeas : Measurable U := by
      dsimp [U,ConditionalPotential]
      apply Measurable.const_mul
      apply Finset.measurable_fun_sum
      intro j hj
      by_cases h : j = i
      · simp only [h,↓reduceIte]
        exact measurable_const
      · simp only [h,↓reduceIte]
        exact hG.comp (measurable_id.sub measurable_const)
    have hterm (j : Fin N) : Integrable
        (fun z => if j = i then (0 : ℝ) else G (z-X j)) volume := by
      by_cases h : j = i
      · simpa only [h,↓reduceIte] using (integrable_const (0 : ℝ) :
          Integrable (fun _ : UnitAddTorus (Fin d) => (0 : ℝ)) volume)
      · simp only [h,↓reduceIte]
        exact (measurePreserving_sub_right volume (X j)).integrable_comp
          hG.aestronglyMeasurable |>.mpr hGi
    have hUint : Integrable U volume :=
      (integrable_finsetSum _ (fun j _ => hterm j)).const_mul _
    have hUpos (z : UnitAddTorus (Fin d)) : 0 ≤ U z := by
      apply mul_nonneg hcoef
      apply Finset.sum_nonneg
      intro j hj
      split_ifs
      · exact le_rfl
      · exact hGn _
    have hUmean : (∫ z,U z) = β/(N : ℝ) * ((N : ℝ)-1) * (∫ z,G z) := by
      dsimp [U,ConditionalPotential]
      rw [integral_const_mul,integral_finsetSum _ (fun j _ => hterm j)]
      have he (j : Fin N) : (∫ z, if j = i then (0 : ℝ) else G (z-X j)) =
          (∫ z,G z) - (if j = i then (∫ z,G z) else 0) := by
        by_cases h : j = i
        · simp [h]
        · simpa [h] using integral_sub_right_eq_self G (X j)
      simp_rw [he]
      simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
        nsmul_eq_mul,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
      ring
    have hqint : Integrable q.density volume := integrable_of_integral_eq_one q.mass
    have hqpos : ∀ᵐ z ∂volume, 0 ≤ q.density z :=
      q.bounds.mono (fun z h => q.lower_pos.le.trans h.1)
    have hqnorm : ∀ᵐ z ∂volume, ‖q.density z‖ ≤ u := by
      filter_upwards [q.bounds,hqpos] with z h hp
      simpa only [Real.norm_eq_abs,abs_of_nonneg hp] using h.2
    have hUqint : Integrable (fun z => U z*q.density z) volume :=
      hUint.mul_bdd q.measurable.aestronglyMeasurable hqnorm
    have hUqbound : (∫ z,U z*q.density z) ≤ β*u*(∫ z,G z) := by
      have h := integral_mono_ae hUqint (hUint.const_mul u) (q.bounds.mono
        (fun z h => by simpa only [mul_comm] using
          mul_le_mul_of_nonneg_left h.2 (hUpos z)))
      rw [integral_const_mul,hUmean] at h
      have hfract : β/(N : ℝ)*((N : ℝ)-1) ≤ β := by
        calc
          _ ≤ β/(N : ℝ)*(N : ℝ) := mul_le_mul_of_nonneg_left
            (sub_le_self _ zero_le_one) hcoef
          _ = β := div_mul_cancel₀ _ hnne
      have hgc : 0 ≤ ∫ z,G z := integral_nonneg hGn
      have hu : 0 ≤ u := zero_le_one.trans q.one_le_upper
      have hm := mul_le_mul_of_nonneg_right hfract (mul_nonneg hu hgc)
      nlinarith
    have hWmeas : Measurable (fun z => Real.exp (-U z)*q.density z) :=
      hUmeas.neg.exp.mul q.measurable
    have hWpos : ∀ᵐ z ∂volume, 0 ≤ Real.exp (-U z)*q.density z :=
      hqpos.mono (fun z h => mul_nonneg (Real.exp_nonneg _) h)
    have hWbound : ∀ᵐ z ∂volume, Real.exp (-U z)*q.density z ≤ q.density z := by
      filter_upwards [hqpos] with z h
      have he : Real.exp (-U z) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hUpos z))
      simpa only [one_mul] using mul_le_mul_of_nonneg_right he h
    have hWint : Integrable (fun z => Real.exp (-U z)*q.density z) volume :=
      hqint.mono' hWmeas.aestronglyMeasurable (by
        filter_upwards [hWpos,hWbound] with z hp hb
        simpa only [Real.norm_eq_abs,abs_of_nonneg hp] using hb)
    have hupper : (∫ z,Real.exp (-U z)*q.density z) ≤ 1 := by
      exact (integral_mono_ae hWint hqint hWbound).trans_eq q.mass
    let b := ∫ z,U z*q.density z
    let F := fun z => (Real.exp (-b)*(1+b))*q.density z -
      Real.exp (-b)*(U z*q.density z)
    have hFint : Integrable F volume :=
      (hqint.const_mul _).sub (hUqint.const_mul _)
    have hFmass : (∫ z,F z) = Real.exp (-b) := by
      rw [integral_sub (hqint.const_mul _) (hUqint.const_mul _)]
      simp only [integral_const_mul,q.mass]
      change Real.exp (-b)*(1+b)*1 - Real.exp (-b)*b = _
      ring
    have hFbound : ∀ᵐ z ∂volume, F z ≤ Real.exp (-U z)*q.density z := by
      filter_upwards [hqpos] with z hq
      have ht : 1-(U z-b) ≤ Real.exp (-(U z-b)) := by
        nlinarith [Real.add_one_le_exp (-(U z-b))]
      have h := mul_le_mul_of_nonneg_left ht (Real.exp_nonneg (-b))
      have he : Real.exp (-b)*Real.exp (-(U z-b)) = Real.exp (-U z) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [he] at h
      have hm := mul_le_mul_of_nonneg_right h hq
      dsimp [F]
      nlinarith
    have hlowb : Real.exp (-b) ≤ ∫ z,Real.exp (-U z)*q.density z := by
      rw [← hFmass]
      exact integral_mono_ae hFint hWint hFbound
    have hlower : Real.exp (-β*u*(∫ z,G z)) ≤ ∫ z,Real.exp (-U z)*q.density z := by
      refine (Real.exp_le_exp.mpr ?_).trans hlowb
      simpa only [neg_mul,b] using neg_le_neg hUqbound
    have hZpos : 0 < ∫ z,Real.exp (-U z)*q.density z := (Real.exp_pos _).trans_le hlower
    refine ⟨hUmeas,hUint,hUpos,hUqint,hWint,hlower,hupper,?_⟩
    have h := (TiltNormalization volume (fun z => Real.exp (-U z)*q.density z)
      hWmeas hWpos hWint hZpos).1
    simpa only [mul_comm] using h

  have weighted_measurability_recovery  {Ω : Type} [MeasurableSpace Ω]
      {μ : Measure Ω} (φ w : Ω → ℝ) (hw : AEStronglyMeasurable w μ)
      (hwp : ∀ᵐ z ∂μ, 0 < w z)
      (hprod : AEStronglyMeasurable (fun z => φ z * w z) μ) :
      AEStronglyMeasurable φ μ := by
    apply (hprod.div₀ hw).congr
    filter_upwards [hwp] with z hz
    exact mul_div_cancel_right₀ (φ z) (ne_of_gt hz)

  have weighted_L2_variance_formula  {Ω : Type} [MeasurableSpace Ω]
      (μ : Measure Ω) (w φ : Ω → ℝ) (hw : Measurable w)
      (hwp : ∀ᵐ x ∂μ, 0 ≤ w x) (hwi : Integrable w μ)
      (hZ : 0 < ∫ x,w x ∂μ) (hφ : Measurable φ)
      (hφw : Integrable (fun x=>φ x*w x) μ)
      (hφ2w : Integrable (fun x=>(φ x)^2*w x) μ) :
      let Z := ∫ x,w x ∂μ
      let ν := NormalizedTilt μ w
      MemLp φ 2 ν ∧ Z*variance φ ν =
        (∫ x,(φ x)^2*w x ∂μ)-(∫ x,φ x*w x ∂μ)^2/Z := by
    dsimp only
    have hTilt := TiltNormalization μ w hw hwp hwi hZ
    haveI := hTilt.1
    have h1 := hTilt.2 φ hφ hφw
    have h2 := hTilt.2 (fun x=>(φ x)^2) (hφ.pow_const 2) hφ2w
    have hLp : MemLp φ 2 (NormalizedTilt μ w) :=
      (memLp_two_iff_integrable_sq hφ.aestronglyMeasurable).mpr h2.1
    refine ⟨hLp,?_⟩
    rw [variance_eq_sub hLp]
    change (∫ x,w x ∂μ)*((∫ x,(φ x)^2 ∂NormalizedTilt μ w)-(∫ x,φ x ∂NormalizedTilt μ w)^2) = _
    rw [h1.2,h2.2]
    have hz : (∫ x,w x ∂μ) ≠ 0 := ne_of_gt hZ
    field_simp
    <;> ring

  have weighted_L2_variance_formula_ae  {Ω : Type} [MeasurableSpace Ω]
      (μ : Measure Ω) (w φ : Ω → ℝ) (hw : Measurable w)
      (hwp : ∀ᵐ x ∂μ, 0 ≤ w x) (hwi : Integrable w μ)
      (hZ : 0 < ∫ x,w x ∂μ) (hφ : AEStronglyMeasurable φ μ)
      (hφw : Integrable (fun x=>φ x*w x) μ)
      (hφ2w : Integrable (fun x=>(φ x)^2*w x) μ) :
      let Z := ∫ x,w x ∂μ
      let ν := NormalizedTilt μ w
      MemLp φ 2 ν ∧ Z*variance φ ν =
        (∫ x,(φ x)^2*w x ∂μ)-(∫ x,φ x*w x ∂μ)^2/Z := by
    dsimp only
    let ψ := hφ.mk φ
    have hm : Measurable ψ := hφ.stronglyMeasurable_mk.measurable
    have he : φ =ᵐ[μ] ψ := hφ.ae_eq_mk
    have he1 : (fun x=>φ x*w x) =ᵐ[μ] (fun x=>ψ x*w x) := he.mul (Filter.EventuallyEq.refl _ _)
    have he2 : (fun x=>(φ x)^2*w x) =ᵐ[μ] (fun x=>(ψ x)^2*w x) := (he.pow_const 2).mul (Filter.EventuallyEq.refl _ _)
    have h := weighted_L2_variance_formula μ w ψ hw hwp hwi hZ hm
      (hφw.congr he1) (hφ2w.congr he2)
    have hac : NormalizedTilt μ w ≪ μ := withDensity_absolutelyContinuous _ _
    have heν : φ =ᵐ[NormalizedTilt μ w] ψ := hac.ae_le he
    refine ⟨(memLp_congr_ae heν).mpr h.1,?_⟩
    rw [variance_congr heν,integral_congr_ae he1,integral_congr_ae he2]
    exact h.2
  classical
  intro P Z ν f hf i
  haveI : IsProbabilityMeasure P := (GibbsNormalizerBounds d N hN l u q G hG hGi 0 β
    (le_refl 0) hβ (Filter.Eventually.of_forall fun x => by simpa using hGn x)).2.2.2
  let J := (P.prod volume).withDensity (fun p : Configuration d N × UnitAddTorus (Fin d) =>
    ENNReal.ofReal (Real.exp (-ConditionalPotential G β p.1 i p.2) * q.density p.2))
  let w := fun p : Configuration d N × UnitAddTorus (Fin d) =>
    Real.exp (-ConditionalPotential G β p.1 i p.2) * q.density p.2
  have hb := ReplacementJointBalance d N hN l u β q hβ G hG hGi hGn hGe i
  haveI : IsFiniteMeasure (J.map Prod.fst) := isFiniteMeasure_of_le P hb.2.1
  haveI : IsFiniteMeasure J := Measure.isFiniteMeasure_of_map measurable_fst.aemeasurable
  have hfr := (dominated_marginal_pullback
    (fun p : Configuration d N × UnitAddTorus (Fin d) => Replacement p.1 i p.2)
    (measurable_fst.comp hb.1.measurable).aemeasurable hb.2.2 f hf).1
  have hUm : Measurable (fun p : Configuration d N × UnitAddTorus (Fin d) =>
      ConditionalPotential G β p.1 i p.2) := by
    unfold ConditionalPotential
    refine measurable_const.mul (Finset.measurable_fun_sum _ fun j _ => ?_)
    split_ifs
    · exact measurable_const
    · exact hG.comp (measurable_snd.sub ((measurable_pi_apply j).comp measurable_fst))
  have hwm : Measurable w := (hUm.neg.exp).mul (q.measurable.comp measurable_snd)
  have hwn : ∀ᵐ p ∂P.prod (volume : Measure (UnitAddTorus (Fin d))), 0 ≤ w p := by
    have hq := (measurePreserving_snd (μ := P) (ν := (volume :
      Measure (UnitAddTorus (Fin d))))).quasiMeasurePreserving.ae q.bounds
    filter_upwards [hq] with p hp
    exact mul_nonneg (Real.exp_pos _).le (q.lower_pos.le.trans hp.1)
  have hfirst := (weighted_integrable_fubini w hwm hwn _ (hfr.integrable (by norm_num))).2.2
  have hsecond := (weighted_square_fubini w hwm hwn _ hfr).2.2
  refine ⟨?_, ?_, ?_⟩
  · simpa only [w, Function.comp_apply, mul_comm, mul_assoc, mul_left_comm] using
      (weighted_square_fubini w hwm hwn _ hfr).1.integral_prod_left
  · simpa only [w, Function.comp_apply, mul_comm, mul_assoc, mul_left_comm] using
      (weighted_integrable_fubini w hwm hwn _ (hfr.integrable (by norm_num))).1.integral_prod_left
  filter_upwards [hfirst, hsecond] with X h1 h2
  have hn := conditionalNormalizer_bounds d N hN l u β q hβ G hG hGi hGn X i
  let φ := fun z => f (Replacement X i z)
  let wx := fun z => q.density z * Real.exp (-ConditionalPotential G β X i z)
  have hxmeas : Measurable wx := q.measurable.mul hn.1.neg.exp
  have hxp : ∀ᵐ z ∂(volume : Measure (UnitAddTorus (Fin d))), 0 < wx z := by
    filter_upwards [q.bounds] with z hz
    exact mul_pos (q.lower_pos.trans_le hz.1) (Real.exp_pos _)
  have hφw : Integrable (fun z => φ z * wx z) volume := h1.congr
    (Filter.Eventually.of_forall fun z => by dsimp [w,φ,wx]; ring)
  have hφ2w : Integrable (fun z => (φ z)^2 * wx z) volume := h2.congr
    (Filter.Eventually.of_forall fun z => by dsimp [w,φ,wx]; ring)
  have hφmeas := weighted_measurability_recovery φ wx hxmeas.aestronglyMeasurable hxp
    hφw.aestronglyMeasurable
  have hwi : Integrable wx volume := hn.2.2.2.2.1.congr
    (Filter.Eventually.of_forall fun z => by dsimp [wx]; ring)
  have hZeq : (∫ z,wx z) = Z X i := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by dsimp [wx,Z]; ring
  have hZp : 0 < ∫ z,wx z := by
    rw [hZeq]
    exact lt_of_lt_of_le (Real.exp_pos _) hn.2.2.2.2.2.1
  have hv := weighted_L2_variance_formula_ae volume wx φ hxmeas
    (hxp.mono fun z hz => hz.le) hwi hZp hφmeas hφw hφ2w
  simpa only [hZeq] using hv
