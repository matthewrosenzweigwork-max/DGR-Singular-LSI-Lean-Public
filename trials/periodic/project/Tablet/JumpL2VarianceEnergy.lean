import Tablet.JumpConditionalL2Moments
import Tablet.ConditionalMeanL2Bound
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Probability.Moments.Variance
open MeasureTheory ProbabilityTheory
set_option maxHeartbeats 6000000 in
-- [TABLET NODE: JumpL2VarianceEnergy]
theorem JumpL2VarianceEnergy (d N : ℕ) (hN : 2 ≤ N) (l u β : ℝ)
    (q : BoundedBackground d l u) (hβ : 0 ≤ β)
    (G : UnitAddTorus (Fin d) → ℝ) (hG : Measurable G)
    (hGi : Integrable G volume) (hGn : ∀ x, 0 ≤ G x) (hGe : ∀ x, G (-x) = G x) :
    let P := CanonicalLaw (N := N) G q.density β
    let Z := fun (X : Configuration d N) (i : Fin N)=>∫ z,Real.exp (-ConditionalPotential G β X i z)*q.density z
    let ν := fun (X : Configuration d N) (i : Fin N)=>NormalizedTilt volume (fun z=>q.density z*Real.exp (-ConditionalPotential G β X i z))
    ∀ f, MemLp f 2 P →
      (1/2:ℝ)*(∑ i : Fin N, ∫ X,(∫ z,Real.exp (-ConditionalPotential G β X i z)*(f (Replacement X i z)-f X)^2*q.density z) ∂P) =
      ∑ i : Fin N, ∫ X,Z X i*variance (fun z=>f (Replacement X i z)) (ν X i) ∂P := by
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

  have conditionalNormalizer_bounds (d N : ℕ) (hN : 2 ≤ N) (l u β : ℝ)
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

  have replacement_joint_measurable (d N : ℕ) (i : Fin N) :
      Measurable (fun p : Configuration d N × UnitAddTorus (Fin d) =>
        Replacement p.1 i p.2) := by
    apply measurable_pi_lambda
    intro k
    by_cases h : k = i
    · simpa only [Replacement,Function.update_apply,h,↓reduceIte,Function.comp_def] using
        (measurable_snd : Measurable (Prod.snd : Configuration d N × UnitAddTorus (Fin d) → _))
    · simpa only [Replacement,Function.update_apply,h,↓reduceIte,Function.comp_def] using
        ((measurable_pi_apply k).comp measurable_fst :
          Measurable (fun p : Configuration d N × UnitAddTorus (Fin d) => p.1 k))

  have conditionalPotential_joint_measurable (d N : ℕ) (G : UnitAddTorus (Fin d) → ℝ)
      (hG : Measurable G) (β : ℝ) (i : Fin N) :
      Measurable (fun p : Configuration d N × UnitAddTorus (Fin d) =>
        ConditionalPotential G β p.1 i p.2) := by
    dsimp [ConditionalPotential]
    apply Measurable.const_mul
    apply Finset.measurable_fun_sum
    intro j hj
    by_cases h : j = i
    · simp only [h,↓reduceIte]
      exact measurable_const
    · simp only [h,↓reduceIte]
      exact hG.comp (measurable_snd.sub ((measurable_pi_apply j).comp measurable_fst))

  have replacement_twice_same {d N : ℕ} (X : Configuration d N) (i : Fin N)
      (z v : UnitAddTorus (Fin d)) :
      Replacement (Replacement X i z) i v = Replacement X i v := by
    exact Function.update_idem (a := i) z v X

  have conditionalPotential_replacement_same {d N : ℕ}
      (G : UnitAddTorus (Fin d) → ℝ) (β : ℝ) (X : Configuration d N)
      (i : Fin N) (z v : UnitAddTorus (Fin d)) :
      ConditionalPotential G β (Replacement X i z) i v = ConditionalPotential G β X i v := by
    dsimp [ConditionalPotential]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : j = i <;> simp [h,Replacement]

  have conditionalMoment_replacement_same {d N : ℕ}
      (G q : UnitAddTorus (Fin d) → ℝ) (β : ℝ)
      (f : Configuration d N → ℝ) (X : Configuration d N)
      (i : Fin N) (z : UnitAddTorus (Fin d)) :
      (∫ v, Real.exp (-ConditionalPotential G β (Replacement X i z) i v) *
        f (Replacement (Replacement X i z) i v) * q v) =
      (∫ v, Real.exp (-ConditionalPotential G β X i v) * f (Replacement X i v) * q v) := by
    simp_rw [conditionalPotential_replacement_same,replacement_twice_same]

  have weighted_swap_iterated_integral {Ω B : Type} [MeasurableSpace Ω] [MeasurableSpace B]
      {μ : Measure Ω} {ν : Measure B} [SFinite μ] [SFinite ν]
      (w : Ω × B → ℝ) (hw : Measurable w) (hwn : ∀ᵐ p ∂μ.prod ν,0≤w p)
      (S : Ω × B → Ω × B)
      (hS : MeasurePreserving S ((μ.prod ν).withDensity (fun p=>ENNReal.ofReal (w p)))
        ((μ.prod ν).withDensity (fun p=>ENNReal.ofReal (w p))))
      (H : Ω × B → ℝ) (hH : Integrable H ((μ.prod ν).withDensity (fun p=>ENNReal.ofReal (w p)))) :
      Integrable (fun X=>∫ z,w (X,z)*H (X,z) ∂ν) μ ∧
      Integrable (fun X=>∫ z,w (X,z)*H (S (X,z)) ∂ν) μ ∧
      (∫ X,(∫ z,w (X,z)*H (X,z) ∂ν) ∂μ) =
        ∫ X,(∫ z,w (X,z)*H (S (X,z)) ∂ν) ∂μ := by
    let J := (μ.prod ν).withDensity (fun p=>ENNReal.ofReal (w p))
    have hSJ : MeasurePreserving S J J := hS
    have hHS : Integrable (H ∘ S) J := (hSJ.integrable_comp hH.aestronglyMeasurable).mpr hH
    have h1 := weighted_integrable_fubini w hw hwn H hH
    have h2 := weighted_integrable_fubini w hw hwn (H ∘ S) hHS
    have hm : AEStronglyMeasurable H (J.map S) := by rw [hSJ.map_eq];exact hH.aestronglyMeasurable
    have he : (∫ p,H (S p) ∂J) = ∫ p,H p ∂J := by
      have hh := integral_map hSJ.measurable.aemeasurable hm
      rw [hSJ.map_eq] at hh
      exact hh.symm
    refine ⟨h1.1.integral_prod_left,h2.1.integral_prod_left,?_⟩
    calc
      _ = ∫ p,H p ∂J := h1.2.1.symm
      _ = ∫ p,(H ∘ S) p ∂J := he.symm
      _ = _ := h2.2.1

  have actualConditional_mean_memLp (d N : ℕ) (hN : 2 ≤ N) (l u β : ℝ)
      (q : BoundedBackground d l u) (hβ : 0 ≤ β)
      (G : UnitAddTorus (Fin d) → ℝ) (hG : Measurable G)
      (hGi : Integrable G volume) (hGn : ∀ x, 0 ≤ G x) (hGe : ∀ x, G (-x) = G x)
      (f : Configuration d N → ℝ) (hf : MemLp f 2 (CanonicalLaw (N := N) G q.density β))
      (i : Fin N) :
      MemLp (fun X : Configuration d N =>
        (∫ z, f (Replacement X i z)*(Real.exp (-ConditionalPotential G β X i z)*q.density z))/
        (∫ z,Real.exp (-ConditionalPotential G β X i z)*q.density z)) 2
        (CanonicalLaw (N := N) G q.density β) := by
    let P := CanonicalLaw (N := N) G q.density β
    let Z := fun X : Configuration d N=>∫ z,Real.exp (-ConditionalPotential G β X i z)*q.density z
    let M := fun X : Configuration d N=>∫ z,f (Replacement X i z)*(q.density z*Real.exp (-ConditionalPotential G β X i z))
    let T := fun X : Configuration d N=>∫ z,(f (Replacement X i z))^2*(q.density z*Real.exp (-ConditionalPotential G β X i z))
    let a := Real.exp (-β*u*(∫ z,G z))
    have hMom := JumpConditionalL2Moments d N hN l u β q hβ G hG hGi hGn hGe f hf i
    have hn (X : Configuration d N) := conditionalNormalizer_bounds d N hN l u β q hβ G hG hGi hGn X i
    have hz (X : Configuration d N) : 0 < Z X := (Real.exp_pos _).trans_le (hn X).2.2.2.2.2.1
    have hZm : Measurable Z :=
      (((conditionalPotential_joint_measurable d N G hG β i).neg.exp).mul
        (q.measurable.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable
    have hZb : ∀ᵐ X ∂P,a≤Z X ∧ Z X≤1 := Filter.Eventually.of_forall fun X=>
      ⟨(hn X).2.2.2.2.2.1,(hn X).2.2.2.2.2.2.1⟩
    have hcs : ∀ᵐ X ∂P,(M X)^2≤Z X*T X := by
      filter_upwards [hMom.2.2] with X hx
      have hv := variance_nonneg (fun z=>f (Replacement X i z))
        (NormalizedTilt volume (fun z=>q.density z*Real.exp (-ConditionalPotential G β X i z)))
      have he : Z X*variance (fun z=>f (Replacement X i z))
        (NormalizedTilt volume (fun z=>q.density z*Real.exp (-ConditionalPotential G β X i z)))=T X-(M X)^2/Z X := hx.2
      have hratio : (M X)^2/Z X≤T X := by nlinarith [mul_nonneg (hz X).le hv]
      have hh := (div_le_iff₀ (hz X)).mp hratio
      simpa only [mul_comm] using hh
    have hm := ConditionalMeanL2Bound a (Real.exp_pos _) Z M T hZm.aestronglyMeasurable hMom.2.1 hMom.1 hZb hcs
    simpa only [M,Z,mul_comm,mul_assoc,mul_left_comm] using hm.1

  have unboundedConditional_integrals (d N : ℕ) (hN : 2 ≤ N) (l u β : ℝ)
      (q : BoundedBackground d l u) (hβ : 0 ≤ β)
      (G : UnitAddTorus (Fin d) → ℝ) (hG : Measurable G)
      (hGi : Integrable G volume) (hGn : ∀ x, 0 ≤ G x) (hGe : ∀ x, G (-x) = G x)
      (f : Configuration d N → ℝ) (hf : MemLp f 2 (CanonicalLaw (N := N) G q.density β))
      (i : Fin N)
      (hmean : MemLp (fun X : Configuration d N =>
        (∫ z, f (Replacement X i z)*(Real.exp (-ConditionalPotential G β X i z)*q.density z))/
        (∫ z,Real.exp (-ConditionalPotential G β X i z)*q.density z)) 2
        (CanonicalLaw (N := N) G q.density β)) :
      let P := CanonicalLaw (N := N) G q.density β
      let Z := fun X : Configuration d N=>∫ z,Real.exp (-ConditionalPotential G β X i z)*q.density z
      let M := fun X : Configuration d N=>∫ z,f (Replacement X i z)*(Real.exp (-ConditionalPotential G β X i z)*q.density z)
      let T := fun X : Configuration d N=>∫ z,(f (Replacement X i z))^2*(Real.exp (-ConditionalPotential G β X i z)*q.density z)
      let ν := fun X : Configuration d N=>NormalizedTilt volume (fun z=>q.density z*Real.exp (-ConditionalPotential G β X i z))
      Integrable (fun X=>Z X*variance (fun z=>f (Replacement X i z)) (ν X)) P ∧
      Integrable (fun X=>f X*M X) P ∧
      Integrable (fun X=>Z X*f X^2) P ∧
      (∫ X,Z X*f X^2 ∂P) = (∫ X,T X ∂P) ∧
      (∫ X,f X*M X ∂P) = (∫ X,(M X)^2/Z X ∂P) ∧
      (∫ X,Z X*f X^2-f X*M X ∂P) = (∫ X,Z X*variance (fun z=>f (Replacement X i z)) (ν X) ∂P) := by
    classical
    dsimp only
    let P := CanonicalLaw (N := N) G q.density β
    let r := fun (p : Configuration d N × UnitAddTorus (Fin d))=>Real.exp (-ConditionalPotential G β p.1 i p.2)*q.density p.2
    let R := fun p : Configuration d N × UnitAddTorus (Fin d)=>Replacement p.1 i p.2
    let S := fun p : Configuration d N × UnitAddTorus (Fin d)=>(R p,p.1 i)
    let J := (P.prod volume).withDensity (fun p=>ENNReal.ofReal (r p))
    let Z := fun X : Configuration d N=>∫ z,r (X,z)
    let M := fun X : Configuration d N=>∫ z,f (R (X,z))*r (X,z)
    let T := fun X : Configuration d N=>∫ z,(f (R (X,z)))^2*r (X,z)
    let ν := fun X : Configuration d N=>NormalizedTilt volume (fun z=>q.density z*Real.exp (-ConditionalPotential G β X i z))
    let m := fun X=>M X/Z X
    have hmLp : MemLp m 2 P := hmean
    have hjoint := ReplacementJointBalance d N hN l u β q hβ G hG hGi hGn hGe i
    have hS : MeasurePreserving S J J := hjoint.1
    have hR : Measurable R := replacement_joint_measurable d N i
    have hr : Measurable r := ((conditionalPotential_joint_measurable d N G hG β i).neg.exp).mul (q.measurable.comp measurable_snd)
    have hZ : Measurable Z := hr.stronglyMeasurable.integral_prod_right'.measurable
    have hP := (GibbsNormalizerBounds d N hN l u q G hG hGi 0 β (le_refl 0) hβ
      (Filter.Eventually.of_forall fun x=>by simpa using hGn x)).2.2.2
    haveI : IsProbabilityMeasure P := hP
    have hn (X : Configuration d N) := conditionalNormalizer_bounds d N hN l u β q hβ G hG hGi hGn X i
    have hz (X : Configuration d N) : 0 < Z X ∧ Z X ≤ 1 :=
      ⟨(Real.exp_pos _).trans_le (hn X).2.2.2.2.2.1,(hn X).2.2.2.2.2.2.1⟩
    have hZm (X : Configuration d N) : M X=Z X*m X := by dsimp only [m];field_simp [ne_of_gt (hz X).1]
    have hzrep (X : Configuration d N) (z : UnitAddTorus (Fin d)) : Z (Replacement X i z)=Z X := by
      simp only [Z,r,conditionalPotential_replacement_same]
    have hmrep (X : Configuration d N) (z : UnitAddTorus (Fin d)) : m (Replacement X i z)=m X := by
      simp only [m,M,Z,R,r,conditionalPotential_replacement_same,replacement_twice_same]
    have hzb : ∀ᵐ X ∂P,‖Z X‖ ≤ 1 := Filter.Eventually.of_forall fun X=>by
      simpa only [Real.norm_eq_abs,abs_of_pos (hz X).1] using (hz X).2
    have hiZf : Integrable (fun X=>Z X*f X^2) P :=
      hf.integrable_sq.bdd_mul hZ.aestronglyMeasurable hzb
    have hifM : Integrable (fun X=>f X*M X) P := by
      have hh := (hf.integrable_mul hmLp).bdd_mul hZ.aestronglyMeasurable hzb
      have he : (fun X=>f X*M X)=(fun X=>Z X*(f X*m X)) := by
        funext X
        rw [hZm]
        ring
      rw [he]
      exact hh
    have hiB : Integrable (fun X=>(M X)^2/Z X) P := by
      have hh := hmLp.integrable_sq.bdd_mul hZ.aestronglyMeasurable hzb
      have he : (fun X=>(M X)^2/Z X)=(fun X=>Z X*(m X)^2) := by
        funext X
        rw [hZm]
        field_simp [ne_of_gt (hz X).1]
        <;> ring
      rw [he]
      exact hh
    have hmu := JumpConditionalL2Moments d N hN l u β q hβ G hG hGi hGn hGe f hf i
    have hiT : Integrable T P := by simpa only [T,R,r,mul_comm,mul_assoc,mul_left_comm] using hmu.1
    have hvar : ∀ᵐ X ∂P,Z X*variance (fun z=>f (Replacement X i z)) (ν X)=T X-(M X)^2/Z X := by
      simpa only [Z,T,M,R,r,ν,mul_comm,mul_assoc,mul_left_comm] using hmu.2.2.mono (fun X hX=>hX.2)
    have hvarEq : (fun X=>Z X*variance (fun z=>f (Replacement X i z)) (ν X)) =ᵐ[P]
        (fun X=>T X-(M X)^2/Z X) := hvar
    have hivar : Integrable (fun X=>Z X*variance (fun z=>f (Replacement X i z)) (ν X)) P :=
      (hiT.sub hiB).congr hvarEq.symm
    have hrn : ∀ᵐ p ∂P.prod (volume : Measure (UnitAddTorus (Fin d))),0≤r p := by
      have hq := (measurePreserving_snd (μ:=P) (ν:=(volume : Measure (UnitAddTorus (Fin d))))).quasiMeasurePreserving.ae q.bounds
      filter_upwards [hq] with p hp
      exact mul_nonneg (Real.exp_pos _).le (q.lower_pos.le.trans hp.1)
    have hf0 := (dominated_marginal_pullback Prod.fst measurable_fst.aemeasurable hjoint.2.1 f hf).1
    have hm0 := (dominated_marginal_pullback Prod.fst measurable_fst.aemeasurable hjoint.2.1 m hmLp).1
    have hTidentity : (∫ X,Z X*f X^2 ∂P)=(∫ X,T X ∂P) := by
      have he := (weighted_swap_iterated_integral r hr hrn S hS
        (fun p=>(f p.1)^2) hf0.integrable_sq).2.2
      have hl (X : Configuration d N) : (∫ z,r (X,z)*(f X)^2)=Z X*(f X)^2 := integral_mul_const _ _
      have hrr (X : Configuration d N) : (∫ z,r (X,z)*(f (R (X,z)))^2)=T X := by simp only [T,mul_comm]
      change (∫ X,(∫ z,r (X,z)*(f X)^2) ∂P)=(∫ X,(∫ z,r (X,z)*(f (R (X,z)))^2) ∂P) at he
      simp_rw [hl,hrr] at he
      exact he
    have hMidentity : (∫ X,f X*M X ∂P)=(∫ X,(M X)^2/Z X ∂P) := by
      have he := (weighted_swap_iterated_integral r hr hrn S hS
        (fun p=>f p.1*m p.1) (hf0.integrable_mul hm0)).2.2
      have hl (X : Configuration d N) : (∫ z,r (X,z)*(f X*m X))=f X*M X := by
        rw [integral_mul_const]
        change Z X*(f X*m X)=f X*M X
        rw [hZm]
        ring
      have hrr (X : Configuration d N) : (∫ z,r (X,z)*(f (R (X,z))*m (R (X,z))))=(M X)^2/Z X := by
        have hi (z : UnitAddTorus (Fin d)) : m (R (X,z))=m X := hmrep X z
        simp_rw [hi]
        have hh : (fun z=>r (X,z)*(f (R (X,z))*m X))=(fun z=>(f (R (X,z))*r (X,z))*m X) := by funext z;ring
        rw [hh,integral_mul_const]
        change M X*m X=(M X)^2/Z X
        dsimp only [m]
        ring
      change (∫ X,(∫ z,r (X,z)*(f X*m X)) ∂P)=(∫ X,(∫ z,r (X,z)*(f (R (X,z))*m (R (X,z)))) ∂P) at he
      simp_rw [hl,hrr] at he
      exact he
    refine ⟨hivar,?_,hiZf,hTidentity,hMidentity,?_⟩
    · exact hifM
    · rw [integral_sub hiZf hifM,hTidentity,hMidentity]
      calc
        _ = ∫ X,T X-(M X)^2/Z X ∂P := (integral_sub hiT hiB).symm
        _ = _ := integral_congr_ae hvarEq.symm

  have weighted_square_sub_integral {Ω : Type} [MeasurableSpace Ω]
      (μ : Measure Ω) (w φ : Ω → ℝ) (c : ℝ)
      (hw : Integrable w μ)
      (h1 : Integrable (fun z => φ z * w z) μ)
      (h2 : Integrable (fun z => (φ z)^2 * w z) μ) :
      (∫ z, (φ z-c)^2*w z ∂μ) =
        (∫ z,(φ z)^2*w z ∂μ) -
          2*c*(∫ z,φ z*w z ∂μ)+c^2*(∫ z,w z ∂μ) := by
    have hpoint : (fun z => (φ z-c)^2*w z) =
        (fun z => (φ z)^2*w z - (2*c)*(φ z*w z)+c^2*w z) := by
      funext z
      ring
    rw [hpoint]
    have hs := integral_sub h2 (h1.const_mul (2*c))
    change (∫ z,(φ z)^2*w z-(2*c)*(φ z*w z) ∂μ) =
      (∫ z,(φ z)^2*w z ∂μ)-(∫ z,(2*c)*(φ z*w z) ∂μ) at hs
    have ha := integral_add (h2.sub (h1.const_mul (2*c))) (hw.const_mul (c^2))
    change (∫ z,(φ z)^2*w z-(2*c)*(φ z*w z)+c^2*w z ∂μ) =
      (∫ z,(φ z)^2*w z-(2*c)*(φ z*w z) ∂μ)+(∫ z,c^2*w z ∂μ) at ha
    rw [ha, hs, integral_const_mul, integral_const_mul]
  intro P Z ν f hf
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  let r := fun (p : Configuration d N × UnitAddTorus (Fin d))=>Real.exp (-ConditionalPotential G β p.1 i p.2)*q.density p.2
  let R := fun p : Configuration d N × UnitAddTorus (Fin d)=>Replacement p.1 i p.2
  let J := (P.prod volume).withDensity (fun p=>ENNReal.ofReal (r p))
  let M := fun X : Configuration d N=>∫ z,f (Replacement X i z)*r (X,z)
  let T := fun X : Configuration d N=>∫ z,(f (Replacement X i z))^2*r (X,z)
  have hP := (GibbsNormalizerBounds d N hN l u q G hG hGi 0 β (le_refl 0) hβ
    (Filter.Eventually.of_forall fun x=>by simpa using hGn x)).2.2.2
  haveI : IsProbabilityMeasure P := hP
  have hj := ReplacementJointBalance d N hN l u β q hβ G hG hGi hGn hGe i
  have hR : Measurable R := replacement_joint_measurable d N i
  have hr : Measurable r := ((conditionalPotential_joint_measurable d N G hG β i).neg.exp).mul (q.measurable.comp measurable_snd)
  have hrn : ∀ᵐ p ∂P.prod (volume : Measure (UnitAddTorus (Fin d))),0≤r p := by
    have hq := (measurePreserving_snd (μ:=P) (ν:=(volume : Measure (UnitAddTorus (Fin d))))).quasiMeasurePreserving.ae q.bounds
    filter_upwards [hq] with p hp
    exact mul_nonneg (Real.exp_pos _).le (q.lower_pos.le.trans hp.1)
  haveI : IsFiniteMeasure (J.map Prod.fst) := isFiniteMeasure_of_le P hj.2.1
  haveI : IsFiniteMeasure J := Measure.isFiniteMeasure_of_map measurable_fst.aemeasurable
  have hfR : MemLp (fun p=>f (R p)) 2 J :=
    (dominated_marginal_pullback R hR.aemeasurable hj.2.2 f hf).1
  have hf1 := weighted_integrable_fubini r hr hrn (fun p=>f (R p))
    (hfR.integrable (by norm_num : (1:ENNReal)≤2))
  have hf2 := weighted_integrable_fubini r hr hrn (fun p=>(f (R p))^2) hfR.integrable_sq
  have hD : ∀ᵐ X ∂P,(∫ z,r (X,z)*(f (Replacement X i z)-f X)^2)=
      T X-2*(f X*M X)+Z X i*f X^2 := by
    filter_upwards [hf1.2.2,hf2.2.2] with X h1 h2
    have hn := conditionalNormalizer_bounds d N hN l u β q hβ G hG hGi hGn X i
    have h1' : Integrable (fun z=>f (Replacement X i z)*r (X,z)) volume := by simpa only [R,mul_comm] using h1
    have h2' : Integrable (fun z=>(f (Replacement X i z))^2*r (X,z)) volume := by simpa only [R,mul_comm] using h2
    have hh := weighted_square_sub_integral volume (fun z=>r (X,z))
      (fun z=>f (Replacement X i z)) (f X) hn.2.2.2.2.1 h1' h2'
    have hl : (∫ z,r (X,z)*(f (Replacement X i z)-f X)^2)=
        ∫ z,(f (Replacement X i z)-f X)^2*r (X,z) := by simp only [mul_comm]
    rw [hl,hh]
    change T X-2*f X*M X+f X^2*Z X i=T X-2*(f X*M X)+Z X i*f X^2
    ring
  have hv := unboundedConditional_integrals d N hN l u β q hβ G hG hGi hGn hGe f hf i
    (actualConditional_mean_memLp d N hN l u β q hβ G hG hGi hGn hGe f hf i)
  have hMom := JumpConditionalL2Moments d N hN l u β q hβ G hG hGi hGn hGe f hf i
  have hTi : Integrable T P := by simpa only [T,r,mul_comm,mul_assoc,mul_left_comm] using hMom.1
  have hMi : Integrable (fun X=>f X*M X) P := hv.2.1
  have hZi : Integrable (fun X=>Z X i*f X^2) P := hv.2.2.1
  have hTidentity : (∫ X,Z X i*f X^2 ∂P)=(∫ X,T X ∂P) := hv.2.2.2.1
  have hvaridentity : (∫ X,Z X i*f X^2-f X*M X ∂P)=
      ∫ X,Z X i*variance (fun z=>f (Replacement X i z)) (ν X i) ∂P := hv.2.2.2.2.2
  have houter : (∫ X,(∫ z,Real.exp (-ConditionalPotential G β X i z)*(f (Replacement X i z)-f X)^2*q.density z) ∂P)=
      ∫ X,T X-2*(f X*M X)+Z X i*f X^2 ∂P := by
    apply integral_congr_ae
    filter_upwards [hD] with X hx
    have hh : (∫ z,Real.exp (-ConditionalPotential G β X i z)*(f (Replacement X i z)-f X)^2*q.density z)=
        ∫ z,r (X,z)*(f (Replacement X i z)-f X)^2 := by simp only [r,mul_comm,mul_assoc,mul_left_comm]
    rw [hh]
    exact hx
  rw [houter]
  rw [←hvaridentity]
  have ha := integral_add (hTi.sub (hMi.const_mul 2)) hZi
  change (∫ X,T X-2*(f X*M X)+Z X i*f X^2 ∂P)=
    (∫ X,T X-2*(f X*M X) ∂P)+(∫ X,Z X i*f X^2 ∂P) at ha
  have hs := integral_sub hTi (hMi.const_mul 2)
  change (∫ X,T X-2*(f X*M X) ∂P)=(∫ X,T X ∂P)-(∫ X,2*(f X*M X) ∂P) at hs
  rw [ha,hs,integral_const_mul,integral_sub hZi hMi,←hTidentity]
  ring
