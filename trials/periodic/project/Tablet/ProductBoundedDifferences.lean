module

public import Tablet.Preamble
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section
open MeasureTheory ProbabilityTheory
-- [TABLET NODE: ProductBoundedDifferences]
theorem ProductBoundedDifferences {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ)
    (F : (Fin N → Ω) → ℝ) (hF : Measurable F)
    (B c : ℝ) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hb : ∀ X, |F X| ≤ B)
    (hd : ∀ i X Y, (∀ j, j ≠ i → X j=Y j) → |F X-F Y| ≤ c) :
    ∀ t : ℝ,
      (∫ X : Fin N → Ω,Real.exp (t*(F X-∫ Y,F Y ∂Measure.pi (fun _ : Fin N => μ)))
        ∂Measure.pi (fun _ : Fin N => μ)) ≤ Real.exp ((N : ℝ)*c^2*t^2/2) := by
-- BODY
  classical
  induction N with
  | zero =>
    intro t
    have he (X Y : Fin 0 → Ω) : X=Y := Subsingleton.elim _ _
    have hm (X : Fin 0 → Ω) : (∫ Y,F Y ∂Measure.pi (fun _ : Fin 0 => μ))=F X :=
      integral_eq_const (Filter.Eventually.of_forall fun Y => congrArg F (he Y X))
    have hh : (fun X => Real.exp (t*(F X-∫ Y,F Y ∂Measure.pi (fun _ : Fin 0 => μ)))) = fun _ => (1 : ℝ) := by
      funext X
      rw [hm X]
      simp
    rw [hh]
    simp
  | succ n ih =>
    let ν := Measure.pi (fun _ : Fin n => μ)
    let η := Measure.pi (fun _ : Fin (n+1) => μ)
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Ω) 0
    have he : MeasurePreserving e η (μ.prod ν) := measurePreserving_piFinSuccAbove (fun _ => μ) 0
    have hei : MeasurePreserving e.symm (μ.prod ν) η := he.symm
    have hes (x : Ω) (Z : Fin n → Ω) : e.symm (x,Z)=Fin.cons x Z := by
      simp [e,MeasurableEquiv.piFinSuccAbove,Fin.insertNthEquiv,Fin.insertNth_zero']
    let f : Ω × (Fin n → Ω) → ℝ := fun p => F (e.symm p)
    have hfm : Measurable f := hF.comp e.symm.measurable
    have hfb (p : Ω × (Fin n → Ω)) : |f p|≤B := hb _
    have hfi : Integrable f (μ.prod ν) := Integrable.of_bound hfm.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hfb p)
    have hfxi (Z : Fin n → Ω) : Integrable (fun x => f (x,Z)) μ :=
      Integrable.of_bound (hfm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable B
        (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hfb (x,Z))
    let G : (Fin n → Ω) → ℝ := fun Z => ∫ x,f (x,Z) ∂μ
    have hGm : Measurable G := hfm.stronglyMeasurable.integral_prod_left'.measurable
    have hGb (Z : Fin n → Ω) : |G Z|≤B := by
      simpa [Real.norm_eq_abs,G] using
        norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => f (x,Z)) (C := B) (Filter.Eventually.of_forall fun x => by
          simpa only [Real.norm_eq_abs] using hfb (x,Z))
    have hGi : Integrable G ν := Integrable.of_bound hGm.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun Z => by simpa only [Real.norm_eq_abs] using hGb Z)
    have hGd : ∀ i Z W, (∀ j, j≠i → Z j=W j) → |G Z-G W|≤c := by
      intro i Z W hZW
      rw [←integral_sub (hfxi Z) (hfxi W)]
      have hd' (x : Ω) : |f (x,Z)-f (x,W)|≤c := by
        apply hd i.succ
        intro j hj
        obtain rfl | ⟨k,rfl⟩ := Fin.eq_zero_or_eq_succ j
        · simp [f,hes]
        · simpa [f,hes] using hZW k (by intro h;apply hj;simpa [h])
      simpa [Real.norm_eq_abs,G] using
        norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => f (x,Z)-f (x,W)) (C := c) (Filter.Eventually.of_forall fun x => by
          simpa only [Real.norm_eq_abs] using hd' x)
    have hmean : (∫ X,F X ∂η) = ∫ Z,G Z ∂ν := by
      calc
        _ = ∫ p,f p ∂μ.prod ν := (hei.integral_comp' F).symm
        _ = _ := integral_prod_symm _ hfi
    intro t
    have hcenter (Z : Fin n → Ω) (x : Ω) : |f (x,Z)-G Z|≤c := by
      have hh : f (x,Z)-G Z = ∫ y,f (x,Z)-f (y,Z) ∂μ := by
        rw [integral_sub (integrable_const _) (hfxi Z)]
        simp [G]
      rw [hh]
      have hh' (y : Ω) : |f (x,Z)-f (y,Z)|≤c := by
        apply hd 0
        intro j hj
        obtain rfl | ⟨k,rfl⟩ := Fin.eq_zero_or_eq_succ j
        · exact False.elim (hj rfl)
        · simp [f,hes]
      simpa [Real.norm_eq_abs,G] using
        norm_integral_le_of_norm_le_const (μ := μ) (f := fun y => f (x,Z)-f (y,Z)) (C := c) (Filter.Eventually.of_forall fun y => by
          simpa only [Real.norm_eq_abs] using hh' y)
    have hcentermean (Z : Fin n → Ω) : (∫ x,f (x,Z)-G Z ∂μ)=0 := by
      rw [integral_sub (hfxi Z) (integrable_const _)];simp [G]
    have hcond (Z : Fin n → Ω) : (∫ x,Real.exp (t*(f (x,Z)-G Z)) ∂μ) ≤ Real.exp (c^2*t^2/2) := by
      have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
        ((hfm.comp (measurable_id.prodMk measurable_const)).sub_const (G Z)).aemeasurable
        (Filter.Eventually.of_forall fun x => abs_le.mp (hcenter Z x)) (hcentermean Z)
      have hm := h.mgf_le t
      simpa only [mgf,coe_nnnorm,Real.norm_eq_abs,NNReal.coe_pow,NNReal.coe_div,NNReal.coe_ofNat,sub_neg_eq_add,abs_of_nonneg (by linarith : 0≤c+c),Function.comp_apply,id_eq,
        add_self_div_two] using hm
    have hexi : Integrable (fun p : Ω × (Fin n → Ω) =>
        Real.exp (t*(f p-∫ Z,G Z ∂ν))) (μ.prod ν) := by
      apply Integrable.of_bound ((hfm.sub_const _).const_mul t).exp.aestronglyMeasurable
        (Real.exp (|t| * (2*B)))
      exact Filter.Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        have hmeanb : |∫ Z,G Z ∂ν|≤B := by
          simpa [Real.norm_eq_abs,G] using
            norm_integral_le_of_norm_le_const (μ := ν) (f := G) (C := B) (Filter.Eventually.of_forall fun Z => by
              simpa only [Real.norm_eq_abs] using hGb Z)
        calc
          _ ≤ |t*(f p-∫ Z,G Z ∂ν)| := le_abs_self _
          _ = |t| * |f p-∫ Z,G Z ∂ν| := abs_mul _ _
          _ ≤ _ := mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (by linarith [hfb p])) (abs_nonneg _)
    have hexGi : Integrable (fun Z => Real.exp (t*(G Z-∫ W,G W ∂ν))) ν := by
      apply Integrable.of_bound ((hGm.sub_const _).const_mul t).exp.aestronglyMeasurable
        (Real.exp (|t| * (B+|∫ W,G W ∂ν|)))
      exact Filter.Eventually.of_forall fun Z => by
        rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        exact (le_abs_self _).trans (by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add_left (hGb Z) _)) (abs_nonneg _))
    calc
      _ = ∫ p : Ω × (Fin n → Ω),Real.exp (t*(f p-∫ Z,G Z ∂ν)) ∂μ.prod ν := by
        rw [hmean]
        exact (hei.integral_comp' (fun X => Real.exp (t*(F X-∫ Z,G Z ∂ν)))).symm
      _ = ∫ Z,∫ x,Real.exp (t*(f (x,Z)-∫ W,G W ∂ν)) ∂μ ∂ν := integral_prod_symm _ hexi
      _ ≤ ∫ Z,Real.exp (c^2*t^2/2)*Real.exp (t*(G Z-∫ W,G W ∂ν)) ∂ν := by
        apply integral_mono_ae hexi.integral_prod_right (hexGi.const_mul _)
        exact Filter.Eventually.of_forall fun Z => by
          have hh (x : Ω) : Real.exp (t*(f (x,Z)-∫ W,G W ∂ν)) =
              Real.exp (t*(f (x,Z)-G Z))*Real.exp (t*(G Z-∫ W,G W ∂ν)) := by
            rw [←Real.exp_add];congr 1;ring
          simp_rw [hh]
          rw [integral_mul_const]
          exact mul_le_mul_of_nonneg_right (hcond Z) (Real.exp_nonneg _)
      _ = Real.exp (c^2*t^2/2)*(∫ Z,Real.exp (t*(G Z-∫ W,G W ∂ν)) ∂ν) := integral_const_mul _ _
      _ ≤ Real.exp (c^2*t^2/2)*Real.exp ((n : ℝ)*c^2*t^2/2) :=
        mul_le_mul_of_nonneg_left (ih G hGm hGb hGd t) (Real.exp_nonneg _)
      _ = _ := by rw [←Real.exp_add];congr 1;push_cast;ring
