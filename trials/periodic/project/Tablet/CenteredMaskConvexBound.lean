import Tablet.Preamble
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.Pi
open MeasureTheory
universe u
-- [TABLET NODE: CenteredMaskConvexBound]
theorem CenteredMaskConvexBound {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ) (f : Fin N → Ω → ℝ)
    (hf : ∀ i, Measurable (f i)) (A : ℝ) (hA : 0 ≤ A)
    (hb : ∀ i x, |f i x| ≤ A) (hm : ∀ i, (∫ x,f i x ∂μ)=0)
    (σ : Fin N → Bool) (Φ : ℝ → ℝ) (hΦ : ConvexOn ℝ Set.univ Φ) (hΦc : Continuous Φ) :
    (∫ X : Fin N → Ω,Φ (∑ i,if σ i=true then f i (X i) else 0)
      ∂Measure.pi (fun _ : Fin N => μ)) ≤
    (∫ X : Fin N → Ω,Φ (∑ i,f i (X i)) ∂Measure.pi (fun _ : Fin N => μ)) := by
-- BODY
  classical
  let ν := Measure.pi (fun _ : Fin N => μ)
  let I := {i : Fin N // σ i=true}
  let J := {i : Fin N // σ i≠true}
  let ηI := Measure.pi (fun _ : I => μ)
  let ηJ := Measure.pi (fun _ : J => μ)
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin N => Ω) (fun i => σ i=true)
  have he : MeasurePreserving e ν (ηI.prod ηJ) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ : Fin N => μ) (fun i => σ i=true)
  let a : (I → Ω) → ℝ := fun X => ∑ i,if hi : σ i=true then f i (X ⟨i,hi⟩) else 0
  let b : (J → Ω) → ℝ := fun Y => ∑ i,if hi : σ i≠true then f i (Y ⟨i,hi⟩) else 0
  let B := (N : ℝ)*A
  have hB : 0 ≤ B := mul_nonneg (Nat.cast_nonneg N) hA
  have sum_bound (g : Fin N → ℝ) (h : ∀ i,|g i|≤A) : |∑ i,g i|≤B := by
    calc
      _ ≤ ∑ i,|g i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin N,A := Finset.sum_le_sum (fun i _ => h i)
      _ = _ := by simp [B]
  have ham : Measurable a := by
    apply Finset.measurable_fun_sum
    intro i hi
    by_cases h : σ i=true
    · simp only [dif_pos h]
      exact (hf i).comp (measurable_pi_apply (⟨i,h⟩ : I))
    · simp only [dif_neg h];exact measurable_const
  have hbm : Measurable b := by
    apply Finset.measurable_fun_sum
    intro i hi
    by_cases h : σ i≠true
    · simp only [dif_pos h]
      exact (hf i).comp (measurable_pi_apply (⟨i,h⟩ : J))
    · simp only [dif_neg h];exact measurable_const
  have hab (X : I → Ω) : |a X|≤B := by
    apply sum_bound
    intro i
    split_ifs
    · exact hb i _
    · simpa using hA
  have hbb (Y : J → Ω) : |b Y|≤B := by
    apply sum_bound
    intro i
    split_ifs
    · exact hb i _
    · simpa using hA
  have hbi : Integrable b ηJ := Integrable.of_bound hbm.aestronglyMeasurable B
    (Filter.Eventually.of_forall (fun Y => by simpa only [Real.norm_eq_abs] using hbb Y))
  have hbmean : (∫ Y,b Y ∂ηJ)=0 := by
    dsimp [b]
    rw [integral_finset_sum _ (fun i _ => ?_)]
    · apply Finset.sum_eq_zero
      intro i hi
      by_cases h : σ i≠true
      · simp only [dif_pos h]
        rw [integral_comp_eval (μ := fun _ : J => μ) (i := (⟨i,h⟩ : J)) ((hf i).aestronglyMeasurable)]
        exact hm i
      · simp [h]
    · by_cases h : σ i≠true
      · simp only [dif_pos h]
        exact integrable_comp_eval (Integrable.of_bound (hf i).aestronglyMeasurable A
          (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb i x)))
      · simp only [dif_neg h];exact integrable_const 0
  obtain ⟨D,hD⟩ := (isCompact_Icc : IsCompact (Set.Icc (-2*B) (2*B))).exists_bound_of_continuousOn hΦc.continuousOn
  have phi_integrable {Λ : Type u} [MeasurableSpace Λ] (ξ : Measure Λ) [IsProbabilityMeasure ξ]
      (g : Λ → ℝ) (hgm : Measurable g) (hgb : ∀ x,|g x|≤2*B) :
      Integrable (fun x => Φ (g x)) ξ := by
    apply Integrable.of_bound (hΦc.measurable.comp hgm).aestronglyMeasurable D
    exact Filter.Eventually.of_forall fun x => hD _ (by simpa only [Set.mem_Icc,neg_mul] using abs_le.mp (hgb x))
  have hphiA : Integrable (fun X => Φ (a X)) ηI :=
    phi_integrable ηI a ham (fun X => (hab X).trans (by linarith))
  have hphiAP : Integrable (fun p : (I → Ω) × (J → Ω) => Φ (a p.1)) (ηI.prod ηJ) :=
    phi_integrable _ _ (ham.comp measurable_fst) (fun p => (hab p.1).trans (by linarith))
  have habm : Measurable (fun p : (I → Ω) × (J → Ω) => a p.1+b p.2) :=
    (ham.comp measurable_fst).add (hbm.comp measurable_snd)
  have hphiP : Integrable (fun p : (I → Ω) × (J → Ω) => Φ (a p.1+b p.2)) (ηI.prod ηJ) :=
    phi_integrable _ _ habm (fun p => (abs_add_le _ _).trans (by linarith [hab p.1,hbb p.2]))
  have hjensen (X : I → Ω) : Φ (a X) ≤ ∫ Y,Φ (a X+b Y) ∂ηJ := by
    have hsum : Integrable (fun Y => a X+b Y) ηJ := (integrable_const _).add hbi
    have hphi : Integrable (fun Y => Φ (a X+b Y)) ηJ :=
      phi_integrable _ _ (measurable_const.add hbm)
        (fun Y => (abs_add_le _ _).trans (by linarith [hab X,hbb Y]))
    have h := hΦ.map_integral_le hΦc.continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hsum hphi
    rw [integral_add (integrable_const _) hbi,hbmean] at h
    simpa using h
  have heA (X : Fin N → Ω) : a (e X).1 = ∑ i,if σ i=true then f i (X i) else 0 := by
    dsimp [a]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : σ i=true <;>simp [h,e,MeasurableEquiv.piEquivPiSubtypeProd]
  have hefull (X : Fin N → Ω) : a (e X).1+b (e X).2 = ∑ i,f i (X i) := by
    dsimp [a,b]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : σ i=true <;>simp [h,e,MeasurableEquiv.piEquivPiSubtypeProd]
  calc
    _ = ∫ X,Φ (a (e X).1) ∂ν := integral_congr_ae (Filter.Eventually.of_forall fun X => congrArg Φ (heA X).symm)
    _ = ∫ p : (I → Ω) × (J → Ω),Φ (a p.1) ∂ηI.prod ηJ := he.integral_comp' (fun p : (I → Ω) × (J → Ω) => Φ (a p.1))
    _ = ∫ X,Φ (a X) ∂ηI := by rw [integral_prod _ hphiAP];simp
    _ ≤ ∫ X,∫ Y,Φ (a X+b Y) ∂ηJ ∂ηI :=
      integral_mono_ae hphiA hphiP.integral_prod_left (Filter.Eventually.of_forall hjensen)
    _ = ∫ p : (I → Ω) × (J → Ω),Φ (a p.1+b p.2) ∂ηI.prod ηJ := (integral_prod _ hphiP).symm
    _ = ∫ X,Φ (a (e X).1+b (e X).2) ∂ν := (he.integral_comp' (fun p : (I → Ω) × (J → Ω) => Φ (a p.1+b p.2))).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun X => congrArg Φ (hefull X))
