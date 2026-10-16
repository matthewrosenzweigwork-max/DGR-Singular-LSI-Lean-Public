import Tablet.BernoulliSplitJensen
import Tablet.CanonicalKernelMaskBound
import Mathlib.MeasureTheory.Constructions.Pi
open MeasureTheory
-- [TABLET NODE: CanonicalConvexDecoupling]
theorem CanonicalConvexDecoupling {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ) (q : Ω → Ω → ℝ)
    (hq : Measurable (fun p : Ω × Ω => q p.1 p.2))
    (A : ℝ) (hA : 0 ≤ A) (hb : ∀ x y, |q x y| ≤ A)
    (hrow : ∀ y, (∫ x, q x y ∂μ) = 0)
    (hcol : ∀ x, (∫ y, q x y ∂μ) = 0) (t : ℝ)
    (Φ : ℝ → ℝ) (hΦ : ConvexOn ℝ Set.univ Φ) (hΦc : Continuous Φ) :
    (∫ X : Fin N → Ω,Φ (t*∑ i,∑ j,if i=j then 0 else q (X i) (X j))
      ∂Measure.pi (fun _ : Fin N => μ)) ≤
    (∫ p : (Fin N → Ω) × (Fin N → Ω),
      Φ (4*t*∑ i,∑ j,if i=j then 0 else q (p.1 i) (p.2 j))
      ∂(Measure.pi (fun _ : Fin N => μ)).prod (Measure.pi (fun _ : Fin N => μ))) := by
-- BODY
  classical
  let ν := Measure.pi (fun _ : Fin N => μ)
  let a (i j : Fin N) (x y : Ω) := if i=j then (0:ℝ) else q x y
  have ham (i j : Fin N) : Measurable (fun p : Ω × Ω => a i j p.1 p.2) := by
    by_cases h : i=j <;>simp only [a,h,ite_true,ite_false]
    · exact measurable_const
    · exact hq
  have hab (i j : Fin N) (x y : Ω) : |a i j x y| ≤ A := by
    dsimp [a]
    split_ifs
    · simpa using hA
    · exact hb x y
  have harow (i j : Fin N) (y : Ω) : (∫ x,a i j x y ∂μ)=0 := by
    by_cases h : i=j <;>simp [a,h,hrow]
  have hacol (i j : Fin N) (x : Ω) : (∫ y,a i j x y ∂μ)=0 := by
    by_cases h : i=j <;>simp [a,h,hcol]
  let U (m : Fin N → Fin N → Prop) (X : Fin N → Ω) :=
    ∑ i,∑ j,if m i j then a i j (X i) (X j) else 0
  let all : Fin N → Fin N → Prop := fun _ _ => True
  let split (σ : Fin N → Bool) : Fin N → Fin N → Prop :=
    fun i j => σ i=true ∧ σ j=false
  have hUm (m : Fin N → Fin N → Prop) : Measurable (U m) := by
    apply Finset.measurable_fun_sum
    intro i hi
    apply Finset.measurable_fun_sum
    intro j hj
    by_cases h : m i j
    · simp only [h,ite_true]
      have hp : Measurable (fun X : Fin N → Ω => (X i,X j)) :=
        (measurable_pi_apply i).prodMk (measurable_pi_apply j)
      have hh := (ham i j).comp hp
      exact hh
    · simp only [h,ite_false];exact measurable_const
  have hUb (m : Fin N → Fin N → Prop) (X : Fin N → Ω) : |U m X| ≤ (N : ℝ)^2*A := by
    have hterm (i j : Fin N) : |if m i j then a i j (X i) (X j) else 0| ≤ A := by
      split_ifs
      · exact hab i j _ _
      · simpa using hA
    have hrow (i : Fin N) : |∑ j,if m i j then a i j (X i) (X j) else 0| ≤ (N : ℝ)*A := by
      calc
        _ ≤ ∑ j,|if m i j then a i j (X i) (X j) else 0| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _ : Fin N,A := Finset.sum_le_sum (fun j _ => hterm i j)
        _ = _ := by simp
    calc
      _ ≤ ∑ i,|∑ j,if m i j then a i j (X i) (X j) else 0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin N,(N : ℝ)*A := Finset.sum_le_sum (fun i _ => hrow i)
      _ = _ := by simp;ring
  have hUI (m : Fin N → Fin N → Prop) (θ : ℝ) :
      Integrable (fun X => Φ (θ*U m X)) ν := by
    let C := |θ| * ((N : ℝ)^2*A)
    obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Set.Icc (-C) C)).exists_bound_of_continuousOn hΦc.continuousOn
    apply Integrable.of_bound (hΦc.measurable.comp ((hUm m).const_mul θ)).aestronglyMeasurable B
    exact Filter.Eventually.of_forall fun X => hB _ (by
      change -C ≤ θ*U m X ∧ θ*U m X ≤ C
      apply abs_le.mp
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hUb m X) (abs_nonneg θ))
  let D := ∫ p : (Fin N → Ω) × (Fin N → Ω),
    Φ (4*t*∑ i,∑ j,a i j (p.1 i) (p.2 j)) ∂ν.prod ν
  have hsplit (σ : Fin N → Bool) : (∫ X,Φ (4*t*U (split σ) X) ∂ν) ≤ D := by
    let I := {i : Fin N // σ i=true}
    let J := {j : Fin N // σ j≠true}
    let ηI := Measure.pi (fun _ : I => μ)
    let ηJ := Measure.pi (fun _ : J => μ)
    let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin N => Ω) (fun i => σ i=true)
    have he : MeasurePreserving e ν (ηI.prod ηJ) :=
      measurePreserving_piEquivPiSubtypeProd (fun _ : Fin N => μ) (fun i => σ i=true)
    let L : (Fin N → Ω) → I → Ω := fun X i => X i
    let R : (Fin N → Ω) → J → Ω := fun X j => X j
    have hL : MeasurePreserving L ν ηI := measurePreserving_fst.comp he
    have hR : MeasurePreserving R ν ηJ := measurePreserving_snd.comp he
    have hLR : MeasurePreserving (Prod.map L R) (ν.prod ν) (ηI.prod ηJ) := hL.prod hR
    let F : (I → Ω) × (J → Ω) → ℝ := fun p => Φ (4*t*∑ i,∑ j,
      if hi : σ i=true then if hj : σ j≠true then a i j (p.1 ⟨i,hi⟩) (p.2 ⟨j,hj⟩) else 0 else 0)
    have hF : Measurable F := by
      apply hΦc.measurable.comp
      apply Measurable.const_mul
      apply Finset.measurable_fun_sum
      intro i hi
      apply Finset.measurable_fun_sum
      intro j hj
      by_cases hσi : σ i=true
      · simp only [hσi,dif_pos]
        by_cases hσj : σ j≠true
        · simp only [hσj,dif_pos]
          have hp : Measurable (fun p : (I → Ω) × (J → Ω) => (p.1 ⟨i,hσi⟩,p.2 ⟨j,hσj⟩)) :=
            ((measurable_pi_apply (⟨i,hσi⟩ : I)).comp measurable_fst).prodMk
              ((measurable_pi_apply (⟨j,hσj⟩ : J)).comp measurable_snd)
          have hh := (ham i j).comp hp
          exact hh
        · simp only [hσj,dif_neg];exact measurable_const
      · simp only [hσi,dif_neg];exact measurable_const
    have hterm (X Y : Fin N → Ω) (i j : Fin N) :
        (if hi : σ i=true then if hj : σ j≠true then a i j (L X ⟨i,hi⟩) (R Y ⟨j,hj⟩) else 0 else 0) =
          (if σ i=true ∧ σ j=false then a i j (X i) (Y j) else 0) := by
      by_cases hi : σ i=true
      · by_cases hj : σ j=true
        · simp [hi,hj]
        · have hjf := Bool.eq_false_of_not_eq_true hj
          simp [hi,hj,hjf,L,R]
      · simp [hi]
    have hFX (X : Fin N → Ω) : F (e X)=Φ (4*t*U (split σ) X) := by
      change F (L X,R X)=_
      dsimp [F,U,split]
      simp_rw [hterm]
      congr 1
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs <;>rfl
    have hFP (p : (Fin N → Ω) × (Fin N → Ω)) : F (Prod.map L R p)=
        Φ (4*t*∑ i,∑ j,if σ i=true ∧ σ j=false then a i j (p.1 i) (p.2 j) else 0) := by
      dsimp [F,Prod.map]
      simp_rw [hterm]
    have hmap : (∫ p,F (Prod.map L R p) ∂ν.prod ν) = ∫ p,F p ∂ηI.prod ηJ := by
      rw [←hLR.map_eq]
      exact (integral_map hLR.measurable.aemeasurable hF.aestronglyMeasurable).symm
    calc
      _ = ∫ X,F (e X) ∂ν := integral_congr_ae (Filter.Eventually.of_forall fun X => (hFX X).symm)
      _ = ∫ p,F p ∂ηI.prod ηJ := he.integral_comp' F
      _ = ∫ p,F (Prod.map L R p) ∂ν.prod ν := hmap.symm
      _ = ∫ p,Φ (4*t*∑ i,∑ j,if σ i=true ∧ σ j=false then a i j (p.1 i) (p.2 j) else 0)
          ∂ν.prod ν := integral_congr_ae (Filter.Eventually.of_forall hFP)
      _ ≤ D := by
        have h := CanonicalKernelMaskBound μ N a ham A hA hab harow hacol σ (fun j => !(σ j)) (4*t) Φ hΦ hΦc
        simpa only [Bool.not_eq_true_eq_eq_false] using h
  let C : ℝ := Fintype.card (Fin N → Bool)
  have hC : C≠0 := by dsimp [C];exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Fin N → Bool)≠0)
  have hC0 : 0≤C⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hsumI : Integrable (fun X => ∑ σ : Fin N → Bool,Φ (4*t*U (split σ) X)) ν :=
    integrable_finset_sum _ (fun σ _ => hUI (split σ) (4*t))
  have hpoint (X : Fin N → Ω) : Φ (t*U all X) ≤
      C⁻¹*∑ σ : Fin N → Bool,Φ (4*t*U (split σ) X) := by
    have h := BernoulliSplitJensen N (fun i j => a i j (X i) (X j)) (fun i => by simp [a]) t Φ hΦ
    have hs (σ : Fin N → Bool) : U (split σ) X =
        ∑ i,∑ j,if σ i=true ∧ σ j=false then a i j (X i) (X j) else 0 := by
      dsimp [U,split]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs <;>rfl
    simp_rw [hs]
    simpa only [U,all,if_pos True.intro,C] using h
  have hbound := integral_mono_ae (hUI all t) (hsumI.const_mul C⁻¹)
    (Filter.Eventually.of_forall hpoint)
  rw [integral_const_mul,integral_finset_sum _ (fun σ _ => hUI (split σ) (4*t))] at hbound
  suffices hfinish : (∫ X,Φ (t*U all X) ∂ν) ≤ D by
    simpa only [U,all,if_pos True.intro,a,D,ν] using hfinish
  calc
    _ ≤ C⁻¹*∑ σ : Fin N → Bool,∫ X,Φ (4*t*U (split σ) X) ∂ν := hbound
    _ ≤ C⁻¹*∑ _ : Fin N → Bool,D :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun σ _ => hsplit σ)) hC0
    _ = D := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      change C⁻¹*(C*D)=D
      rw [←mul_assoc,inv_mul_cancel₀ hC,one_mul]
