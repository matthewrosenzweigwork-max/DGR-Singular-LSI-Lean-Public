module

public import Tablet.CenteredKernelBounds
public import Tablet.CenteredPairEnergy
public import Tablet.ProductDensity
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Group.Prod

@[expose] public section
open MeasureTheory ProbabilityTheory
-- [TABLET NODE: CenteredProductMean]
theorem CenteredProductMean (d N : ℕ) (g r : UnitAddTorus (Fin d) → ℝ)
    (hg : Measurable g) (hgi : Integrable g volume) (hr : Measurable r)
    (M c : ℝ) (hM : 1 ≤ M) (hc : 0 ≤ c)
    (hrb : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), 0 ≤ r x ∧ r x ≤ M)
    (hrmass : ∫ x, r x ∂volume = 1) (hgl : ∀ x, -c ≤ g x) :
    Measurable (CenteredPairEnergy (N := N) g r) ∧
    Measurable (ProductDensity (N := N) r) ∧
    Integrable (ProductDensity (N := N) r) volume ∧
    (∫ X : Configuration d N, ProductDensity r X ∂volume) = 1 ∧
    (∀ᵐ X ∂(volume : Measure (Configuration d N)),
      0 ≤ ProductDensity r X ∧ ProductDensity r X ≤ M ^ N) ∧
    Integrable (fun X : Configuration d N =>
      CenteredPairEnergy g r X * ProductDensity r X) volume ∧
    (∫ X : Configuration d N, CenteredPairEnergy g r X * ProductDensity r X ∂volume) = 0 := by
-- BODY
  classical
  haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
    infer_instance
  haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := by infer_instance
  haveI : IsProbabilityMeasure (volume : Measure (Configuration d N)) := by infer_instance
  let H := M * ∫ x, |g x| ∂volume
  obtain ⟨hpm,hpf,hpri,hJ,hcm,hcf,hcl⟩ :=
    CenteredKernelBounds d g r hg hgi hr M c hM hc hrb hrmass hgl
  have hrnorm : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), ‖r x‖ ≤ M := by
    filter_upwards [hrb] with x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2
  have hcoord (k : Fin N) : ∀ᵐ X ∂(volume : Measure (Configuration d N)),
      0 ≤ r (X k) ∧ r (X k) ≤ M :=
    (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin N =>
      (volume : Measure (UnitAddTorus (Fin d)))) (i := k)).eventually hrb
  have hmeasw : Measurable (ProductDensity (N := N) r) :=
    Finset.measurable_fun_prod _ (fun i _ => hr.comp (measurable_pi_apply i))
  have hmassw : (∫ X : Configuration d N, ProductDensity r X ∂volume) = 1 := by
    simpa only [ProductDensity,Fintype.card_fin,hrmass,one_pow] using
      (integral_fintype_prod_volume_eq_pow (ι := Fin N) r)
  have hintw : Integrable (ProductDensity (N := N) r) volume :=
    integrable_of_integral_eq_one hmassw
  have hwbound : ∀ᵐ X ∂(volume : Measure (Configuration d N)),
      0 ≤ ProductDensity r X ∧ ProductDensity r X ≤ M ^ N := by
    filter_upwards [ae_all_iff.mpr hcoord] with X hx
    constructor
    · exact Finset.prod_nonneg (fun k _ => (hx k).1)
    · simpa only [ProductDensity,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
        Finset.prod_le_prod (s := Finset.univ) (fun k _ => (hx k).1) (fun k _ => (hx k).2)
  have hpair (i j : Fin N) (hij : i ≠ j) :
      MeasurePreserving (fun X : Configuration d N => (X i,X j))
        volume ((volume : Measure (UnitAddTorus (Fin d))).prod volume) := by
    have hi := (iIndepFun_pi (μ := fun _ : Fin N =>
      (volume : Measure (UnitAddTorus (Fin d)))) (X := fun _ => id)
      (fun _ => aemeasurable_id)).indepFun hij
    refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j),?_⟩
    change Measure.map (fun X : Configuration d N => (X i,X j))
      (Measure.pi (fun _ : Fin N => (volume : Measure (UnitAddTorus (Fin d))))) = _
    have h := hi.map_prod_eq_prod_map_map
      (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
    simpa only [(measurePreserving_eval (fun _ : Fin N =>
      (volume : Measure (UnitAddTorus (Fin d)))) i).map_eq,
      (measurePreserving_eval (fun _ : Fin N =>
      (volume : Measure (UnitAddTorus (Fin d)))) j).map_eq] using h
  have hdiff : MeasurePreserving
      (fun p : UnitAddTorus (Fin d) × UnitAddTorus (Fin d) => p.1-p.2)
      (volume.prod volume) volume :=
    measurePreserving_fst.comp (measurePreserving_sub_prod volume volume)
  have hrawi : Integrable
      (fun p : UnitAddTorus (Fin d) × UnitAddTorus (Fin d) => CenteredKernel g r p.1 p.2)
      (volume.prod volume) := by
    refine ((hdiff.integrable_comp hg.aestronglyMeasurable).mpr hgi).abs.add
      (integrable_const (3*H)) |>.mono' hcm.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun p => by
      have h1 := norm_sub_le (g (p.1-p.2)) (BackgroundPotential g r p.1)
      have h2 := norm_sub_le (g (p.1-p.2)-BackgroundPotential g r p.1)
        (BackgroundPotential g r p.2)
      have h3 := norm_add_le
        (g (p.1-p.2)-BackgroundPotential g r p.1-BackgroundPotential g r p.2)
        (BackgroundPairMean g r)
      simp only [Real.norm_eq_abs] at h1 h2 h3 ⊢
      dsimp [CenteredKernel]
      linarith [(hpf p.1).2,(hpf p.2).2,hJ]
  let F : UnitAddTorus (Fin d) × UnitAddTorus (Fin d) → ℝ :=
    fun p => CenteredKernel g r p.1 p.2 * r p.1 * r p.2
  have hFm : Measurable F := (hcm.mul (hr.comp measurable_fst)).mul (hr.comp measurable_snd)
  have hFi : Integrable F (volume.prod volume) :=
    (hrawi.mul_bdd (hr.comp measurable_fst).aestronglyMeasurable
      (measurePreserving_fst.quasiMeasurePreserving.ae hrnorm)).mul_bdd
      (hr.comp measurable_snd).aestronglyMeasurable
      (measurePreserving_snd.quasiMeasurePreserving.ae hrnorm)
  have hFmean : (∫ p, F p ∂volume.prod volume) = 0 := by
    rw [integral_prod F hFi]
    have heq (x y : UnitAddTorus (Fin d)) : F (x,y) =
      r x * (CenteredKernel g r x y*r y) := by dsimp [F];ring
    simp_rw [heq,integral_const_mul,fun x => (hcf x).2,mul_zero]
    simp
  have weighted_pair (i j : Fin N) (hij : i ≠ j) :
      Integrable (fun X : Configuration d N => CenteredKernel g r (X i) (X j) * ProductDensity r X) volume ∧
      (∫ X : Configuration d N, CenteredKernel g r (X i) (X j) * ProductDensity r X ∂volume) = 0 := by
    let S : Finset (Fin N) := {i,j}
    let T : Finset (Fin N) := (Finset.univ.erase i).erase j
    let a : Configuration d N → ℝ := fun X => F (X i,X j)
    let b : Configuration d N → ℝ := fun X => ∏ k ∈ T, r (X k)
    have ham : Measurable a := hFm.comp ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
    have hai : Integrable a volume := (hpair i j hij).integrable_comp hFm.aestronglyMeasurable |>.mpr hFi
    have hamean : (∫ X, a X ∂volume) = 0 := by
      rw [← hFmean,← (hpair i j hij).map_eq]
      exact (integral_map (hpair i j hij).measurable.aemeasurable hFm.aestronglyMeasurable).symm
    have hbm : Measurable b := Finset.measurable_fun_prod _ (fun k _ => hr.comp (measurable_pi_apply k))
    have hb : ∀ᵐ X ∂(volume : Measure (Configuration d N)), ‖b X‖ ≤ M^T.card := by
      filter_upwards [ae_all_iff.mpr hcoord] with X hx
      rw [Real.norm_eq_abs,abs_of_nonneg (Finset.prod_nonneg (fun k _ => (hx k).1))]
      simpa only [b,Finset.prod_const] using
        Finset.prod_le_prod (s := T) (fun k _ => (hx k).1) (fun k _ => (hx k).2)
    have hind : IndepFun a b (volume : Measure (Configuration d N)) := by
      have hST : Disjoint S T := by simp [S,T,Finset.disjoint_left]
      have hI := iIndepFun_pi (μ := fun _ : Fin N =>
        (volume : Measure (UnitAddTorus (Fin d)))) (X := fun _ => id) (fun _ => aemeasurable_id)
      have hR := hI.indepFun_finset S T hST (fun k => measurable_pi_apply k)
      let A : (S → UnitAddTorus (Fin d)) → ℝ :=
        fun V => F (V ⟨i,by simp [S]⟩,V ⟨j,by simp [S]⟩)
      let B : (T → UnitAddTorus (Fin d)) → ℝ := fun V => ∏ k, r (V k)
      have hAm : Measurable A := hFm.comp
        ((measurable_pi_apply (⟨i,by simp [S]⟩ : S)).prodMk
          (measurable_pi_apply (⟨j,by simp [S]⟩ : S)))
      have hBm : Measurable B := Finset.measurable_fun_prod _ (fun k _ => hr.comp (measurable_pi_apply k))
      have h := hR.comp hAm hBm
      change IndepFun a (fun X : Configuration d N => B (fun k : T => X k)) _ at h
      have hsame : (fun X : Configuration d N => B (fun k : T => X k)) = b := by
        funext X
        exact Finset.prod_coe_sort T (fun k => r (X k))
      rw [hsame] at h
      exact h
    have heq (X : Configuration d N) :
        CenteredKernel g r (X i) (X j)*ProductDensity r X = a X*b X := by
      have hp : (∏ k : Fin N, r (X k)) = r (X i)*r (X j)*∏ k ∈ T, r (X k) := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
          ← Finset.mul_prod_erase _ _ (show j ∈ (Finset.univ.erase i : Finset (Fin N)) by simp [hij,Ne.symm hij])]
        ring
      simp only [ProductDensity,hp,a,b,F]
      ring
    constructor
    · simp_rw [heq]
      exact hai.mul_bdd hbm.aestronglyMeasurable hb
    · simp_rw [heq]
      rw [hind.integral_fun_mul_eq_mul_integral ham.aestronglyMeasurable hbm.aestronglyMeasurable,hamean,zero_mul]
  have hterm (i j : Fin N) : Integrable
      (fun X : Configuration d N => (if i<j then CenteredKernel g r (X i) (X j) else 0)*ProductDensity r X) volume := by
    by_cases h : i<j
    · simpa only [h,↓reduceIte] using (weighted_pair i j (ne_of_lt h)).1
    · simpa only [h,↓reduceIte,zero_mul] using (integrable_const (0 : ℝ) : Integrable (fun _ : Configuration d N => (0:ℝ)) volume)
  have hrepr (X : Configuration d N) : CenteredPairEnergy g r X*ProductDensity r X =
      (N:ℝ)⁻¹*∑ i : Fin N,∑ j : Fin N,
        (if i<j then CenteredKernel g r (X i) (X j) else 0)*ProductDensity r X := by
    simp only [CenteredPairEnergy,Finset.sum_mul,mul_assoc]
  have heint : Integrable (fun X : Configuration d N => CenteredPairEnergy g r X*ProductDensity r X) volume := by
    simp_rw [hrepr]
    exact (integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hterm i j))).const_mul _
  have hem : Measurable (CenteredPairEnergy (N := N) g r) := by
    unfold CenteredPairEnergy
    have htm (i j : Fin N) : Measurable (fun X : Configuration d N =>
        if i<j then CenteredKernel g r (X i) (X j) else 0) := by
      by_cases h : i<j
      · simp only [h,↓reduceIte]
        have hx : Measurable (fun X : Configuration d N => (X i,X j)) :=
          (measurable_pi_apply i).prodMk (measurable_pi_apply j)
        have hh := hcm.comp hx
        exact hh
      · simpa only [h,↓reduceIte] using
          (measurable_const : Measurable (fun _ : Configuration d N => (0:ℝ)))
    exact (Finset.measurable_fun_sum _ (fun i _ =>
      Finset.measurable_fun_sum _ (fun j _ => htm i j))).const_mul _
  refine ⟨hem,hmeasw,hintw,hmassw,hwbound,heint,?_⟩
  simp_rw [hrepr]
  rw [integral_const_mul,integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hterm i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hterm _ j)]
  have hz (i j : Fin N) :
      (∫ X : Configuration d N, (if i<j then CenteredKernel g r (X i) (X j) else 0)*ProductDensity r X ∂volume) = 0 := by
    by_cases h : i<j
    · simpa only [h,↓reduceIte] using (weighted_pair i j (ne_of_lt h)).2
    · simp [h]
  simp_rw [hz]
  simp
