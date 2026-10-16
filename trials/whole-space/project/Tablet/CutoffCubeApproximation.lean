module

public import Tablet.EuclideanCubeNeumann
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

@[expose] public section

open MeasureTheory Set Function
open scoped ContDiff NNReal
noncomputable section

namespace CutoffCubeApproximation

private theorem grad_cont (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) : Continuous (gradient f) :=
  (InnerProductSpace.toDual ℝ _).symm.continuous.comp
    (hf.continuous_fderiv (by norm_num))

private theorem grad_norm (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (x) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ :=
  (InnerProductSpace.toDual ℝ _).symm.norm_map _

private theorem comp_energy (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (h : ℝ → ℝ) (hh : ContDiff ℝ 1 h) (x) :
    ‖gradient (fun y => h (f y)) x‖^2 = (deriv h (f x))^2*‖gradient f x‖^2 := by
  have hd := (hh.differentiable (by norm_num) (f x)).hasDerivAt.comp_hasFDerivAt x
    (hf.differentiable (by norm_num) x).hasFDerivAt
  rw [grad_norm, grad_norm]
  change ‖fderiv ℝ (h ∘ f) x‖^2 = _
  rw [hd.fderiv, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

private theorem product_energy (n : ℕ) (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (x) :
    ‖gradient (fun y => f y*g y) x‖^2 ≤
      2*(f x)^2*‖gradient g x‖^2+2*(g x)^2*‖gradient f x‖^2 := by
  have hd := (hf.differentiable (by norm_num) x).hasFDerivAt.mul
    (hg.differentiable (by norm_num) x).hasFDerivAt
  have hn : ‖gradient (fun y => f y*g y) x‖ ≤
      |f x| * ‖gradient g x‖+|g x| * ‖gradient f x‖ := by
    rw [grad_norm, grad_norm, grad_norm]
    change ‖fderiv ℝ (f*g) x‖ ≤ _
    rw [hd.fderiv]
    simpa only [norm_smul, Real.norm_eq_abs] using
      norm_add_le (f x • fderiv ℝ g x) (g x • fderiv ℝ f x)
  calc
    _ ≤ (|f x| * ‖gradient g x‖+|g x| * ‖gradient f x‖)^2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
    _ ≤ 2*(|f x| * ‖gradient g x‖)^2+2*(|g x| * ‖gradient f x‖)^2 := by
      nlinarith [sq_nonneg (|f x| * ‖gradient g x‖-|g x| * ‖gradient f x‖)]
    _ = _ := by simp only [mul_pow, sq_abs]; ring

private theorem cube_compact (n : ℕ) (a b : ℝ) :
    IsCompact {x : EuclideanSpace ℝ (Fin n) | ∀ i, a ≤ x i ∧ x i ≤ b} := by
  have hc := (isCompact_univ_pi (fun _ : Fin n => isCompact_Icc (a := a) (b := b))).image
    (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous
  convert hc using 1
  ext x
  change (∀ i, a ≤ x i ∧ x i ≤ b) ↔
    ∃ q ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc a b), WithLp.toLp 2 q = x
  constructor
  · intro hx
    exact ⟨x.ofLp, by simpa only [Set.mem_pi, Set.mem_univ, forall_true_left,
      Set.mem_Icc] using hx, rfl⟩
  · rintro ⟨q, hq, he⟩
    rw [← he]
    simpa only [WithLp.ofLp_toLp, Set.mem_pi, Set.mem_univ, forall_true_left,
      Set.mem_Icc] using hq

private theorem weighted_upper {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (g : α → ℝ) (hg : Measurable g) (ρ : α → ℝ≥0) (hρ : Measurable ρ)
    (Q : Set α) (hQ : MeasurableSet Q) (hi : IntegrableOn (fun x => g x^2) Q μ)
    (D : ℝ) (hD : 0 ≤ D) (hu : ∀ x ∈ Q, (ρ x : ℝ) ≤ D) :
    IntegrableOn (fun x => g x^2) Q (μ.withDensity (fun x => ρ x)) ∧
    (∫ x in Q, g x^2 ∂μ.withDensity (fun x => ρ x)) ≤ D*(∫ x in Q, g x^2 ∂μ) := by
  have hm := hρ.coe_nnreal_real.mul (hg.pow_const 2)
  have hip : IntegrableOn (fun x => (ρ x : ℝ)*g x^2) Q μ :=
    (hi.const_mul D).mono' hm.aestronglyMeasurable (by
      filter_upwards [ae_restrict_mem hQ] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right (hu x hx) (sq_nonneg _))
  have hw : IntegrableOn (fun x => g x^2) Q (μ.withDensity (fun x => ρ x)) := by
    rw [IntegrableOn, restrict_withDensity hQ]
    simpa only [NNReal.smul_def, smul_eq_mul] using
      (integrable_withDensity_iff_integrable_smul hρ).mpr hip
  refine ⟨hw, ?_⟩
  rw [setIntegral_withDensity_eq_setIntegral_smul hρ _ hQ]
  have h := integral_mono_ae hip (hi.const_mul D) (by
    filter_upwards [ae_restrict_mem hQ] with x hx
    exact mul_le_mul_of_nonneg_right (hu x hx) (sq_nonneg _))
  rw [integral_const_mul] at h
  simpa only [NNReal.smul_def, smul_eq_mul] using h

private theorem bounded_sq {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsFiniteMeasure ν] (g : α → ℝ) (hg : Measurable g) (B : ℝ)
    (hB : 0 ≤ B) (hb : ∀ x, |g x| ≤ B) : Integrable (fun x => g x^2) ν := by
  apply (integrable_const (B^2)).mono' (hg.pow_const 2).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (hb x)

private theorem diff_sq {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsFiniteMeasure ν] (f g : α → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hi : Integrable (fun x => f x^2) ν) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, |g x| ≤ B) : Integrable (fun x => (f x-g x)^2) ν := by
  have hgI := bounded_sq ν g hg B hB hb
  apply ((hi.const_mul 2).add (hgI.const_mul 2)).mono'
    ((hf.sub hg).pow_const 2).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change (f x-g x)^2 ≤ 2*f x^2+2*g x^2
  nlinarith [sq_nonneg (f x+g x)]

end CutoffCubeApproximation

-- [TABLET NODE: CutoffCubeApproximation]
theorem CutoffCubeApproximation (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ, a < b →
    ∀ f U : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 f → ContDiff ℝ 1 U →
    ∀ (ρ : EuclideanSpace ℝ (Fin n) → ℝ≥0), Measurable ρ →
      IsFiniteMeasure (volume.withDensity (fun x => ρ x)) →
      Integrable (fun x => f x^2) (volume.withDensity (fun x => ρ x)) →
      Integrable (fun x => ‖EuclideanGradient f x‖^2)
        (volume.withDensity (fun x => ρ x)) →
    ∀ (χ h : ℝ → ℝ), ContDiff ℝ 1 χ → ContDiff ℝ 1 h →
    ∀ m T D β K V S : ℝ, 0 < m → 0 < T → 0 ≤ D → 0 < β → 0 ≤ K →
      0 ≤ V → 0 ≤ S →
      (∀ u, 0 ≤ χ u ∧ χ u ≤ 1 ∧ (2*T ≤ u → χ u = 0)) →
      (∀ u, |h u| ≤ 2*m ∧ |deriv h u| ≤ K) →
      let Q := {x : EuclideanSpace ℝ (Fin n) | ∀ i, a ≤ x i ∧ x i ≤ b}
      (∀ x ∈ Q, (ρ x : ℝ) ≤ D) →
      (∀ x ∈ Q, U x ≤ 2*T → β ≤ (ρ x : ℝ)) →
      (∫ x in Q, (1-χ (U x))^2) ≤ V/T →
      (∫ x in Q, ‖EuclideanGradient (fun y => χ (U y)) x‖^2) ≤ S/T →
      let ν := volume.withDensity (fun x => ρ x)
      let F := fun x => χ (U x)*h (f x)
      let c := (∫ x in Q, F x)/(b-a)^n
      Integrable (fun x => (f x-h (f x))^2) ν ∧
      IntegrableOn (fun x => ‖EuclideanGradient F x‖^2) Q ∧
      IntegrableOn (fun x => (f x-c)^2) Q ν ∧
      (∫ x in Q, (f x-c)^2 ∂ν) ≤
        3*((∫ x, (f x-h (f x))^2 ∂ν)+D*(2*m)^2*(V/T)+
          D*C*(b-a)^2*((2*K^2/β)*(∫ x in Q, ‖EuclideanGradient f x‖^2 ∂ν)+
            8*m^2*(S/T))) := by
-- BODY
  obtain ⟨C, hC, hPI⟩ := EuclideanCubeNeumann n
  refine ⟨C, hC, ?_⟩
  intro a b hab f U hf hU ρ hρ hfinite hSq hEi χ h hχ hh m T D β K V S
    hm hT hD hβ hK hV hS hr hb
  dsimp only
  intro hUpper hLower hErr hSource
  let Q := {x : EuclideanSpace ℝ (Fin n) | ∀ i, a ≤ x i ∧ x i ≤ b}
  let ν := volume.withDensity (fun x => ρ x)
  let g := fun x => h (f x)
  let z := fun x => χ (U x)
  let F := fun x => z x*g x
  let c := (∫ x in Q, F x)/(b-a)^n
  letI : IsFiniteMeasure ν := hfinite
  have hcQ := CutoffCubeApproximation.cube_compact n a b
  have hQ : MeasurableSet Q := hcQ.isClosed.measurableSet
  have hg : ContDiff ℝ 1 g := hh.comp hf
  have hz : ContDiff ℝ 1 z := hχ.comp hU
  have hF : ContDiff ℝ 1 F := hz.mul hg
  have hgb : ∀ x, |g x| ≤ 2*m := fun x => (hb (f x)).1
  have hFb : ∀ x, |F x| ≤ 2*m := by
    intro x
    rw [abs_mul]
    have hx := hr (U x)
    have hz1 : |z x| ≤ 1 := by simpa [z, abs_of_nonneg hx.1] using hx.2.1
    exact (mul_le_mul hz1 (hgb x) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hfg := CutoffCubeApproximation.diff_sq ν f g hf.continuous.measurable
    hg.continuous.measurable hSq (2*m) (by positivity) hgb
  have hgI := CutoffCubeApproximation.bounded_sq ν g hg.continuous.measurable (2*m) (by positivity) hgb
  have hgF := CutoffCubeApproximation.diff_sq ν g F hg.continuous.measurable
    hF.continuous.measurable hgI (2*m) (by positivity) hFb
  have hFI := CutoffCubeApproximation.bounded_sq ν F hF.continuous.measurable (2*m) (by positivity) hFb
  have hFc := CutoffCubeApproximation.diff_sq ν F (fun _ => c) hF.continuous.measurable
    measurable_const hFI |c| (abs_nonneg _) (fun _ => le_rfl)
  have hfc := CutoffCubeApproximation.diff_sq ν f (fun _ => c) hf.continuous.measurable
    measurable_const hSq |c| (abs_nonneg _) (fun _ => le_rfl)
  have hEnergyI : IntegrableOn (fun x => ‖gradient F x‖^2) Q :=
    ((CutoffCubeApproximation.grad_cont n F hF).norm.pow 2).continuousOn.integrableOn_compact hcQ
  have hzI : IntegrableOn (fun x => ‖gradient z x‖^2) Q :=
    ((CutoffCubeApproximation.grad_cont n z hz).norm.pow 2).continuousOn.integrableOn_compact hcQ
  have hwEi : IntegrableOn (fun x => (ρ x : ℝ)*‖gradient f x‖^2) Q := by
    have hi := hEi.integrableOn (s := Q)
    rw [IntegrableOn, restrict_withDensity hQ] at hi
    simpa only [IntegrableOn, EuclideanGradient, NNReal.smul_def, smul_eq_mul] using
      (integrable_withDensity_iff_integrable_smul hρ).mp hi
  have hpoint (x) (hx : x ∈ Q) : ‖gradient F x‖^2 ≤
      (2*K^2/β)*((ρ x : ℝ)*‖gradient f x‖^2)+8*m^2*‖gradient z x‖^2 := by
    have hp := CutoffCubeApproximation.product_energy n z g hz hg x
    have hg2 : (g x)^2 ≤ 4*m^2 := by
      have hh2 := (sq_le_sq₀ (abs_nonneg (g x)) (by positivity : 0 ≤ 2*m)).mpr (hgb x)
      simp only [sq_abs] at hh2
      nlinarith only [hh2]
    have hmask : (z x)^2*‖gradient g x‖^2 ≤ (K^2/β)*(ρ x : ℝ)*‖gradient f x‖^2 := by
      by_cases hxz : z x = 0
      · rw [hxz, zero_pow (by decide : 2 ≠ 0), zero_mul]; positivity
      · have hu : U x ≤ 2*T := by
          by_contra hn
          exact hxz ((hr (U x)).2.2 (le_of_lt (lt_of_not_ge hn)))
        have hρx := hLower x hx hu
        have hcoef : K^2 ≤ (K^2/β)*(ρ x : ℝ) := by
          calc
            _ = (K^2/β)*β := by field_simp
            _ ≤ _ := mul_le_mul_of_nonneg_left hρx (by positivity)
        have hz2 : (z x)^2 ≤ 1 := by have hhx := hr (U x); dsimp [z]; nlinarith [hhx.1, hhx.2.1]
        have hc := CutoffCubeApproximation.comp_energy n f hf h hh x
        have hd2 : (deriv h (f x))^2 ≤ K^2 := by
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).mpr (hb (f x)).2
        calc
          _ ≤ ‖gradient g x‖^2 := mul_le_of_le_one_left (sq_nonneg _) hz2
          _ = (deriv h (f x))^2*‖gradient f x‖^2 := hc
          _ ≤ K^2*‖gradient f x‖^2 := mul_le_mul_of_nonneg_right hd2 (sq_nonneg _)
          _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
    have h1 : 2*(z x)^2*‖gradient g x‖^2 ≤
        (2*K^2/β)*((ρ x : ℝ)*‖gradient f x‖^2) := by
      simpa only [div_eq_mul_inv, mul_assoc] using
        mul_le_mul_of_nonneg_left hmask (by norm_num : (0 : ℝ) ≤ 2)
    have h2 : 2*(g x)^2*‖gradient z x‖^2 ≤ 8*m^2*‖gradient z x‖^2 := by
      nlinarith only [mul_le_mul_of_nonneg_right hg2
        (show 0 ≤ 2*‖gradient z x‖^2 by positivity)]
    exact hp.trans (add_le_add h1 h2)
  have hEnergy := integral_mono_ae hEnergyI
    ((hwEi.const_mul (2*K^2/β)).add (hzI.const_mul (8*m^2))) (by
      filter_upwards [ae_restrict_mem hQ] with x hx
      simpa only [Pi.add_apply] using hpoint x hx)
  simp only [Pi.add_apply] at hEnergy
  rw [integral_add (hwEi.const_mul _) (hzI.const_mul _), integral_const_mul, integral_const_mul] at hEnergy
  have hconv := setIntegral_withDensity_eq_setIntegral_smul (μ := volume) hρ (fun x => ‖gradient f x‖^2) hQ
  simp only [NNReal.smul_def, smul_eq_mul] at hconv
  rw [← hconv] at hEnergy
  have hEnergyBound := hEnergy.trans (add_le_add_right
    (mul_le_mul_of_nonneg_left hSource (show 0 ≤ 8*m^2 by positivity)) _)
  have herrorI : IntegrableOn (fun x => (1-z x)^2) Q :=
    ((continuous_const.sub hz.continuous).pow 2).continuousOn.integrableOn_compact hcQ
  have hcut := CutoffCubeApproximation.weighted_upper volume (fun x => g x-F x)
    (hg.continuous.sub hF.continuous).measurable ρ hρ Q hQ
    (((hg.continuous.sub hF.continuous).pow 2).continuousOn.integrableOn_compact hcQ) D hD hUpper
  have hcutL := integral_mono
    (((hg.continuous.sub hF.continuous).pow 2).continuousOn.integrableOn_compact hcQ)
    (herrorI.const_mul ((2*m)^2)) (fun x => by
      have hb2 := (sq_le_sq₀ (abs_nonneg (g x)) (by positivity : 0 ≤ 2*m)).mpr (hgb x)
      simp only [sq_abs] at hb2
      have hp := mul_le_mul_of_nonneg_right hb2 (sq_nonneg (1-z x))
      dsimp [F]; nlinarith only [hp])
  rw [integral_const_mul] at hcutL
  have hcutBound : (∫ x in Q, (g x-F x)^2 ∂ν) ≤ D*(2*m)^2*(V/T) := by
    calc
      _ ≤ D*(∫ x in Q, (g x-F x)^2) := hcut.2
      _ ≤ D*((2*m)^2*(∫ x in Q, (1-z x)^2)) := mul_le_mul_of_nonneg_left hcutL hD
      _ ≤ D*((2*m)^2*(V/T)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hErr (sq_nonneg _)) hD
      _ = _ := by ring
  have hPI' := hPI a b hab F hF
  have hweighted := CutoffCubeApproximation.weighted_upper volume (fun x => F x-c)
    (hF.continuous.sub continuous_const).measurable ρ hρ Q hQ
    (((hF.continuous.sub continuous_const).pow 2).continuousOn.integrableOn_compact hcQ) D hD hUpper
  have hcoef : 0 ≤ D*C*(b-a)^2 := by positivity
  have hconstBound : (∫ x in Q, (F x-c)^2 ∂ν) ≤ D*C*(b-a)^2*
      ((2*K^2/β)*(∫ x in Q, ‖EuclideanGradient f x‖^2 ∂ν)+8*m^2*(S/T)) := by
    calc
      _ ≤ D*(∫ x in Q, (F x-c)^2) := hweighted.2
      _ ≤ D*(C*(b-a)^2*(∫ x in Q, ‖EuclideanGradient F x‖^2)) :=
        mul_le_mul_of_nonneg_left hPI' hD
      _ = D*C*(b-a)^2*(∫ x in Q, ‖gradient F x‖^2) := by unfold EuclideanGradient; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hEnergyBound hcoef
  have hclip := setIntegral_le_integral hfg
    (Filter.Eventually.of_forall (fun x => sq_nonneg (f x-g x))) (s := Q)
  have htri := integral_mono (μ := ν.restrict Q) hfc.integrableOn
    (((hfg.integrableOn.add hgF.integrableOn).add hFc.integrableOn).const_mul 3)
    (fun x => by
      change (f x-c)^2 ≤ 3*((f x-g x)^2+(g x-F x)^2+(F x-c)^2)
      nlinarith [sq_nonneg ((f x-g x)-(g x-F x)),
        sq_nonneg ((f x-g x)-(F x-c)), sq_nonneg ((g x-F x)-(F x-c))])
  simp only [Pi.add_apply] at htri
  rw [integral_const_mul] at htri
  have hi1 : Integrable (fun x => (f x-g x)^2) (ν.restrict Q) := hfg.integrableOn
  have hi2 : Integrable (fun x => (g x-F x)^2) (ν.restrict Q) := hgF.integrableOn
  have hi3 : Integrable (fun x => (F x-c)^2) (ν.restrict Q) := hFc.integrableOn
  have hi12 : Integrable (fun x => (f x-g x)^2+(g x-F x)^2) (ν.restrict Q) := by
    convert hi1.add hi2 using 1 <;> rfl
  rw [integral_add (μ := ν.restrict Q) (f := fun x => (f x-g x)^2+(g x-F x)^2)
    (g := fun x => (F x-c)^2) hi12 hi3,
    integral_add (μ := ν.restrict Q) (f := fun x => (f x-g x)^2) (g := fun x => (g x-F x)^2)
      hi1 hi2] at htri
  exact ⟨hfg, hEnergyI, hfc.integrableOn, htri.trans
    (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hclip hcutBound) hconstBound) (by norm_num))⟩
