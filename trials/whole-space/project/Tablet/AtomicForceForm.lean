import Tablet.AtomicForceWeak
import Tablet.WeakPotentialForm
import Tablet.ForceExponentRange
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped ENNReal NNReal

-- [TABLET NODE: AtomicForceForm]
theorem AtomicForceForm (d : ℕ) (hd : 3 ≤ d) (s : ℝ)
    (hs : 0 < s) (hsd : s ≤ (d : ℝ) - 2) :
    ∃ K : ℝ≥0, ∀ {ι : Type*} (J : Finset ι) (a : ι → ℝ)
      (y : ι → OneParticle d) (ε A : ℝ),
      (∀ j ∈ J, 0 ≤ a j) → (∑ j ∈ J, a j ≤ A) → 0 ≤ A → 0 < ε →
      ∀ ψ : OneParticle d → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      Integrable (fun x => ‖EuclideanGradient (fun z => ∑ j ∈ J,
        a j * RieszKernel s ε (z - y j)) x‖ ^ (ForceExponent s) * (ψ x)^2) volume ∧
      (∫ x, ‖EuclideanGradient (fun z => ∑ j ∈ J,
        a j * RieszKernel s ε (z - y j)) x‖ ^ (ForceExponent s) * (ψ x)^2) ≤
        (K : ℝ) * A ^ (ForceExponent s) * ∫ x, ‖EuclideanGradient ψ x‖^2 := by
-- BODY
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  let q := (d : ℝ) / 2
  let θ := ForceExponent s
  let ν := (d : ℝ) / (s + 1)
  have hq : 1 < q := by dsimp [q]; linarith
  have hθ : 0 < θ := (ForceExponentRange s hs).1
  have hsp : s + 1 ≠ 0 := by linarith
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hexp : 1 - 1 / q = 1 - 2 / (d : ℝ) := by dsimp [q]; field_simp
  have hνq : ν / θ = q := by dsimp [ν, θ, ForceExponent, q]; field_simp
  have hνq' : ν * (1 / q) = θ := by dsimp [ν, q, θ, ForceExponent]; field_simp
  obtain ⟨B, hB⟩ := WeakPotentialForm d hd q hq hexp
  obtain ⟨C, hC, hweak⟩ := AtomicForceWeak d hd s hs hsd
  let R : ℝ≥0 := ⟨C ^ (1 / q), (Real.rpow_pos_of_pos hC _).le⟩
  refine ⟨B * R, ?_⟩
  intro ι J a y ε A ha hA hA0 hε ψ hψ hcψ
  let U := fun z => ∑ j ∈ J, a j * RieszKernel s ε (z - y j)
  have hU : ContDiff ℝ 1 U := by
    apply ContDiff.sum
    intro j hj
    have hk : ContDiff ℝ 1 (RieszKernel (d := d) s ε) := by
      unfold RieszKernel
      simp only [if_neg (ne_of_gt hε)]
      exact (((contDiff_norm_sq ℝ).add contDiff_const).rpow_const_of_ne
        (fun x => (show 0 < ‖x‖^2 + ε^2 by positivity).ne')).div_const s
    exact contDiff_const.mul (hk.comp (contDiff_id.sub contDiff_const))
  let F := fun x => ‖EuclideanGradient U x‖
  have hFc : Continuous F := by
    have hn : F = fun x => ‖fderiv ℝ U x‖ :=
      funext (fun x => (GradientNormIdentity U x).2)
    rw [hn]
    exact (hU.continuous_fderiv (by norm_num)).norm
  have hiF : Integrable (fun x => (F x)^θ * (ψ x)^2) volume := by
    have hc : Continuous (fun x => (F x)^θ * (ψ x)^2) :=
      (hFc.rpow_const (fun x => Or.inr hθ.le)).mul (hψ.continuous.pow 2)
    exact hc.integrable_of_hasCompactSupport
      ((hcψ.comp_left (g := fun z : ℝ => z^2) (by simp)).mul_left)
  have hiG : Integrable (fun x => ‖EuclideanGradient ψ x‖^2) volume := by
    have hcs : HasCompactSupport (fun x => ‖fderiv ℝ ψ x‖^2) :=
      (hcψ.fderiv ℝ).comp_left (g := fun L : OneParticle d →L[ℝ] ℝ => ‖L‖^2) (by simp)
    have hi0 := ((hψ.continuous_fderiv (by norm_num)).norm.pow 2).integrable_of_hasCompactSupport
      (μ := (volume : Measure (OneParticle d))) hcs
    have hi : Integrable (fun x => ‖fderiv ℝ ψ x‖^2) volume :=
      hi0.congr (Eventually.of_forall (fun _ => rfl))
    exact hi.congr (Eventually.of_forall (fun x => by
      dsimp only
      rw [(GradientNormIdentity ψ x).2]))
  refine ⟨hiF, ?_⟩
  rcases eq_or_lt_of_le hA0 with hAzero | hApos
  · have hAeq : A = 0 := hAzero.symm
    have ha0 : ∀ j ∈ J, a j = 0 := by
      intro j hj
      exact le_antisymm ((Finset.single_le_sum ha hj).trans (by simpa [hAeq] using hA)) (ha j hj)
    have hUz : U = fun _ => 0 := by
      funext x
      exact Finset.sum_eq_zero (fun j hj => by simp [ha0 j hj])
    change (∫ x, ‖EuclideanGradient U x‖^θ * (ψ x)^2) ≤ _
    have hgz : EuclideanGradient U = fun _ => 0 := by
      rw [hUz]
      funext x
      simp [EuclideanGradient]
    simpa only [hgz, hAeq, norm_zero, Real.zero_rpow (ne_of_gt hθ),
      Real.zero_rpow (show ForceExponent s ≠ 0 from ne_of_gt hθ),
      zero_mul, mul_zero, integral_zero] using (le_refl (0 : ℝ))
  · have hD : 0 < C * A^ν := mul_pos hC (Real.rpow_pos_of_pos hApos _)
    have hpweak : ∀ t : ℝ, 0 < t → volume {x | t < (F x)^θ} ≤
        ENNReal.ofReal (C * A^ν) * ENNReal.ofReal (t^(-q)) := by
      intro t ht
      have ht' : 0 < t^(1/θ) := Real.rpow_pos_of_pos ht _
      have hid : (t^(1/θ))^θ = t := by
        rw [← Real.rpow_mul ht.le, one_div_mul_cancel (ne_of_gt hθ), Real.rpow_one]
      have hset : {x | t < (F x)^θ} = {x | t^(1/θ) < F x} := by
        ext x
        conv_lhs => lhs; rw [← hid]
        exact Real.rpow_lt_rpow_iff (Real.rpow_nonneg ht.le _) (norm_nonneg _) hθ
      rw [hset]
      have H := hweak J a y ε A ha hA hA0 hε (t^(1/θ)) ht'
      have hp : (A / t^(1/θ))^ν = A^ν * t^(-q) := by
        rw [Real.div_rpow hApos.le ht'.le, ← Real.rpow_mul ht.le]
        have he : 1/θ * ν = q := by calc
          _ = ν/θ := by ring
          _ = q := hνq
        rw [he, Real.rpow_neg ht.le]
        rfl
      rw [hp, ← mul_assoc, ENNReal.ofReal_mul (by positivity)] at H
      exact H
    have H := hB (C * A^ν) hD (fun x => (F x)^θ) (hFc.measurable.pow_const _)
      (fun x => Real.rpow_nonneg (norm_nonneg _) _) hpweak ψ hψ hcψ
    have hid : (C * A^ν)^(1/q) = C^(1/q) * A^θ := by
      rw [Real.mul_rpow hC.le (Real.rpow_nonneg hApos.le _), ← Real.rpow_mul hApos.le, hνq']
    rw [hid, ENNReal.ofReal_mul (Real.rpow_pos_of_pos hC _).le] at H
    have hleft : (∫⁻ x, ENNReal.ofReal ((F x)^θ) * ENNReal.ofReal ((ψ x)^2)) =
        ENNReal.ofReal (∫ x, (F x)^θ * (ψ x)^2) := by
      rw [ofReal_integral_eq_lintegral_ofReal hiF (Eventually.of_forall (fun x => by positivity))]
      exact lintegral_congr (fun x => (ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _)).symm)
    have hright : (∫⁻ x, ‖fderiv ℝ ψ x‖ₑ^(2 : ℕ)) =
        ENNReal.ofReal (∫ x, ‖EuclideanGradient ψ x‖^2) := by
      rw [ofReal_integral_eq_lintegral_ofReal hiG (Eventually.of_forall (fun x => sq_nonneg _))]
      apply lintegral_congr
      intro x
      rw [(GradientNormIdentity ψ x).2, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    have hR : ENNReal.ofReal (C^(1/q)) = (R : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_coe_nnreal]; rfl
    rw [hleft, hright, hR] at H
    rw [← mul_assoc, ← ENNReal.coe_mul, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)] at H
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp H
