import Tablet.AtomicInteractionSource
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
set_option maxHeartbeats 1600000
open MeasureTheory Set

-- [TABLET NODE: AtomicCoulombSourceMass]
theorem AtomicCoulombSourceMass (d : ℕ) (hd : 3 ≤ d) :
    let C := ∫ z : OneParticle d,
      (d : ℝ) * (‖z‖ ^ 2 + 1) ^ (-((d : ℝ) + 2) / 2)
    0 ≤ C ∧ ∀ {ι : Type*} (J : Finset ι) (a : ι → ℝ)
      (y : ι → OneParticle d) (ε : ℝ),
      0 < ε → (∀ j ∈ J, 0 ≤ a j) →
      let U := fun x => ∑ j ∈ J, a j * RieszKernel ((d : ℝ) - 2) ε (x - y j)
      Integrable (fun x => -EuclideanLaplacian U x) ∧
      (∫ x, -EuclideanLaplacian U x) = (∑ j ∈ J, a j) * C ∧
      ∀ K : Set (OneParticle d),
        IntegrableOn (fun x => -EuclideanLaplacian U x) K ∧
        (∫ x in K, -EuclideanLaplacian U x) ≤ (∑ j ∈ J, a j) * C := by
-- BODY
  let ρ := fun (ε : ℝ) (z : OneParticle d) =>
    (d : ℝ) * ε ^ 2 * (‖z‖ ^ 2 + ε ^ 2) ^ (-((d : ℝ) + 2) / 2)
  have hn (ε : ℝ) (z : OneParticle d) : 0 ≤ ρ ε z := by dsimp [ρ]; positivity
  have hi1 : Integrable (ρ 1) := by
    have h := (integrable_rpow_neg_one_add_norm_sq
      (μ := (volume : Measure (OneParticle d)))
      (r := (d : ℝ) + 2) (by simp [OneParticle])).const_mul (d : ℝ)
    convert h using 1
    funext x
    simp only [ρ, one_pow, mul_one]
    rw [add_comm (1 : ℝ)]
  have hscale (ε : ℝ) (hε : 0 < ε) (z : OneParticle d) :
      ρ ε (ε • z) = ε ^ (-(d : ℝ)) * ρ 1 z := by
    have hnorm : ‖ε • z‖ = ε * ‖z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    have hb : (ε * ‖z‖) ^ 2 + ε ^ 2 = ε ^ 2 * (‖z‖ ^ 2 + 1) := by ring
    have hp : ε ^ 2 * (ε ^ 2) ^ (-((d : ℝ) + 2) / 2) = ε ^ (-(d : ℝ)) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hε.le, ← Real.rpow_add hε]
      congr 1
      ring
    dsimp [ρ]
    rw [hnorm, hb, Real.mul_rpow (by positivity) (by positivity)]
    simp only [one_pow, mul_one]
    rw [show (d : ℝ) * ε ^ 2 *
      ((ε ^ 2) ^ (-((d : ℝ) + 2) / 2) * (‖z‖ ^ 2 + 1) ^ (-((d : ℝ) + 2) / 2)) =
      (d : ℝ) * (ε ^ 2 * (ε ^ 2) ^ (-((d : ℝ) + 2) / 2)) *
        (‖z‖ ^ 2 + 1) ^ (-((d : ℝ) + 2) / 2) by ring, hp]
    ring
  have hi (ε : ℝ) (hε : 0 < ε) : Integrable (ρ ε) := by
    apply (integrable_comp_smul_iff volume (ρ ε) hε.ne').mp
    simpa only [hscale ε hε] using hi1.const_mul (ε ^ (-(d : ℝ)))
  have ht (ε : ℝ) (hε : 0 < ε) : (∫ z, ρ ε z) = ∫ z, ρ 1 z := by
    have h := Measure.integral_comp_smul_of_nonneg
      (volume : Measure (OneParticle d)) (ρ ε) ε (hR := hε.le)
    simp only [OneParticle, finrank_euclideanSpace_fin, smul_eq_mul] at h
    simp_rw [hscale ε hε] at h
    rw [integral_const_mul] at h
    have he : ε ^ (-(d : ℝ)) = (ε ^ d)⁻¹ := by
      rw [Real.rpow_neg, Real.rpow_natCast]
      exact hε.le
    rw [he] at h
    exact (mul_left_cancel₀ (inv_ne_zero (pow_ne_zero d hε.ne')) h).symm
  have hC : (∫ z, ρ 1 z) = ∫ z : OneParticle d,
      (d : ℝ) * (‖z‖ ^ 2 + 1) ^ (-((d : ℝ) + 2) / 2) := by simp [ρ]
  refine ⟨?_, ?_⟩
  · rw [← hC]
    exact integral_nonneg (hn 1)
  intro ι J a y ε hε ha
  dsimp only
  let U := fun x => ∑ j ∈ J, a j * RieszKernel ((d : ℝ) - 2) ε (x - y j)
  have hs : 0 < (d : ℝ) - 2 := by
    have hh : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hsource := AtomicInteractionSource d ((d : ℝ) - 2) ε hs le_rfl hε J a y ha
  have he : (fun x => -EuclideanLaplacian U x) =
      fun x => ∑ j ∈ J, a j * ρ ε (x - y j) := by
    funext x
    rw [(hsource.2 x).1]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [ρ]
    rw [show -((d : ℝ) - 2) / 2 - 2 = -((d : ℝ) + 2) / 2 by ring]
    ring
  have htrans (j : ι) : Integrable (fun x => ρ ε (x - y j)) := by
    simpa only [sub_eq_add_neg] using (hi ε hε).comp_add_right (-y j)
  have hUi : Integrable (fun x => -EuclideanLaplacian U x) := by
    rw [he]
    exact integrable_finsetSum J (fun j hj => (htrans j).const_mul (a j))
  have hmass : (∫ x, -EuclideanLaplacian U x) =
      (∑ j ∈ J, a j) * (∫ z, ρ 1 z) := by
    rw [he, integral_finsetSum J (fun j hj => (htrans j).const_mul (a j))]
    simp_rw [integral_const_mul]
    have hj (j : ι) : (∫ x, ρ ε (x - y j)) = ∫ z, ρ 1 z := by
      calc
        _ = ∫ x, ρ ε x := by
          simpa only [sub_eq_add_neg] using integral_add_right_eq_self (ρ ε) (-y j)
        _ = _ := ht ε hε
    simp_rw [hj]
    rw [Finset.sum_mul]
  refine ⟨hUi, hmass.trans (congrArg ((∑ j ∈ J, a j) * ·) hC), ?_⟩
  intro K
  refine ⟨hUi.integrableOn, ?_⟩
  rw [← hC, ← hmass]
  exact setIntegral_le_integral hUi (Filter.Eventually.of_forall (fun x => (hsource.2 x).2))
