import Tablet.ProductConfinementCalculus
import Tablet.PairInteractionForceForm
import Tablet.PairInteractionSource
import Tablet.EuclideanGroundState
import Tablet.UniformTraceAbsorption
import Tablet.ForceExponentRange
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1600000
open MeasureTheory Filter
open scoped ContDiff

-- [TABLET NODE: FixedNProductCoercivity]
theorem FixedNProductCoercivity (N d : ℕ) (hN : 0 < N) (hd : 3 ≤ d) (s B : ℝ)
    (hs : 0 < s) (hsd : s ≤ (d : ℝ) - 2) (hB : 0 ≤ B) (Ca : ℝ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ V : OneParticle d → ℝ, ContDiff ℝ 2 V →
      (∀ a : ℝ, 0 < a → ∀ z, EuclideanLaplacian V z ≤
        a * ‖EuclideanGradient V z‖ ^ (ForceExponent s) + Ca a) →
      ∀ coupling ε : ℝ, 0 ≤ coupling → coupling ≤ B → 0 < ε →
      ∀ f : ParticleConfig d N → ℝ, ContDiff ℝ 1 f → HasCompactSupport f →
      let W := fun X : ParticleConfig d N => ∑ i : Fin N, V (ParticlePosition X i)
      let U := PairInteraction (d := d) (N := N) s coupling ε
      let ψ := fun X => f X * Real.exp (-(W X + U X) / 2)
      (∫ X, ‖EuclideanGradient ψ X‖ ^ 2) / 2 +
        (∫ X, ‖EuclideanGradient W X + EuclideanGradient U X‖ ^ 2 * (ψ X)^2) / 8 +
        (∫ X, -EuclideanLaplacian U X * (ψ X)^2) / 2 ≤
        (∫ X, ‖EuclideanGradient f X‖ ^ 2 * Real.exp (-(W X + U X))) + C * (∫ X, (ψ X)^2) := by
-- BODY
  classical
  let θ := ForceExponent s
  have hθ : 0 < θ := (ForceExponentRange s hs).1
  have hθ2 : θ < 2 := (ForceExponentRange s hs).2
  obtain ⟨H, hH, hforce⟩ := PairInteractionForceForm d N hd s B hs hB
  let c := (2 : ℝ)^θ
  let a₀ := 1 / (4 * c * (1 + H))
  have ha₀ : 0 < a₀ := by dsimp [a₀, c]; positivity
  let P := (N : ℝ) ^ (1 - θ / 2)
  have hP : 0 < P := Real.rpow_pos_of_pos (by exact_mod_cast hN) _
  let CaN := fun a : ℝ => (N : ℝ) * Ca (a / P)
  let C := max 0 ((CaN a₀ + a₀ * c) / 2)
  refine ⟨C, le_max_left _ _, ?_⟩
  intro V hV hgrowth coupling ε ha haB hε f hf hcf
  let W := fun X : ParticleConfig d N => ∑ i : Fin N, V (ParticlePosition X i)
  let U := PairInteraction (d := d) (N := N) s coupling ε
  let Htot := fun X : ParticleConfig d N => W X + U X
  let ψ := fun X => f X * Real.exp (-Htot X / 2)
  obtain ⟨hW, hprod⟩ := ProductConfinementCalculus d N V hV
  have hsource := PairInteractionSource d N s coupling ε hs hsd ha hε
  have hU : ContDiff ℝ 2 U := hsource.1.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hHtot : ContDiff ℝ 2 Htot := hW.add hU
  have hψ : ContDiff ℝ 1 ψ := hf.mul (((hHtot.of_le (by norm_num)).neg.div_const 2).exp)
  have hcψ : HasCompactSupport ψ := hcf.mul_right
  have hcg (u : ParticleConfig d N → ℝ) (hu : ContDiff ℝ 1 u) :
      Continuous (EuclideanGradient u) :=
    (InnerProductSpace.toDual ℝ (ParticleConfig d N)).symm.continuous.comp
      (hu.continuous_fderiv (by norm_num))
  have hcl (u : ParticleConfig d N → ℝ) (hu : ContDiff ℝ 2 u) :
      Continuous (EuclideanLaplacian u) := by
    have hfd : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
    have hffd := hfd.continuous_fderiv (by norm_num)
    have he : EuclideanLaplacian u = fun X => ∑ k,
        EuclideanHessian u X (EuclideanSpace.basisFun (Fin N × Fin d) ℝ k)
          (EuclideanSpace.basisFun (Fin N × Fin d) ℝ k) :=
      funext (fun X => (EuclideanDerivativeCoordinates u X).2)
    rw [he]
    unfold EuclideanHessian
    fun_prop
  have hiweight (a : ParticleConfig d N → ℝ) (hac : Continuous a) :
      Integrable (fun X => a X * (ψ X)^2) volume := by
    have hc : HasCompactSupport (fun X => (ψ X)^2) :=
      hcψ.comp_left (g := fun z : ℝ => z^2) (by simp)
    exact (hac.mul (hψ.continuous.pow 2)).integrable_of_hasCompactSupport hc.mul_left
  have himass : Integrable (fun X => (ψ X)^2) volume := by
    simpa only [one_mul] using hiweight (fun _ => 1) continuous_const
  have hiT := hiweight (fun X => ‖EuclideanGradient W X + EuclideanGradient U X‖^2)
    (((hcg W (hW.of_le (by norm_num))).add (hcg U (hU.of_le (by norm_num)))).norm.pow 2)
  have hiQ := hiweight (EuclideanLaplacian W) (hcl W hW)
  have hiS := hiweight (fun X => -EuclideanLaplacian U X) (hcl U hU).neg
  have hforced := hforce coupling ε ha haB hε ψ hψ hcψ
  have hiF : Integrable (fun X => ‖EuclideanGradient U X‖^θ * (ψ X)^2) volume := hforced.1
  have hform : (∫ X, ‖EuclideanGradient U X‖^θ * (ψ X)^2) ≤ H * (∫ X, ‖EuclideanGradient ψ X‖^2) := hforced.2
  have hgradadd (X : ParticleConfig d N) : EuclideanGradient Htot X =
      EuclideanGradient W X + EuclideanGradient U X := by
    apply (InnerProductSpace.toDual ℝ (ParticleConfig d N)).injective
    rw [map_add, EuclideanGradient, EuclideanGradient, EuclideanGradient,
      toDual_gradient, toDual_gradient, toDual_gradient,
      fderiv_fun_add (hW.differentiable (by norm_num) X) (hU.differentiable (by norm_num) X)]
  have hlapadd (X : ParticleConfig d N) : EuclideanLaplacian Htot X =
      EuclideanLaplacian W X + EuclideanLaplacian U X := hW.contDiffAt.laplacian_add hU.contDiffAt
  have hID := EuclideanGroundState Htot f hHtot hf hcf
  have hpot : (fun X => (‖EuclideanGradient Htot X‖^2 / 4 - EuclideanLaplacian Htot X / 2) * (ψ X)^2) =
      (fun X => 1/4 * (‖EuclideanGradient W X + EuclideanGradient U X‖^2 * (ψ X)^2) -
        1/2 * (EuclideanLaplacian W X * (ψ X)^2) + 1/2 * (-EuclideanLaplacian U X * (ψ X)^2)) := by
    funext X
    rw [hgradadd, hlapadd]
    ring
  change (∫ X, ‖EuclideanGradient f X‖^2 * Real.exp (-Htot X)) =
    (∫ X, ‖EuclideanGradient ψ X‖^2) + ∫ X,
      (‖EuclideanGradient Htot X‖^2 / 4 - EuclideanLaplacian Htot X / 2) * (ψ X)^2 at hID
  have hisub : Integrable (fun X => 1/4 * (‖EuclideanGradient W X + EuclideanGradient U X‖^2 * (ψ X)^2) -
      1/2 * (EuclideanLaplacian W X * (ψ X)^2)) volume :=
    ((hiT.const_mul (1/4)).sub (hiQ.const_mul (1/2))).congr (Eventually.of_forall (fun _ => rfl))
  rw [hpot, integral_add hisub (hiS.const_mul (1/2)),
    integral_sub (hiT.const_mul (1/4)) (hiQ.const_mul (1/2)),
    integral_const_mul, integral_const_mul, integral_const_mul] at hID
  have hground : (∫ X, ‖EuclideanGradient ψ X‖^2) +
      (∫ X, ‖EuclideanGradient W X + EuclideanGradient U X‖^2 * (ψ X)^2) / 4 +
      (∫ X, -EuclideanLaplacian U X * (ψ X)^2) / 2 =
      (∫ X, ‖EuclideanGradient f X‖^2 * Real.exp (-Htot X)) +
      (∫ X, EuclideanLaplacian W X * (ψ X)^2) / 2 := by linarith
  have hpower (w : Fin N → OneParticle d) :
      (∑ i, ‖w i‖^θ) ≤ P * (∑ i, ‖w i‖^2)^(θ/2) := by
    let p := 2/θ
    let q := θ/2
    have hp : 1 ≤ p := by dsimp [p]; apply (le_div_iff₀ hθ).2; linarith
    have hq : 0 ≤ q := by dsimp [q]; positivity
    have htp : θ*p = 2 := by dsimp [p]; field_simp
    have hpq : p*q = 1 := by dsimp [p,q]; field_simp
    have hNexp : (p-1)*q = 1-θ/2 := by dsimp [p,q]; field_simp
    have hi (i : Fin N) : (‖w i‖^θ)^p = ‖w i‖^2 := by
      rw [← Real.rpow_mul (norm_nonneg _), htp, Real.rpow_two]
    have hb := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg Finset.univ
      (f := fun i : Fin N => ‖w i‖^θ) hp (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
    simp only [Finset.card_univ, Fintype.card_fin, hi] at hb
    have hh := Real.rpow_le_rpow
      (Real.rpow_nonneg (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)) _) hb hq
    rw [← Real.rpow_mul (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)), hpq,
      Real.rpow_one, Real.mul_rpow (Real.rpow_nonneg (Nat.cast_nonneg N) _)
        (Finset.sum_nonneg (fun i _ => sq_nonneg _)),
      ← Real.rpow_mul (Nat.cast_nonneg N), hNexp] at hh
    exact hh
  have hpsum (X : ParticleConfig d N) :
      (∑ i : Fin N, ‖EuclideanGradient V (ParticlePosition X i)‖^θ) ≤ P * ‖EuclideanGradient W X‖^θ := by
    have hh := hpower (fun i : Fin N => EuclideanGradient V (ParticlePosition X i))
    rw [← (hprod X).1, ← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _)] at hh
    have hexp : 2 * (θ/2) = θ := by ring
    rw [hexp] at hh
    exact hh
  have hGrowth : ∀ X : ParticleConfig d N,
      EuclideanLaplacian W X ≤ a₀ * ‖EuclideanGradient W X‖^θ + CaN a₀ := by
    intro X
    let b := a₀/P
    have hb : 0 < b := div_pos ha₀ hP
    rw [(hprod X).2]
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hgrowth b hb (ParticlePosition X i))
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hsum
    have hp := mul_le_mul_of_nonneg_left (hpsum X) hb.le
    have hbP : b * P = a₀ := by dsimp [b]; field_simp
    have heq : b * (P * ‖EuclideanGradient W X‖^θ) = a₀ * ‖EuclideanGradient W X‖^θ := by
      rw [← mul_assoc, hbP]
    rw [heq] at hp
    exact hsum.trans (add_le_add hp (le_refl _))
  have Habs := UniformTraceAbsorption volume ψ (EuclideanLaplacian W)
    (EuclideanGradient W) (EuclideanGradient U) θ H (∫ X, ‖EuclideanGradient ψ X‖^2)
    (∫ X, -EuclideanLaplacian U X * (ψ X)^2)
    (∫ X, ‖EuclideanGradient f X‖^2 * Real.exp (-Htot X)) (CaN a₀)
    hθ hθ2 hH (integral_nonneg (fun X => sq_nonneg _)) himass hiQ hiT hiF hform hground hGrowth
  have hMC : ((CaN a₀ + a₀*c)/2) * (∫ X, (ψ X)^2) ≤ C * (∫ X, (ψ X)^2) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (integral_nonneg (fun X => sq_nonneg _))
  dsimp only [a₀, c, W, U, Htot, ψ] at Habs hMC ⊢
  linarith
