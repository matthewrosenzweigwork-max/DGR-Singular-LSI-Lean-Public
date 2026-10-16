module

public import Tablet.PairInteractionCalculus
public import Tablet.PairRelativeLaplacian
public import Tablet.AtomicInteractionSource
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped ContDiff

-- [TABLET NODE: PairInteractionSource]
theorem PairInteractionSource (d N : ℕ) (s coupling ε : ℝ)
    (hs : 0 < s) (hsd : s ≤ (d : ℝ) - 2) (ha : 0 ≤ coupling) (hε : 0 < ε) :
    ContDiff ℝ ∞ (PairInteraction (d := d) (N := N) s coupling ε) ∧
    ∀ X : ParticleConfig d N,
      -EuclideanLaplacian (PairInteraction s coupling ε) X =
        (2 * coupling / (N : ℝ)) * (∑ i : Fin N, ∑ j : Fin N,
          if i < j then
            (((d : ℝ) - s - 2) * ‖ParticlePosition X i - ParticlePosition X j‖ ^ 2 +
              (d : ℝ) * ε ^ 2) *
              (‖ParticlePosition X i - ParticlePosition X j‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 2)
          else 0) ∧
      0 ≤ -EuclideanLaplacian (PairInteraction s coupling ε) X := by
-- BODY
  classical
  obtain ⟨_, _, hall⟩ := PairInteractionCalculus d N s coupling hs ha
  have hactual := (hall coupling ε ha le_rfl hε).1
  refine ⟨hactual, ?_⟩
  let k : OneParticle d → ℝ := RieszKernel s ε
  have hk : ContDiff ℝ ∞ k := by
    dsimp only [k]
    unfold RieszKernel
    simp only [if_neg hε.ne']
    exact (((contDiff_norm_sq ℝ).add contDiff_const).rpow_const_of_ne
      (fun z => ne_of_gt (by positivity : 0 < ‖z‖ ^ 2 + ε ^ 2))).div_const s
  have hk2 : ContDiff ℝ 2 k := hk.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hrow := AtomicInteractionSource d s ε hs hsd hε
    ({()} : Finset Unit) (fun _ : Unit => (1 : ℝ)) (fun _ => (0 : OneParticle d))
    (by intro _ _; norm_num)
  simp only [Finset.sum_singleton, one_mul, sub_zero] at hrow
  let S : OneParticle d → ℝ := fun z =>
    (((d : ℝ) - s - 2) * ‖z‖ ^ 2 + (d : ℝ) * ε ^ 2) *
      (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 2)
  have hsrow (z : OneParticle d) : -EuclideanLaplacian k z = S z ∧ 0 ≤ S z := by
    have hh := hrow.2 z
    exact ⟨hh.1, by dsimp only [k, S]; rw [← hh.1]; exact hh.2⟩
  let I := Fin N × Fin N
  let U : I → ParticleConfig d N → ℝ := fun p X =>
    if p.1 < p.2 then k (ParticlePosition X p.1 - ParticlePosition X p.2) else 0
  have hU (p : I) : ContDiff ℝ 2 (U p) := by
    by_cases hp : p.1 < p.2
    · obtain ⟨e, he, _, _⟩ := RelativePairCoordinates (d := d) p.1 p.2 (ne_of_lt hp)
      let L : ParticleConfig d N →L[ℝ] OneParticle d :=
        Real.sqrt 2 • ((WithLp.fstL 2 ℝ (OneParticle d)
          (EuclideanSpace ℝ {q : Fin N × Fin d // q.1 ≠ p.1})).comp
            e.toContinuousLinearEquiv.toContinuousLinearMap)
      have hL (X : ParticleConfig d N) : L X = ParticlePosition X p.1 - ParticlePosition X p.2 := by
        ext l
        change Real.sqrt 2 * (WithLp.ofLp (e X)).1 l = X (p.1, l) - X (p.2, l)
        rw [he]
        have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
        field_simp
      have hfun : U p = k ∘ L := by funext X; simp only [U, if_pos hp, Function.comp_apply, hL]
      rw [hfun]
      exact hk2.comp L.contDiff
    · simpa only [U, if_neg hp] using (contDiff_const : ContDiff ℝ 2 (fun _ : ParticleConfig d N => (0 : ℝ)))
  have hsumLap (J : Finset I) (X : ParticleConfig d N) :
      EuclideanLaplacian (fun Y => ∑ p ∈ J, U p Y) X = ∑ p ∈ J, EuclideanLaplacian (U p) X := by
    induction J using Finset.induction_on with
    | empty => simp [EuclideanLaplacian, InnerProductSpace.laplacian_const]
    | @insert p J hp ih =>
      have hf : ContDiff ℝ 2 (fun Y => ∑ q ∈ J, U q Y) := ContDiff.sum (fun q _ => hU q)
      simp only [Finset.sum_insert hp]
      change EuclideanLaplacian (U p + fun Y => ∑ q ∈ J, U q Y) X = _
      rw [EuclideanLaplacian, (hU p).contDiffAt.laplacian_add hf.contDiffAt]
      change EuclideanLaplacian (U p) X + EuclideanLaplacian (fun Y => ∑ q ∈ J, U q Y) X = _
      rw [ih]
  intro X
  have hterm (p : I) : -EuclideanLaplacian (U p) X =
      2 * (if p.1 < p.2 then S (ParticlePosition X p.1 - ParticlePosition X p.2) else 0) := by
    by_cases hp : p.1 < p.2
    · simp only [U, if_pos hp]
      rw [PairRelativeLaplacian p.1 p.2 (ne_of_lt hp) k hk2 X]
      have hh := (hsrow (ParticlePosition X p.1 - ParticlePosition X p.2)).1
      linarith
    · simp [U, hp, EuclideanLaplacian, InnerProductSpace.laplacian_const]
  have heq : PairInteraction (d := d) (N := N) s coupling ε =
      (coupling / (N : ℝ)) • (fun Y => ∑ p : I, U p Y) := by
    funext Y
    simp only [PairInteraction, Pi.smul_apply, smul_eq_mul, Fintype.sum_prod_type, U, I, k]
  have hsum : ContDiff ℝ 2 (fun Y => ∑ p : I, U p Y) := ContDiff.sum (fun p _ => hU p)
  have hcalc : -EuclideanLaplacian (PairInteraction s coupling ε) X =
      (2 * coupling / (N : ℝ)) * ∑ i : Fin N, ∑ j : Fin N,
        if i < j then S (ParticlePosition X i - ParticlePosition X j) else 0 := by
    rw [heq, EuclideanLaplacian, InnerProductSpace.laplacian_smul _ hsum.contDiffAt]
    change -(coupling / (N : ℝ) * EuclideanLaplacian (fun Y => ∑ p : I, U p Y) X) = _
    rw [hsumLap Finset.univ X]
    have hh : -(∑ p : I, EuclideanLaplacian (U p) X) =
        2 * ∑ p : I, if p.1 < p.2 then S (ParticlePosition X p.1 - ParticlePosition X p.2) else 0 := by
      rw [← Finset.sum_neg_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun p _ => hterm p)
    rw [neg_mul_eq_mul_neg, hh]
    simp only [Fintype.sum_prod_type, I]
    ring
  refine ⟨hcalc, ?_⟩
  rw [hcalc]
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact (hsrow _).2
  · exact le_rfl
