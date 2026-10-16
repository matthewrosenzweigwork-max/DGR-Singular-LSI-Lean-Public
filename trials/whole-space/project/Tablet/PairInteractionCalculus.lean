module

public import Tablet.PairInteraction
public import Tablet.RelativePairCoordinates
public import Tablet.GradientNormIdentity
public import Tablet.ForceExponent
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open MeasureTheory
open scoped ContDiff

-- [TABLET NODE: PairInteractionCalculus]
theorem PairInteractionCalculus (d N : ℕ) (s B : ℝ) (hs : 0 < s) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ coupling ε : ℝ, 0 ≤ coupling → coupling ≤ B → 0 < ε →
      ContDiff ℝ ∞ (PairInteraction (d := d) (N := N) s coupling ε) ∧
      ∀ X : ParticleConfig d N,
        ‖EuclideanGradient (PairInteraction s coupling ε) X‖ ^ (ForceExponent s) ≤
          K * ∑ i : Fin N, ∑ j : Fin N,
            if i < j then 1 / ‖ParticlePosition X i - ParticlePosition X j‖ ^ 2 else 0 := by
-- BODY
  classical
  let θ := ForceExponent s
  have hθ : 0 < θ := by dsimp [θ, ForceExponent]; positivity
  let I := Fin N × Fin N
  let M : ℝ := (Fintype.card I : ℝ) ^ (max (θ - 1) 0)
  let K := (B / (N : ℝ)) ^ θ * M * (Real.sqrt 2) ^ θ
  have hK : 0 ≤ K := by dsimp [K, M]; positivity
  refine ⟨K, hK, ?_⟩
  intro coupling ε ha haB hε
  let k : OneParticle d → ℝ := RieszKernel s ε
  let F : OneParticle d → OneParticle d := fun z =>
    -((‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1) • z)
  have hk : ContDiff ℝ ∞ k := by
    dsimp only [k]
    unfold RieszKernel
    simp only [if_neg hε.ne']
    exact (((contDiff_norm_sq ℝ).add contDiff_const).rpow_const_of_ne
      (fun z => ne_of_gt (by positivity : 0 < ‖z‖ ^ 2 + ε ^ 2))).div_const s
  have hkder (z : OneParticle d) : HasFDerivAt k (innerSL ℝ (F z)) z := by
    have hbase : 0 < ‖z‖ ^ 2 + ε ^ 2 := by positivity
    have hder := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.add_const (ε ^ 2)).rpow_const
      (p := -s / 2) (Or.inl hbase.ne')
    have hscaled := hder.const_smul s⁻¹
    have heq : s⁻¹ • ((-s / 2 * (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1)) •
        (2 • innerSL ℝ z)) = innerSL ℝ (F z) := by
      ext h
      simp only [smul_apply, smul_eq_mul, nsmul_eq_mul, innerSL_apply_apply,
        F, inner_neg_left, real_inner_smul_left]
      field_simp
      ring
    rw [heq] at hscaled
    have hfun : (s⁻¹ • fun z : OneParticle d => (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2)) = k := by
      funext z
      simp [k, RieszKernel, hε.ne', Pi.smul_apply, div_eq_mul_inv, mul_comm]
    rw [hfun] at hscaled
    exact hscaled
  have hFnorm (z : OneParticle d) : ‖F z‖ ≤ ‖z‖ ^ (-(s + 1)) := by
    by_cases hz : z = 0
    · subst z
      simp only [F, norm_zero, smul_zero, neg_zero]
      exact Real.rpow_nonneg (by rfl) _
    · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
      have hn2 : 0 < ‖z‖ ^ 2 := by positivity
      have he : -s / 2 - 1 ≤ 0 := by linarith
      have hp := Real.rpow_le_rpow_of_nonpos hn2
        (by nlinarith [sq_nonneg ε] : ‖z‖ ^ 2 ≤ ‖z‖ ^ 2 + ε ^ 2) he
      have hb : 0 ≤ ‖z‖ ^ 2 + ε ^ 2 := by positivity
      dsimp [F]
      rw [norm_neg, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hb _)]
      calc
        (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1) * ‖z‖ ≤
            (‖z‖ ^ 2) ^ (-s / 2 - 1) * ‖z‖ := mul_le_mul_of_nonneg_right hp hn.le
        _ = ‖z‖ ^ (-(s + 1)) := by
          rw [← Real.rpow_two, ← Real.rpow_mul hn.le]
          have heq := Real.rpow_add hn (2 * (-s / 2 - 1)) 1
          simp only [Real.rpow_one] at heq
          rw [← heq]
          congr 1
          ring
  have hpairs (i j : Fin N) (hij : i ≠ j) :
      ContDiff ℝ ∞ (fun X : ParticleConfig d N => k (ParticlePosition X i - ParticlePosition X j)) ∧
      ∀ X, ‖fderiv ℝ (fun Y : ParticleConfig d N =>
        k (ParticlePosition Y i - ParticlePosition Y j)) X‖ ^ θ ≤
        (Real.sqrt 2) ^ θ / ‖ParticlePosition X i - ParticlePosition X j‖ ^ 2 := by
    obtain ⟨e, he, _, _⟩ := RelativePairCoordinates (d := d) i j hij
    let L : ParticleConfig d N →L[ℝ] OneParticle d :=
      Real.sqrt 2 • ((WithLp.fstL 2 ℝ (OneParticle d)
        (EuclideanSpace ℝ {p : Fin N × Fin d // p.1 ≠ i})).comp
          e.toContinuousLinearEquiv.toContinuousLinearMap)
    have hL (X : ParticleConfig d N) : L X = ParticlePosition X i - ParticlePosition X j := by
      ext l
      change Real.sqrt 2 * (WithLp.ofLp (e X)).1 l = X (i, l) - X (j, l)
      rw [he]
      have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
      field_simp
    have hLn : ‖L‖ ≤ Real.sqrt 2 := by
      apply L.opNorm_le_bound (Real.sqrt_nonneg 2)
      intro X
      change ‖Real.sqrt 2 • (WithLp.ofLp (e X)).1‖ ≤ Real.sqrt 2 * ‖X‖
      rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg 2)]
      calc
        _ ≤ Real.sqrt 2 * ‖e X‖ :=
          mul_le_mul_of_nonneg_left (WithLp.norm_fst_le (α := OneParticle d) (β := EuclideanSpace ℝ {p : Fin N × Fin d // p.1 ≠ i}) (e X)) (Real.sqrt_nonneg 2)
        _ = _ := by rw [e.norm_map]
    have hfun : (fun X : ParticleConfig d N => k (ParticlePosition X i - ParticlePosition X j)) = k ∘ L := by
      funext X
      simp only [Function.comp_apply, hL]
    rw [hfun]
    refine ⟨hk.comp L.contDiff, ?_⟩
    intro X
    have hd := (hkder (L X)).comp X L.hasFDerivAt
    have hn : ‖fderiv ℝ (k ∘ L) X‖ ≤ Real.sqrt 2 * ‖ParticlePosition X i - ParticlePosition X j‖ ^ (-(s + 1)) := by
      rw [hd.fderiv]
      calc
        _ ≤ ‖innerSL ℝ (F (L X))‖ * ‖L‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖F (L X)‖ * Real.sqrt 2 := by
          rw [innerSL_apply_norm]
          exact mul_le_mul_of_nonneg_left hLn (norm_nonneg _)
        _ ≤ ‖L X‖ ^ (-(s + 1)) * Real.sqrt 2 :=
          mul_le_mul_of_nonneg_right (hFnorm _) (Real.sqrt_nonneg 2)
        _ = _ := by rw [hL]; ring
    have hp := Real.rpow_le_rpow (norm_nonneg _) hn hθ.le
    rw [Real.mul_rpow (Real.sqrt_nonneg 2) (Real.rpow_nonneg (norm_nonneg _) _),
      ← Real.rpow_mul (norm_nonneg _)] at hp
    have hexp : -(s + 1) * θ = (-2 : ℝ) := by
      dsimp [θ, ForceExponent]
      have hsp : s + 1 ≠ 0 := by positivity
      field_simp
    rw [hexp, Real.rpow_neg (norm_nonneg _), Real.rpow_two] at hp
    simpa only [div_eq_mul_inv] using hp
  let U : I → ParticleConfig d N → ℝ := fun p X =>
    if p.1 < p.2 then k (ParticlePosition X p.1 - ParticlePosition X p.2) else 0
  have hU (p : I) : ContDiff ℝ ∞ (U p) := by
    by_cases hp : p.1 < p.2
    · simpa only [U, if_pos hp] using (hpairs p.1 p.2 (ne_of_lt hp)).1
    · simpa only [U, if_neg hp] using (contDiff_const : ContDiff ℝ ∞ (fun _ : ParticleConfig d N => (0 : ℝ)))
  have hactual : PairInteraction (d := d) (N := N) s coupling ε =
      fun X => (coupling / (N : ℝ)) • ∑ p : I, U p X := by
    funext X
    simp only [PairInteraction, Fintype.sum_prod_type, U, I, k, smul_eq_mul]
  have hsum : ContDiff ℝ ∞ (fun X => ∑ p : I, U p X) :=
    ContDiff.sum (fun p _ => hU p)
  constructor
  · rw [hactual]
    exact hsum.const_smul (coupling / (N : ℝ))
  · intro X
    have hsubadd (J : Finset I) (a : I → ℝ) (ha : ∀ p, 0 ≤ a p) (ht : θ ≤ 1) :
        (∑ p ∈ J, a p)^θ ≤ ∑ p ∈ J, (a p)^θ := by
      induction J using Finset.induction_on with
      | empty => simp [Real.zero_rpow hθ.ne']
      | @insert p J hp ih =>
        rw [Finset.sum_insert hp, Finset.sum_insert hp]
        exact (Real.rpow_add_le_add_rpow (ha p) (Finset.sum_nonneg (fun p _ => ha p)) hθ.le ht).trans
          (add_le_add (le_refl _) ih)
    let D : I → (ParticleConfig d N →L[ℝ] ℝ) := fun p => fderiv ℝ (U p) X
    have hsumD : ‖∑ p : I, D p‖ ^ θ ≤ M * ∑ p : I, ‖D p‖ ^ θ := by
      have hn := Real.rpow_le_rpow (norm_nonneg _)
        (norm_sum_le (Finset.univ : Finset I) D) hθ.le
      apply hn.trans
      by_cases hh : 1 ≤ θ
      · have hb := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
          (Finset.univ : Finset I) (f := fun p => ‖D p‖) hh (fun p _ => norm_nonneg _)
        simpa only [M, Finset.card_univ, max_eq_left (by linarith : 0 ≤ θ - 1)] using hb
      · have ht : θ ≤ 1 := by linarith
        simpa only [M, max_eq_right (by linarith : θ - 1 ≤ 0), Real.rpow_zero, one_mul] using
          hsubadd Finset.univ (fun p => ‖D p‖) (fun p => norm_nonneg _) ht
    have hDp (p : I) : ‖D p‖ ^ θ ≤ (Real.sqrt 2) ^ θ *
        (if p.1 < p.2 then 1 / ‖ParticlePosition X p.1 - ParticlePosition X p.2‖ ^ 2 else 0) := by
      by_cases hp : p.1 < p.2
      · simpa only [D, U, if_pos hp, div_eq_mul_inv, one_mul] using
          (hpairs p.1 p.2 (ne_of_lt hp)).2 X
      · simp [D, U, hp, Real.zero_rpow hθ.ne']
    have hbound : (∑ p : I, ‖D p‖ ^ θ) ≤ (Real.sqrt 2) ^ θ *
        ∑ i : Fin N, ∑ j : Fin N,
          if i < j then 1 / ‖ParticlePosition X i - ParticlePosition X j‖ ^ 2 else 0 := by
      calc
        _ ≤ ∑ p : I, (Real.sqrt 2) ^ θ *
            (if p.1 < p.2 then 1 / ‖ParticlePosition X p.1 - ParticlePosition X p.2‖ ^ 2 else 0) :=
          Finset.sum_le_sum (fun p _ => hDp p)
        _ = _ := by rw [← Finset.mul_sum]; simp only [Fintype.sum_prod_type, I]
    have hder := (HasFDerivAt.fun_sum (fun p (_ : p ∈ (Finset.univ : Finset I)) =>
      (hU p).differentiable (by simp) X |>.hasFDerivAt)).const_smul (coupling / (N : ℝ))
    have hdf : fderiv ℝ (PairInteraction (d := d) (N := N) s coupling ε) X =
        (coupling / (N : ℝ)) • ∑ p : I, D p := by
      rw [hactual]
      exact hder.fderiv
    rw [(GradientNormIdentity _ X).2, hdf, norm_smul,
      Real.norm_of_nonneg (div_nonneg ha (Nat.cast_nonneg N)),
      Real.mul_rpow (div_nonneg ha (Nat.cast_nonneg N)) (norm_nonneg _)]
    have hc : (coupling / (N : ℝ)) ^ θ ≤ (B / (N : ℝ)) ^ θ :=
      Real.rpow_le_rpow (div_nonneg ha (Nat.cast_nonneg N))
        (div_le_div_of_nonneg_right haB (Nat.cast_nonneg N)) hθ.le
    calc
      _ ≤ (coupling / (N : ℝ)) ^ θ * (M * ∑ p : I, ‖D p‖ ^ θ) :=
        mul_le_mul_of_nonneg_left hsumD (Real.rpow_nonneg (by positivity) _)
      _ ≤ (B / (N : ℝ)) ^ θ * (M * ((Real.sqrt 2) ^ θ *
          ∑ i : Fin N, ∑ j : Fin N,
            if i < j then 1 / ‖ParticlePosition X i - ParticlePosition X j‖ ^ 2 else 0)) := by
        apply mul_le_mul
        · exact hc
        · exact mul_le_mul_of_nonneg_left hbound (by dsimp [M]; positivity)
        · positivity
        · positivity
      _ = _ := by dsimp [K]; ring
