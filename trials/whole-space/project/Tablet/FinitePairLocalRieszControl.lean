import Tablet.RelativePairCoordinates
import Tablet.AtomicLocalRieszBounds
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

set_option autoImplicit false
set_option maxHeartbeats 1600000
open MeasureTheory Set Metric
open scoped ContDiff Pointwise
noncomputable section

-- [TABLET NODE: FinitePairLocalRieszControl]
theorem FinitePairLocalRieszControl (d : ℕ) (hd : 3 ≤ d) (s : ℝ)
    (hs : 0 < s) (hsd : s ≤ (d : ℝ) - 2) (R : ℝ) (hR : 0 < R) :
    ∃ P F S : ℝ, 0 ≤ P ∧ 0 ≤ F ∧ 0 ≤ S ∧
      ∀ (N : ℕ) (i j : Fin N), i ≠ j → ∀ ε : ℝ, 0 < ε →
        let K := closedBall (0 : ParticleConfig d N) R
        let Bs := closedBall (0 : EuclideanSpace ℝ {p : Fin N × Fin d // p.1 ≠ i}) R
        let r := fun X : ParticleConfig d N => ParticlePosition X i - ParticlePosition X j
        IntegrableOn (fun X => RieszKernel s ε (r X)) K ∧
        IntegrableOn (fun X => Real.sqrt 2 * ‖EuclideanGradient (RieszKernel s ε) (r X)‖) K ∧
        IntegrableOn (fun X => 2 * (-EuclideanLaplacian (RieszKernel s ε) (r X))) K ∧
        (∫ X in K, RieszKernel s ε (r X)) ≤ P * volume.real Bs ∧
        (∫ X in K, Real.sqrt 2 * ‖EuclideanGradient (RieszKernel s ε) (r X)‖) ≤ F * volume.real Bs ∧
        (∫ X in K, 2 * (-EuclideanLaplacian (RieszKernel s ε) (r X))) ≤ S * volume.real Bs := by
-- BODY
  let B := closedBall (0 : OneParticle d) R
  let A := Real.sqrt 2 • B
  have hAc : IsCompact A := (isCompact_closedBall _ _).image (continuous_const_smul (Real.sqrt 2))
  obtain ⟨P₀, F₀, S₀, hP₀, hF₀, hS₀, hlocal⟩ :=
    AtomicLocalRieszBounds d hd s hs hsd A hAc.measurableSet hAc.measure_ne_top
  let c := (Real.sqrt 2 ^ d)⁻¹
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨c*P₀, Real.sqrt 2*c*F₀, 2*c*S₀, by positivity, by positivity, by positivity, ?_⟩
  intro N i j hij ε hε
  dsimp only
  let Z := EuclideanSpace ℝ {p : Fin N × Fin d // p.1 ≠ i}
  let K := closedBall (0 : ParticleConfig d N) R
  let Bs := closedBall (0 : Z) R
  let r := fun X : ParticleConfig d N => ParticlePosition X i - ParticlePosition X j
  obtain ⟨e, he, hmp, _⟩ := RelativePairCoordinates (d := d) i j hij
  let em : ParticleConfig d N ≃ᵐ (OneParticle d × Z) :=
    e.toMeasurableEquiv.trans (MeasurableEquiv.toLp 2 _).symm
  have hem : MeasurePreserving em volume volume := hmp
  have hr (X : ParticleConfig d N) : r X = Real.sqrt 2 • (em X).1 := by
    ext k
    change X (i,k) - X (j,k) = Real.sqrt 2 * (WithLp.ofLp (e X)).1 k
    rw [he]
    have hn : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
  have hrc : Continuous r := by
    change Continuous (fun X : ParticleConfig d N =>
      WithLp.toLp 2 (fun k => X (i,k)) - WithLp.toLp 2 (fun k => X (j,k)))
    fun_prop
  have hfiber (f : OneParticle d → ℝ) (hf : Continuous f) (hn : ∀ z, 0 ≤ f z)
      (C : ℝ) (hb : (∫ z in A, f z) ≤ C) :
      IntegrableOn (fun X => f (r X)) K ∧
      (∫ X in K, f (r X)) ≤ (c*C)*volume.real Bs := by
    let T := em ⁻¹' (B ×ˢ Bs)
    have hsub : K ⊆ T := by
      intro X hX
      have hnorm : ‖X‖ ≤ R := by simpa [K] using hX
      have hu := (WithLp.norm_fst_le _ (e X)).trans_eq (e.norm_map X)
      have hz := (WithLp.norm_snd_le _ (e X)).trans_eq (e.norm_map X)
      exact ⟨by simpa [B, em] using hu.trans hnorm, by simpa [Bs, em] using hz.trans hnorm⟩
    have hTc : IsCompact T := by
      let eh := e.toHomeomorph.trans (WithLp.homeomorphProd 2 (OneParticle d) Z)
      change IsCompact (eh ⁻¹' (B ×ˢ Bs))
      exact eh.isCompact_preimage.mpr ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
    have hi : IntegrableOn (fun X => f (r X)) T :=
      (hf.comp hrc).continuousOn.integrableOn_compact hTc
    have hsplit : (∫ X in T, f (r X)) =
        (∫ u in B, f (Real.sqrt 2 • u))*volume.real Bs := by
      have hh := hem.setIntegral_preimage_emb em.measurableEmbedding
        (fun q : OneParticle d × Z => f (Real.sqrt 2 • q.1)) (B ×ˢ Bs)
      have hh' : (fun X => f (Real.sqrt 2 • (em X).1)) = fun X => f (r X) := by
        funext X
        rw [hr]
      rw [hh'] at hh
      rw [hh]
      have hp := setIntegral_prod_mul (μ := volume) (ν := volume)
        (fun u : OneParticle d => f (Real.sqrt 2 • u)) (fun _ : Z => (1 : ℝ)) B Bs
      rw [Measure.volume_eq_prod]
      simpa only [mul_one, setIntegral_const, smul_eq_mul] using hp
    have hscaled : (∫ u in B, f (Real.sqrt 2 • u)) ≤ c*C := by
      rw [Measure.setIntegral_comp_smul_of_pos volume f B (by positivity : 0 < Real.sqrt 2)]
      simp only [OneParticle, finrank_euclideanSpace_fin, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left hb hc
    refine ⟨(hf.comp hrc).continuousOn.integrableOn_compact (isCompact_closedBall _ _), ?_⟩
    calc
      _ ≤ ∫ X in T, f (r X) := setIntegral_mono_set hi
        (Filter.Eventually.of_forall (fun X => hn _)) (Filter.Eventually.of_forall hsub)
      _ = _ := hsplit
      _ ≤ _ := mul_le_mul_of_nonneg_right hscaled measureReal_nonneg
  let J : Finset Unit := {()}
  have hrow := hlocal J (fun _ => (1 : ℝ)) (fun _ => (0 : OneParticle d)) ε 1 hε
    (by norm_num) (by intro x hx; norm_num) (by simp [J])
  have hsingle : (fun z : OneParticle d => ∑ q ∈ J, (1 : ℝ) * RieszKernel s ε (z - 0)) =
      RieszKernel s ε := by
    funext z
    simp [J]
  dsimp only at hrow
  rw [hsingle] at hrow
  simp only [one_mul] at hrow
  have hsrc := AtomicInteractionSource d s ε hs hsd hε J
    (fun _ => (1 : ℝ)) (fun _ => (0 : OneParticle d)) (by intro q hq; norm_num)
  dsimp only at hsrc
  rw [hsingle] at hsrc
  have hk : ContDiff ℝ 2 (RieszKernel s ε : OneParticle d → ℝ) := hsrc.1
  have hgc : Continuous (fun z : OneParticle d => ‖EuclideanGradient (RieszKernel s ε) z‖) := by
    change Continuous (fun z : OneParticle d => ‖gradient (RieszKernel s ε) z‖)
    exact ((InnerProductSpace.toDual ℝ (OneParticle d)).symm.continuous.comp
      (hk.continuous_fderiv (by norm_num))).norm
  let σ := fun z : OneParticle d =>
    (((d : ℝ)-s-2)*‖z‖^2 + (d : ℝ)*ε^2) * (‖z‖^2+ε^2)^(-s/2-2)
  have hσ (z : OneParticle d) : -EuclideanLaplacian (RieszKernel s ε) z = σ z := by
    simpa [J, σ] using (hsrc.2 z).1
  have hσc : Continuous σ := by
    dsimp [σ]
    apply Continuous.mul
    · fun_prop
    · exact ((continuous_norm.pow 2).add continuous_const).rpow_const
        (fun z => Or.inl (show ‖z‖^2+ε^2 ≠ 0 by positivity))
  have hsc : Continuous (fun z : OneParticle d => -EuclideanLaplacian (RieszKernel s ε) z) := by
    simpa only [hσ] using hσc
  have hsn (z : OneParticle d) : 0 ≤ -EuclideanLaplacian (RieszKernel s ε) z := (hsrc.2 z).2
  have hp := hfiber (RieszKernel s ε) hk.continuous
    ((RieszKernelBounds s ε hs hε.le).1) P₀ hrow.2.2.2.1
  have hg := hfiber (fun z => ‖EuclideanGradient (RieszKernel s ε) z‖) hgc
    (fun z => norm_nonneg _) F₀ hrow.2.2.2.2.1
  have hS := hfiber (fun z => -EuclideanLaplacian (RieszKernel s ε) z) hsc hsn S₀ hrow.2.2.2.2.2
  refine ⟨hp.1, hg.1.const_mul (Real.sqrt 2), hS.1.const_mul 2, hp.2, ?_, ?_⟩
  · rw [integral_const_mul]
    calc
      _ ≤ Real.sqrt 2 * ((c*F₀)*volume.real Bs) :=
        mul_le_mul_of_nonneg_left hg.2 (Real.sqrt_nonneg _)
      _ = _ := by ring
  · rw [integral_const_mul]
    calc
      _ ≤ 2 * ((c*S₀)*volume.real Bs) := mul_le_mul_of_nonneg_left hS.2 (by norm_num)
      _ = _ := by ring
