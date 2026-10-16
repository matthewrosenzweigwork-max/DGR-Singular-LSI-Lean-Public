import Tablet.NativeGibbsReplacementBalance
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
open MeasureTheory Filter Set
open scoped ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

-- [TABLET NODE: NativeGibbsTransformedL2]
theorem NativeGibbsTransformedL2 (d N : ℕ) (μ : Measure (OneParticle d))
    [IsProbabilityMeasure μ] (s coupling ε : ℝ) (hs : 0 < s)
    (hc : 0 ≤ coupling) (hε : 0 < ε) :
    let P := GibbsLaw (N:=N) μ s coupling ε
    let U := fun (X : ParticleConfig d N) (i : Fin N) (z : OneParticle d) =>
      ∑ j ∈ Finset.univ.erase i, (coupling/(N:ℝ))*RieszKernel s ε (z-ParticlePosition X j)
    let J := fun i => (P.prod μ).withDensity
      (fun q => ENNReal.ofReal (Real.exp (-U q.1 i q.2)))
    ∀ (f : ParticleConfig d N → ℝ), MemLp f 2 P →
      let δ := fun i (q : ParticleConfig d N × OneParticle d) =>
        f (ParticleInsertion q.1 i q.2)-f q.1
      let F := fun i (q : ParticleConfig d N × OneParticle d) =>
        Real.exp (-U q.1 i q.2)*δ i q
      (∀ i, MemLp (F i) 2 (P.prod μ) ∧
        (∫ X, ∫ z, (F i (X,z))^2 ∂μ ∂P) ≤ ∫ q, (δ i q)^2 ∂J i) ∧
      (∀ᵐ X ∂P, ∀ i, MemLp (fun z => F i (X,z)) 2 μ) ∧
      ∀ i j,
        Integrable (fun q : (ParticleConfig d N × OneParticle d) × OneParticle d =>
          Real.exp (-(coupling/(N:ℝ))*RieszKernel s ε (q.1.2-q.2))*
            F i q.1*F j (q.1.1,q.2)) ((P.prod μ).prod μ) ∧
        Integrable (fun q : (ParticleConfig d N × OneParticle d) × OneParticle d =>
          (1-Real.exp (-(coupling/(N:ℝ))*RieszKernel s ε (q.1.2-q.2)))*
            F i q.1*F j (q.1.1,q.2)) ((P.prod μ).prod μ) := by
-- BODY
  classical
  dsimp only
  let P := GibbsLaw (N:=N) μ s coupling ε
  let U := fun (X : ParticleConfig d N) (i : Fin N) (z : OneParticle d) =>
    ∑ j ∈ Finset.univ.erase i, (coupling/(N:ℝ))*RieszKernel s ε (z-ParticlePosition X j)
  let r := fun i (q : ParticleConfig d N × OneParticle d) => Real.exp (-U q.1 i q.2)
  let J := fun i => (P.prod μ).withDensity (fun q => ENNReal.ofReal (r i q))
  letI : IsProbabilityMeasure P := (SoftGibbsNormalization (N:=N) μ s coupling ε hs hc hε).2.2
  have hrm (i : Fin N) : Measurable (r i) := by
    have hU : Measurable (fun q : ParticleConfig d N × OneParticle d => U q.1 i q.2) := by
      apply Finset.measurable_sum
      intro j hj
      dsimp only [RieszKernel]
      simp only [ne_of_gt hε, if_false]
      unfold ParticlePosition
      fun_prop
    exact hU.neg.exp
  have hr (i : Fin N) (q : ParticleConfig d N × OneParticle d) : 0 ≤ r i q ∧ r i q ≤ 1 := by
    refine ⟨Real.exp_nonneg _, Real.exp_le_one_iff.mpr ?_⟩
    apply neg_nonpos.mpr
    exact Finset.sum_nonneg fun j hj => mul_nonneg (div_nonneg hc (Nat.cast_nonneg _))
      ((RieszKernelBounds s ε hs hε.le).1 _)
  have hbJ (i : Fin N) := NativeGibbsReplacementBalance d N μ s coupling ε hs hc hε i
  have hins (i : Fin N) : Measurable (fun q : ParticleConfig d N × OneParticle d => ParticleInsertion q.1 i q.2) :=
    measurable_fst.comp (hbJ i).1.measurable
  intro f hf
  let δ := fun i (q : ParticleConfig d N × OneParticle d) => f (ParticleInsertion q.1 i q.2)-f q.1
  let F := fun i (q : ParticleConfig d N × OneParticle d) => r i q*δ i q
  have hmem (i : Fin N) : MemLp (F i) 2 (P.prod μ) ∧
      (∫ X, ∫ z, (F i (X,z))^2 ∂μ ∂P) ≤ ∫ q, (δ i q)^2 ∂J i := by
    have hJle : J i ≤ P.prod μ := by
      have hh := withDensity_mono (μ := P.prod μ) (Eventually.of_forall fun q =>
        ENNReal.ofReal_le_ofReal (hr i q).2)
      simpa only [ENNReal.ofReal_one, withDensity_const, one_smul] using hh
    letI : IsFiniteMeasure (J i) := isFiniteMeasure_of_le (P.prod μ) hJle
    have ho := (hf.mono_measure (hbJ i).2.1).comp_of_map measurable_fst.aemeasurable
    have hn := (hf.mono_measure (hbJ i).2.2).comp_of_map (hins i).aemeasurable
    have hd : MemLp (δ i) 2 (J i) := hn.sub ho
    have hm := (hrm i).ennreal_ofReal
    have hfin : ∀ᵐ q ∂P.prod μ, ENNReal.ofReal (r i q)<⊤ := Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
    have hi : Integrable (F i) (P.prod μ) := by
      have hh := (integrable_withDensity_iff_integrable_smul' hm hfin).mp (hd.integrable (by norm_num))
      simpa only [ENNReal.toReal_ofReal (hr i _).1, smul_eq_mul] using hh
    have hi2 : Integrable (fun q => r i q*(δ i q)^2) (P.prod μ) := by
      have hh := (integrable_withDensity_iff_integrable_smul' hm hfin).mp hd.integrable_sq
      simpa only [ENNReal.toReal_ofReal (hr i _).1, smul_eq_mul] using hh
    have hpoint (q) : (F i q)^2 ≤ r i q*(δ i q)^2 := by
      have hh := mul_le_mul_of_nonneg_right (hr i q).2 (mul_nonneg (hr i q).1 (sq_nonneg (δ i q)))
      dsimp [F]
      nlinarith only [hh]
    have hsq : Integrable (fun q => (F i q)^2) (P.prod μ) := hi2.mono' (hi.1.pow 2)
      (Eventually.of_forall fun q => by rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]; exact hpoint q)
    refine ⟨(memLp_two_iff_integrable_sq hi.1).mpr hsq, ?_⟩
    rw [← integral_prod _ hsq]
    calc
      _ ≤ ∫ q, r i q*(δ i q)^2 ∂P.prod μ := integral_mono hsq hi2 hpoint
      _ = ∫ q, (δ i q)^2 ∂J i := by
        rw [integral_withDensity_eq_integral_toReal_smul hm hfin]
        simp only [ENNReal.toReal_ofReal (hr i _).1,smul_eq_mul]
  refine ⟨hmem, ?_, ?_⟩
  · apply eventually_all.mpr
    intro i
    filter_upwards [(hmem i).1.1.prodMk_left, (hmem i).1.integrable_sq.prod_right_ae] with X hm hi
    exact (memLp_two_iff_integrable_sq hm).mpr hi
  · intro i j
    let Q := (P.prod μ).prod μ
    have hproj1 : MeasurePreserving (Prod.fst : (ParticleConfig d N × OneParticle d) × OneParticle d → ParticleConfig d N × OneParticle d) Q (P.prod μ) := measurePreserving_fst
    let A := fun q : (ParticleConfig d N × OneParticle d) × OneParticle d => ((q.1.1,q.2),q.1.2)
    let e : (ParticleConfig d N × OneParticle d) × OneParticle d ≃ᵐ ParticleConfig d N × (OneParticle d × OneParticle d) := MeasurableEquiv.prodAssoc
    have he : MeasurePreserving e Q (P.prod (μ.prod μ)) := measurePreserving_prodAssoc P μ μ
    have hswap : MeasurePreserving A Q Q := (MeasurePreserving.symm e he).comp
      (((MeasurePreserving.id P).prod Measure.measurePreserving_swap).comp he)
    have hproj2 : MeasurePreserving (fun q : (ParticleConfig d N × OneParticle d) × OneParticle d => (q.1.1,q.2)) Q (P.prod μ) := hproj1.comp hswap
    have hprod : Integrable (fun q : (ParticleConfig d N × OneParticle d) × OneParticle d => F i q.1*F j (q.1.1,q.2)) Q :=
      ((hmem i).1.comp_measurePreserving hproj1).integrable_mul ((hmem j).1.comp_measurePreserving hproj2)
    let E := fun q : (ParticleConfig d N × OneParticle d) × OneParticle d =>
      Real.exp (-(coupling/(N:ℝ))*RieszKernel s ε (q.1.2-q.2))
    have hEm : Measurable E := by
      dsimp [E,RieszKernel]
      simp only [ne_of_gt hε, if_false]
      fun_prop
    have hE (q) : 0 ≤ E q ∧ E q ≤ 1 := by
      refine ⟨Real.exp_nonneg _, Real.exp_le_one_iff.mpr ?_⟩
      simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg (div_nonneg hc (Nat.cast_nonneg N)) ((RieszKernelBounds s ε hs hε.le).1 (q.1.2-q.2)))
    change Integrable (fun q => E q*F i q.1*F j (q.1.1,q.2)) Q ∧
      Integrable (fun q => (1-E q)*F i q.1*F j (q.1.1,q.2)) Q
    constructor
    · simpa only [mul_assoc] using hprod.bdd_mul hEm.aestronglyMeasurable
        (Eventually.of_forall fun q => by rw [Real.norm_eq_abs,abs_of_nonneg (hE q).1]; exact (hE q).2)
    · simpa only [mul_assoc, Pi.sub_apply] using hprod.bdd_mul (measurable_const.sub hEm).aestronglyMeasurable
        (Eventually.of_forall fun q => by
          change ‖1-E q‖ ≤ (1:ℝ)
          rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (hE q).2)]
          linarith [(hE q).1])
