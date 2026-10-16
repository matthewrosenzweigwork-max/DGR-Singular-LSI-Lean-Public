import Tablet.ReferenceTranslation
import Tablet.CommonReferenceDensity
import Tablet.ReferenceLawProbability
import Tablet.RieszProbabilityRows
import Tablet.HessianQuadraticSupport
import Tablet.SoftGibbsNormalization
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal
noncomputable section

-- [TABLET NODE: FiniteGibbsMeanPartition]
theorem FiniteGibbsMeanPartition (d : ℕ) (hd : 3 ≤ d) (s κ L M1 : ℝ)
    (hs : 0 < s) (hsd : s ≤ (d : ℝ)-2) (hκ : 0 < κ) (hL : 1 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ V b : OneParticle d → ℝ,
      PotentialBounds d κ V → (∀ x, V 0 ≤ V x) →
      (∀ x, ‖x‖ ≤ 1 → V x-V 0 ≤ M1) → BoundedMultiplier d L b →
      ReferencePartition (fun x => V x-V 0) b = Real.exp (V 0)*ReferencePartition V b ∧
      ReferenceLaw (fun x => V x-V 0) b = ReferenceLaw V b ∧
      0 < ReferencePartition V b ∧ IsProbabilityMeasure (ReferenceLaw V b) ∧
      ∀ N : ℕ, 1 ≤ N → ∀ coupling ε : ℝ, 0 ≤ coupling → 0 < ε →
        let μ := ReferenceLaw V b
        let ν := ConfigurationReference d N μ
        IsProbabilityMeasure ν ∧ Integrable (PairInteraction (N:=N) s coupling ε) ν ∧
        (∫ X, PairInteraction s coupling ε X ∂ν) ≤
          (coupling/(N : ℝ))*(∑ i : Fin N, ∑ j : Fin N, if i<j then C else 0) ∧
        (∫ X, PairInteraction s coupling ε X ∂ν) ≤ coupling*(N : ℝ)*C ∧
        Real.exp (-(coupling*(N : ℝ)*C)) ≤ GibbsPartition (N:=N) μ s coupling ε ∧
        GibbsPartition (N:=N) μ s coupling ε ≤ 1 ∧
        IsProbabilityMeasure (GibbsLaw (N:=N) μ s coupling ε) := by
-- BODY
  classical
  let v := (volume : Measure (OneParticle d)).real (Metric.ball 0 1)
  let Q := L*Real.exp M1/v
  have hv : 0 < v := ENNReal.toReal_pos
    (ne_of_gt (Metric.measure_ball_pos volume (0 : OneParticle d) (by norm_num)))
    (ne_of_lt (lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
      (isCompact_closedBall (0 : OneParticle d) 1).measure_lt_top))
  have hQ : 0 ≤ Q := div_nonneg (mul_nonneg (by linarith) (Real.exp_pos _).le) hv.le
  obtain ⟨C,hC,hrow⟩ := RieszProbabilityRows d (by omega) s Q hs (by linarith) hQ
  refine ⟨C,hC,?_⟩
  intro V b hV hmin hlocal hb
  let W := fun x => V x-V 0
  have hz : fderiv ℝ V 0 = 0 :=
    (show IsLocalMin V 0 from Eventually.of_forall hmin).fderiv_eq_zero
  have hquad (x : OneParticle d) : κ/2*‖x‖^2 ≤ W x := by
    have h := (HessianQuadraticSupport V κ hV 0 x).2
    simp only [hz, ContinuousLinearMap.zero_apply, sub_zero, add_zero] at h
    dsimp [W]; linarith
  have hpart : ReferencePartition W b = Real.exp (V 0)*ReferencePartition V b := by
    simpa [ShiftedReference,W] using (ReferenceTranslation V b 0).1
  have hlaw : ReferenceLaw W b = ReferenceLaw V b := by
    have h := (ReferenceTranslation V b 0).2
    simpa [ShiftedReference,W,Measure.map_id] using h.symm
  obtain ⟨m,M,hm,_,hcontrast,hbounds⟩ := hb.bounds
  have hbound (x) : m ≤ b x ∧ b x ≤ L*m :=
    ⟨(hbounds x).1,(hbounds x).2.trans ((div_le_iff₀ hm).mp hcontrast)⟩
  have hnorm := ReferenceQuadraticNormalization V b κ (V 0) L hκ hV.regularity.continuous hb
    (fun x => by have h := hquad x; dsimp [W] at h; linarith)
  have hprob : IsProbabilityMeasure (ReferenceLaw V b) :=
    ReferenceLawProbability V b hnorm.1 (fun x => hm.le.trans (hbounds x).1) hnorm.2
  have hdom : ReferenceLaw V b ≤ ENNReal.ofReal Q • volume := by
    have h := (CommonReferenceDensity W b κ m L M1 hκ hm hL
      (hV.regularity.continuous.sub continuous_const) hb.measurable hbound hquad hlocal).2.2.2.2.2
    simpa only [hlaw] using h
  refine ⟨hpart,hlaw,hnorm.2,hprob,?_⟩
  intro N hN coupling ε hcoupling hε
  dsimp only
  let μ := ReferenceLaw V b
  let ν := ConfigurationReference d N μ
  letI : IsProbabilityMeasure μ := hprob
  letI : IsProbabilityMeasure ν := ConfigurationReferenceProbability d N μ
  have hrows (y : OneParticle d) := hrow ε hε.le μ hprob hdom y
  let K := fun p : OneParticle d × OneParticle d => RieszKernel s ε (p.1-p.2)
  have hKm : Measurable K := by dsimp [K]; simp only [RieszKernel,ne_of_gt hε,if_false]; fun_prop
  have hKn (p) : 0 ≤ K p := (RieszKernelBounds s ε hs hε.le).1 _
  have hnormK : (fun y => ∫ x, ‖K (x,y)‖ ∂μ) = (fun y => ∫ x, K (x,y) ∂μ) := by
    funext y; apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change ‖K (x,y)‖ = K (x,y)
      rw [Real.norm_eq_abs,abs_of_nonneg (hKn _)]
  have hKI : Integrable K (μ.prod μ) := by
    apply (integrable_prod_iff' hKm.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall fun y => (hrows y).1,?_⟩
    rw [hnormK]
    apply (integrable_const C).mono' hKm.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
    exact Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg fun x => hKn (x,y))]
      exact (hrows y).2
  have hKM : (∫ p, K p ∂μ.prod μ) ≤ C := by
    rw [integral_prod_symm K hKI]
    simpa using integral_mono hKI.integral_prod_right (integrable_const C) (fun y => (hrows y).2)
  have hpairMap (i j : Fin N) (hij : i ≠ j) :
      MeasurePreserving (fun X : ParticleConfig d N => (ParticlePosition X i,ParticlePosition X j)) ν (μ.prod μ) := by
    have hInd := (iIndepFun_pi (μ:=fun _ : Fin N => μ) (X:=fun _ => id)
      (fun _ => aemeasurable_id)).indepFun hij
    have hp : MeasurePreserving (fun Y : Fin N → OneParticle d => (Y i,Y j))
        (Measure.pi (fun _ : Fin N => μ)) (μ.prod μ) := by
      refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j),?_⟩
      have h := hInd.map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
        (measurable_pi_apply j).aemeasurable
      simpa only [(measurePreserving_eval (fun _ : Fin N => μ) i).map_eq,
        (measurePreserving_eval (fun _ : Fin N => μ) j).map_eq] using h
    have hpm : Measurable (fun X : ParticleConfig d N => (ParticlePosition X i,ParticlePosition X j)) := by
      unfold ParticlePosition; fun_prop
    refine ⟨hpm,?_⟩
    dsimp [ν]; unfold ConfigurationReference
    have hfm : Measurable (fun Y : Fin N → OneParticle d =>
      WithLp.toLp 2 (fun ik : Fin N × Fin d => Y ik.1 ik.2)) := by fun_prop
    rw [Measure.map_map hpm hfm]
    convert hp.map_eq using 1
    congr 1
  let F := fun (i j : Fin N) (X : ParticleConfig d N) =>
    if i<j then RieszKernel s ε (ParticlePosition X i-ParticlePosition X j) else 0
  have hF (i j : Fin N) : Integrable (F i j) ν ∧ (∫ X, F i j X ∂ν) ≤ (if i<j then C else 0) := by
    by_cases hij : i<j
    · have hp := hpairMap i j (ne_of_lt hij)
      have hi := hp.integrable_comp_of_integrable hKI
      have he := integral_map (μ:=ν) hp.measurable.aemeasurable hKm.aestronglyMeasurable
      rw [hp.map_eq] at he
      refine ⟨by simpa [F,hij,K,Function.comp_def] using hi,?_⟩
      simpa [F,hij,K] using he.symm.trans_le hKM
    · simp [F,hij]
  have hirow (i : Fin N) : Integrable (fun X => ∑ j : Fin N, F i j X) ν :=
    integrable_finsetSum _ (fun j _ => (hF i j).1)
  have hiSum : Integrable (fun X => ∑ i : Fin N, ∑ j : Fin N, F i j X) ν :=
    integrable_finsetSum _ (fun i _ => hirow i)
  have hUi : Integrable (PairInteraction (N:=N) s coupling ε) ν := by
    change Integrable (fun X => (coupling/(N:ℝ))*(∑ i : Fin N, ∑ j : Fin N, F i j X)) ν
    exact hiSum.const_mul (coupling/(N:ℝ))
  have hmean : (∫ X, PairInteraction (N:=N) s coupling ε X ∂ν) ≤
      (coupling/(N:ℝ))*(∑ i : Fin N, ∑ j : Fin N, if i<j then C else 0) := by
    unfold PairInteraction
    change (∫ X, (coupling/(N:ℝ))*(∑ i : Fin N, ∑ j : Fin N, F i j X) ∂ν) ≤ _
    rw [integral_const_mul,integral_finsetSum _ (fun i _ => hirow i)]
    apply mul_le_mul_of_nonneg_left _ (div_nonneg hcoupling (Nat.cast_nonneg N))
    apply Finset.sum_le_sum
    intro i _
    rw [integral_finsetSum _ (fun j _ => (hF i j).1)]
    exact Finset.sum_le_sum fun j _ => (hF i j).2
  have hcoarse : (∫ X, PairInteraction (N:=N) s coupling ε X ∂ν) ≤ coupling*(N:ℝ)*C := by
    have hsum : (∑ i : Fin N, ∑ j : Fin N, if i<j then C else 0) ≤ (N:ℝ)^2*C := by
      have h := Finset.sum_le_sum (s:=Finset.univ) fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) =>
        Finset.sum_le_sum (s:=Finset.univ) fun j (_ : j ∈ (Finset.univ : Finset (Fin N))) =>
          (show (if i<j then C else 0) ≤ C by split_ifs <;> simp [hC])
      have := h
      simpa [sq,mul_assoc] using this
    have hh := hmean.trans (mul_le_mul_of_nonneg_left hsum (div_nonneg hcoupling (Nat.cast_nonneg N)))
    have hn : (N:ℝ) ≠ 0 := by exact_mod_cast (show N≠0 by omega)
    have he : (coupling/(N:ℝ))*((N:ℝ)^2*C) = coupling*(N:ℝ)*C := by field_simp
    simpa only [he] using hh
  have hw (X : ParticleConfig d N) : InteractionWeight s coupling ε X = Real.exp (-PairInteraction s coupling ε X) := by
    by_cases h : coupling=0
    · simp [h,InteractionWeight,PairInteraction]
    · simp [InteractionWeight,h,ne_of_gt hε]
  have hn := SoftGibbsNormalization (N:=N) μ s coupling ε hs hcoupling hε
  have hiExp : Integrable (fun X => Real.exp (-PairInteraction (N:=N) s coupling ε X)) ν := by
    have he : InteractionWeight s coupling ε = (fun X : ParticleConfig d N => Real.exp (-PairInteraction s coupling ε X)) := funext hw
    rw [← he]
    exact hn.1
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Eventually.of_forall fun _ => Set.mem_univ _) hUi.neg hiExp
  simp only [Pi.neg_apply] at hj
  rw [integral_neg] at hj
  have hJ : Real.exp (-(coupling*(N:ℝ)*C)) ≤ GibbsPartition (N:=N) μ s coupling ε := by
    have h := (Real.exp_le_exp.mpr (neg_le_neg hcoarse)).trans hj
    simpa only [GibbsPartition,hw] using h
  exact ⟨inferInstance,hUi,hmean,hcoarse,hJ,hn.2.1.2,hn.2.2⟩

#print axioms FiniteGibbsMeanPartition
