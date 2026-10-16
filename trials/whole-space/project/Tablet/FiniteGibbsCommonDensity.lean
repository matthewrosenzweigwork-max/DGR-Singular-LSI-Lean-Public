module

public import Tablet.FiniteGibbsMeanPartition
public import Tablet.GibbsRawDensity
public import Tablet.GaussianConfinementIntegral
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 3000000
open MeasureTheory Filter Set
open scoped ENNReal NNReal
noncomputable section

-- [TABLET NODE: FiniteGibbsCommonDensity]
theorem FiniteGibbsCommonDensity (d Nmax : ℕ) (hd : 3 ≤ d) (hNmax : 1 ≤ Nmax)
    (s B κ L : ℝ) (hs : 0 < s) (hsd : s ≤ (d : ℝ)-2)
    (hB : 0 ≤ B) (hκ : 0 < κ) (hL : 1 ≤ L) (Mloc : ℝ → ℝ) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 < D ∧ ∃ beta : ℝ → ℝ → ℝ,
      (∀ R T, 0 < R → 0 < T → 0 < beta R T) ∧
      ∀ V b : OneParticle d → ℝ, PotentialBounds d κ V →
      (∀ x, V 0 ≤ V x) →
      (∀ R, 0 < R → ∀ x, ‖x‖ ≤ R → V x-V 0 ≤ Mloc R) →
      BoundedMultiplier d L b → ∀ N : ℕ, 1 ≤ N → N ≤ Nmax →
      ∀ coupling ε : ℝ, 0 ≤ coupling → coupling ≤ B → 0 < ε →
      let μ := ReferenceLaw V b
      let Z := GibbsPartition (N:=N) μ s coupling ε
      let Zraw := (ReferencePartition V b)^N * Z
      let raw := fun X : ParticleConfig d N =>
        (∏ i : Fin N, b (ParticlePosition X i)) *
          Real.exp (-( (∑ i : Fin N, V (ParticlePosition X i)) + PairInteraction s coupling ε X))
      let p := GibbsLebesgueDensity (N:=N) V b s coupling ε
      Real.exp (-(B*(Nmax:ℝ)*C)) ≤ Z ∧ Z ≤ 1 ∧ 0 < Zraw ∧
      Integrable raw volume ∧ (∫ X, raw X) = Zraw ∧
      Measurable p ∧ (∀ X, 0 ≤ p X) ∧
      (∀ X, p X = Zraw⁻¹ * raw X) ∧
      IsProbabilityMeasure (GibbsLaw (N:=N) μ s coupling ε) ∧
      GibbsLaw (N:=N) μ s coupling ε = volume.withDensity (fun X => ENNReal.ofReal (p X)) ∧
      (∀ X, p X ≤ D*Real.exp (-(κ/2)*‖X‖^2)) ∧
      (∀ R T, 0 < R → 0 < T → ∀ X, ‖X‖ ≤ R → PairInteraction s coupling ε X ≤ 2*T →
        beta R T ≤ p X) := by
-- BODY
  classical
  let v := (volume : Measure (OneParticle d)).real (Metric.ball 0 1)
  let Q := L*Real.exp (Mloc 1)/v
  let G := ∫ x : OneParticle d, Real.exp (-(κ/2)*‖x‖^2)
  have hv : 0 < v := ENNReal.toReal_pos
    (ne_of_gt (Metric.measure_ball_pos volume (0 : OneParticle d) (by norm_num)))
    (ne_of_lt (lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
      (isCompact_closedBall (0 : OneParticle d) 1).measure_lt_top))
  have hQ : 0 < Q := div_pos (mul_pos (by linarith) (Real.exp_pos _)) hv
  have hG : 0 < G := (GaussianConfinementIntegral (ι:=Fin d) κ hκ).2.2
  obtain ⟨C,hC,hMean⟩ := FiniteGibbsMeanPartition d hd s κ L (Mloc 1) hs hsd hκ hL
  let A := B*(Nmax:ℝ)*C
  let D := Real.exp A*(max 1 Q)^Nmax
  let beta := fun R T : ℝ =>
    (min 1 (Real.exp (-Mloc R)/(L*G)))^Nmax * Real.exp (-(2*T))
  have hD : 0 < D := mul_pos (Real.exp_pos _) (pow_pos (lt_max_of_lt_left (by norm_num)) _)
  have hbpos (R T : ℝ) : 0 < beta R T := by
    dsimp [beta]
    exact mul_pos (pow_pos (lt_min (by norm_num)
      (div_pos (Real.exp_pos _) (mul_pos (by linarith) hG))) _) (Real.exp_pos _)
  refine ⟨C,D,hC,hD,beta,(fun R T _ _ => hbpos R T),?_⟩
  intro V b hV hmin hlocal hb N hN hNbound coupling ε hc hcB hε
  dsimp only
  let μ := ReferenceLaw V b
  let Z := GibbsPartition (N:=N) μ s coupling ε
  let W := fun x => V x-V 0
  let q := fun x => (ReferencePartition V b)⁻¹*(b x*Real.exp (-V x))
  let p := GibbsLebesgueDensity (N:=N) V b s coupling ε
  have hdata := hMean V b hV hmin (hlocal 1 (by norm_num)) hb
  have hZref : 0 < ReferencePartition V b := hdata.2.2.1
  have hprob := hdata.2.2.2.1
  letI : IsProbabilityMeasure μ := hprob
  have hNP := hdata.2.2.2.2 N hN coupling ε hc hε
  have hZlower : Real.exp (-A) ≤ Z := by
    have hscale : coupling*(N:ℝ)*C ≤ A := by
      apply mul_le_mul_of_nonneg_right _ hC
      apply mul_le_mul hcB (by exact_mod_cast hNbound) (Nat.cast_nonneg N) hB
    exact (Real.exp_le_exp.mpr (neg_le_neg hscale)).trans hNP.2.2.2.2.1
  have hZone : Z ≤ 1 := hNP.2.2.2.2.2.1
  have hZ : 0 < Z := (Real.exp_pos (-A)).trans_le hZlower
  have hProbG : IsProbabilityMeasure (GibbsLaw (N:=N) μ s coupling ε) := hNP.2.2.2.2.2.2
  have hRaw : 0 < (ReferencePartition V b)^N*Z := mul_pos (pow_pos hZref N) hZ
  have hz : fderiv ℝ V 0 = 0 :=
    (show IsLocalMin V 0 from Eventually.of_forall hmin).fderiv_eq_zero
  have hquad (x : OneParticle d) : κ/2*‖x‖^2 ≤ W x := by
    have h := (HessianQuadraticSupport V κ hV 0 x).2
    simp only [hz,ContinuousLinearMap.zero_apply,sub_zero,add_zero] at h
    dsimp [W]; linarith
  obtain ⟨m,M,hm,_,hcontrast,hbounds⟩ := hb.bounds
  have hbound (x) : m ≤ b x ∧ b x ≤ L*m :=
    ⟨(hbounds x).1,(hbounds x).2.trans ((div_le_iff₀ hm).mp hcontrast)⟩
  have hcap := CommonReferenceDensity W b κ m L (Mloc 1) hκ hm hL
    (hV.regularity.continuous.sub continuous_const) hb.measurable hbound hquad (hlocal 1 (by norm_num))
  have hqeq (x) : (ReferencePartition W b)⁻¹*(b x*Real.exp (-W x)) = q x := by
    rw [hdata.1]
    have he : Real.exp (-W x) = Real.exp (V 0)*Real.exp (-V x) := by
      dsimp [W]; rw [neg_sub,sub_eq_add_neg,Real.exp_add]
    rw [he,mul_inv_rev]
    dsimp [q]
    field_simp [Real.exp_ne_zero (V 0)]
  have hqnonneg (x) : 0 ≤ q x := mul_nonneg (inv_nonneg.mpr hZref.le)
    (mul_nonneg (hm.le.trans (hbounds x).1) (Real.exp_pos _).le)
  have hqupper (x) : q x ≤ Q*Real.exp (-(κ/2)*‖x‖^2) := by
    have h := hcap.2.2.2.1 x
    simpa only [hqeq] using h
  have hqlower (R : ℝ) (hR : 0 < R) (x : OneParticle d) (hx : ‖x‖ ≤ R) :
      Real.exp (-Mloc R)/(L*G) ≤ q x := by
    have h := hcap.2.2.2.2.1 R (Mloc R) (hlocal R hR) x hx
    simpa only [hqeq] using h
  have hw (X : ParticleConfig d N) : InteractionWeight s coupling ε X = Real.exp (-PairInteraction s coupling ε X) := by
    by_cases h : coupling=0
    · simp [h,InteractionWeight,PairInteraction]
    · simp [InteractionWeight,h,ne_of_gt hε]
  have hpq (X : ParticleConfig d N) : p X = Z⁻¹*((∏ i : Fin N, q (ParticlePosition X i))*
      Real.exp (-PairInteraction s coupling ε X)) := by
    have hprod : (∏ i : Fin N, q (ParticlePosition X i)) =
        ((ReferencePartition V b)^N)⁻¹ *
          ((∏ i : Fin N, b (ParticlePosition X i))*Real.exp (-(∑ i : Fin N, V (ParticlePosition X i)))) := by
      dsimp [q]
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,inv_pow,
        Finset.prod_mul_distrib,← Real.exp_sum,Finset.sum_neg_distrib]
      simp only [Fintype.card_fin]
    rw [hprod]
    dsimp [p,Z,μ]; unfold GibbsLebesgueDensity
    rw [hw,mul_inv_rev]
    ring
  have hpnonneg (X) : 0 ≤ p X := by
    rw [hpq]
    exact mul_nonneg (inv_nonneg.mpr hZ.le)
      (mul_nonneg (Finset.prod_nonneg fun i _ => hqnonneg _) (Real.exp_pos _).le)
  have hnorm (X : ParticleConfig d N) : ‖X‖^2 = ∑ i : Fin N, ‖ParticlePosition X i‖^2 := by
    simp only [EuclideanSpace.real_norm_sq_eq,Fintype.sum_prod_type,ParticlePosition]
  have hposnorm (X : ParticleConfig d N) (i : Fin N) : ‖ParticlePosition X i‖ ≤ ‖X‖ := by
    have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin N))) => sq_nonneg ‖ParticlePosition X j‖)
      (Finset.mem_univ i)
    rw [← hnorm X] at h
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h
  have hUn (X : ParticleConfig d N) : 0 ≤ PairInteraction s coupling ε X := by
    unfold PairInteraction
    apply mul_nonneg (div_nonneg hc (Nat.cast_nonneg N))
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    split_ifs
    · exact (RieszKernelBounds s ε hs hε.le).1 _
    · exact le_rfl
  have hupper (X : ParticleConfig d N) : p X ≤ D*Real.exp (-(κ/2)*‖X‖^2) := by
    have he : (∑ i : Fin N, -(κ/2)*‖ParticlePosition X i‖^2) = -(κ/2)*‖X‖^2 := by
      rw [← Finset.mul_sum,← hnorm X]
    have hprod : (∏ i : Fin N, q (ParticlePosition X i)) ≤ Q^N*Real.exp (-(κ/2)*‖X‖^2) := by
      calc
        _ ≤ ∏ i : Fin N, Q*Real.exp (-(κ/2)*‖ParticlePosition X i‖^2) :=
          Finset.prod_le_prod₀ (s:=Finset.univ) (fun i _ => hqnonneg (ParticlePosition X i))
            (fun i _ => hqupper (ParticlePosition X i))
        _ = _ := by
          rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,← Real.exp_sum,he]
          simp only [Fintype.card_fin]
    have hnum : (∏ i : Fin N, q (ParticlePosition X i))*Real.exp (-PairInteraction s coupling ε X) ≤
        Q^N*Real.exp (-(κ/2)*‖X‖^2) :=
      (mul_le_of_le_one_right (Finset.prod_nonneg fun i _ => hqnonneg _)
        (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hUn X)))).trans hprod
    have hdiv := div_le_div₀ (by positivity : 0 ≤ Q^N*Real.exp (-(κ/2)*‖X‖^2))
      hnum (Real.exp_pos (-A)) hZlower
    have hpbound : p X ≤ (Real.exp A*Q^N)*Real.exp (-(κ/2)*‖X‖^2) := by
      rw [hpq]
      simpa [div_eq_mul_inv,Real.exp_neg,mul_assoc,mul_comm,mul_left_comm] using hdiv
    have hpow : Q^N ≤ (max 1 Q)^Nmax :=
      (pow_le_pow_left₀ hQ.le (le_max_right _ _) N).trans
        (pow_le_pow_right₀ (le_max_left _ _) hNbound)
    exact hpbound.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le) (Real.exp_pos _).le)
  have hlower (R T : ℝ) (hR : 0 < R) (_hT : 0 < T) (X : ParticleConfig d N)
      (hx : ‖X‖ ≤ R) (hU : PairInteraction s coupling ε X ≤ 2*T) : beta R T ≤ p X := by
    let a := Real.exp (-Mloc R)/(L*G)
    have ha : 0 < a := div_pos (Real.exp_pos _) (mul_pos (by linarith) hG)
    have hp : a^N ≤ ∏ i : Fin N, q (ParticlePosition X i) := by
      have h := Finset.prod_le_prod₀ (s:=Finset.univ) (fun i _ => ha.le)
        (fun i _ => hqlower R hR (ParticlePosition X i) ((hposnorm X i).trans hx))
      simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using h
    have hn := mul_le_mul hp (Real.exp_le_exp.mpr (neg_le_neg hU))
      (Real.exp_pos (-(2*T))).le (Finset.prod_nonneg fun i _ => hqnonneg _)
    have hdiv := div_le_div₀ (mul_nonneg (Finset.prod_nonneg fun i _ => hqnonneg _) (Real.exp_pos _).le)
      hn hZ hZone
    have hb : a^N*Real.exp (-(2*T)) ≤ p X := by
      rw [hpq]
      simpa [div_eq_mul_inv,mul_comm] using hdiv
    have hpow : (min 1 a)^Nmax ≤ a^N :=
      (pow_le_pow_of_le_one (le_min (by norm_num) ha.le) (min_le_left _ _) hNbound).trans
        (pow_le_pow_left₀ (le_min (by norm_num) ha.le) (min_le_right _ _) N)
    exact (mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le).trans hb
  have hpm (i : Fin N) : Measurable (fun X : ParticleConfig d N => ParticlePosition X i) := by
    unfold ParticlePosition; fun_prop
  have hpmeas : Measurable p := by
    have hbprod : Measurable (fun X : ParticleConfig d N => ∏ i : Fin N, b (ParticlePosition X i)) :=
      Finset.measurable_prod _ (fun i _ => hb.measurable.comp (hpm i))
    have hsum : Measurable (fun X : ParticleConfig d N => ∑ i : Fin N, V (ParticlePosition X i)) :=
      Finset.measurable_sum _ (fun i _ => hV.regularity.continuous.measurable.comp (hpm i))
    exact ((measurable_const.mul hbprod).mul hsum.neg.exp).mul (InteractionWeightMeasurable s coupling ε)
  have hlaw := GibbsRawDensity (N:=N) (by omega : 0<d) V b κ L hκ hV hb s coupling ε hs hc hε.le
  have hlin : (∫⁻ X, ENNReal.ofReal (p X)) = 1 := by
    haveI : IsProbabilityMeasure (volume.withDensity (fun X => ENNReal.ofReal (p X))) := by
      rw [← hlaw]; exact hProbG
    have h := (measure_univ : (volume.withDensity (fun X => ENNReal.ofReal (p X))) univ = 1)
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ] at h
    exact h
  have hpI : Integrable p volume := by
    refine ⟨hpmeas.aestronglyMeasurable,?_⟩
    change (∫⁻ X, ‖p X‖ₑ) < ⊤
    have he : (fun X => ‖p X‖ₑ) = fun X => ENNReal.ofReal (p X) := by
      funext X; rw [← ofReal_norm,Real.norm_eq_abs,abs_of_nonneg (hpnonneg X)]
    rw [he,hlin]; exact ENNReal.one_lt_top
  have hpone : (∫ X, p X) = 1 := by
    have he := ofReal_integral_eq_lintegral_ofReal hpI (Eventually.of_forall hpnonneg)
    rw [hlin] at he
    have h := congrArg ENNReal.toReal he
    simpa only [ENNReal.toReal_ofReal (integral_nonneg hpnonneg),ENNReal.toReal_one] using h
  let raw := fun X : ParticleConfig d N => (∏ i : Fin N, b (ParticlePosition X i))*
    Real.exp (-((∑ i : Fin N, V (ParticlePosition X i))+PairInteraction s coupling ε X))
  let Zraw := (ReferencePartition V b)^N*Z
  have hpraw (X) : p X = Zraw⁻¹*raw X := by
    dsimp [p,Zraw,Z,μ,raw]; unfold GibbsLebesgueDensity
    rw [hw,neg_add,Real.exp_add]
    ring
  have hraw (X) : raw X = Zraw*p X := by
    rw [hpraw]; exact (mul_inv_cancel_left₀ (ne_of_gt hRaw) (raw X)).symm
  have hrawI : Integrable raw volume := (hpI.const_mul Zraw).congr (Eventually.of_forall fun X => (hraw X).symm)
  have hrawZ : (∫ X, raw X) = Zraw := by
    simp_rw [hraw]
    rw [integral_const_mul,hpone,mul_one]
  exact ⟨hZlower,hZone,hRaw,hrawI,hrawZ,hpmeas,hpnonneg,hpraw,hProbG,hlaw,hupper,hlower⟩

#print axioms FiniteGibbsCommonDensity
