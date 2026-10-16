module

public import Tablet.WeightedMeanJointL2
public import Tablet.WeightedJointRowL2
public import Tablet.NativeGibbsReplacementBalance
public import Tablet.GibbsInsertionReference
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Tactic

@[expose] public section
open MeasureTheory Filter Set
open scoped ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

-- [TABLET NODE: NativeGibbsJumpVariance]
theorem NativeGibbsJumpVariance (d : ℕ) (hd : 3 ≤ d) (s B κ L M1 : ℝ)
    (hs : 0 < s) (hsd : s ≤ (d:ℝ)-2) (hB : 0 ≤ B) (hκ : 0 < κ) (hL : 1 ≤ L)
    (V b : OneParticle d → ℝ) (hV : Continuous V) (hb : BoundedMultiplier d L b)
    (hquad : ∀ x, κ/2*‖x‖^2 ≤ V x-V 0)
    (hlocal : ∀ x, ‖x‖ ≤ 1 → V x-V 0 ≤ M1)
    (N : ℕ) (hN : 2 ≤ N) (coupling ε : ℝ)
    (hc : 0 ≤ coupling) (hcB : coupling ≤ B) (hε : 0 < ε) :
    let μ := ReferenceLaw V b
    let P := GibbsLaw (N:=N) μ s coupling ε
    let U := fun (X : ParticleConfig d N) (i : Fin N) (z : OneParticle d) =>
      ∑ j ∈ Finset.univ.erase i, (coupling/(N:ℝ))*RieszKernel s ε (z-ParticlePosition X j)
    let Z := fun X i => ∫ z, Real.exp (-U X i z) ∂μ
    let ν := fun X i => ReferenceLaw (fun z => V z+U X i z) b
    let J := fun i => (P.prod μ).withDensity
      (fun q => ENNReal.ofReal (Real.exp (-U q.1 i q.2)))
    (∀ (i : Fin N) (g : ParticleConfig d N × OneParticle d → ℝ), Integrable g (J i) →
      (∫ q,g q ∂J i)=∫ X,Z X i*(∫ z,g (X,z) ∂ν X i) ∂P) ∧
    ∀ (f : ParticleConfig d N → ℝ), MemLp f 2 P →
      (∀ i : Fin N, ∀ᵐ X ∂P,
        MemLp (fun z => f (ParticleInsertion X i z)) 2 (ν X i)) ∧
      (∀ i : Fin N, Integrable (fun X => Z X i*
        ProbabilityTheory.variance (fun z => f (ParticleInsertion X i z)) (ν X i)) P) ∧
      (1/2:ℝ)*(∑ i : Fin N, ∫ q, (f (ParticleInsertion q.1 i q.2)-f q.1)^2 ∂J i) =
        ∫ X, ∑ i : Fin N, Z X i*
          ProbabilityTheory.variance (fun z => f (ParticleInsertion X i z)) (ν X i) ∂P := by
-- BODY
  classical
  dsimp only
  let μ := ReferenceLaw V b
  let P := GibbsLaw (N:=N) μ s coupling ε
  let U := fun (X : ParticleConfig d N) (i : Fin N) (z : OneParticle d) =>
    ∑ j ∈ Finset.univ.erase i, (coupling/(N:ℝ))*RieszKernel s ε (z-ParticlePosition X j)
  let r := fun i (q : ParticleConfig d N × OneParticle d) => Real.exp (-U q.1 i q.2)
  let Z := fun X i => ∫ z, r i (X,z) ∂μ
  let ν := fun X i => ReferenceLaw (fun z => V z+U X i z) b
  let J := fun i => (P.prod μ).withDensity (fun q => ENNReal.ofReal (r i q))
  obtain ⟨C,hC,href⟩ := ReferenceOffsetDensity d (by omega) s κ L M1 hs (by linarith) hκ hL
  haveI : IsProbabilityMeasure μ := (href V b hV hb hquad hlocal).2.2.1
  haveI : IsProbabilityMeasure P := (SoftGibbsNormalization μ s coupling ε hs hc hε).2.2
  obtain ⟨D,hD,hsite⟩ := GibbsInsertionReference d hd s B κ L M1 hs hsd hB hκ hL
  have hsitedata (X : ParticleConfig d N) (i : Fin N) :=
    hsite V b hV hb hquad hlocal N hN coupling ε hc hcB hε X i
  have hZ (X : ParticleConfig d N) (i : Fin N) : 0 < Z X i := by
    have h := (hsitedata X i).2.2.2.2.1
    exact (Real.exp_pos _).trans_le h
  have hνprob (X : ParticleConfig d N) (i : Fin N) : IsProbabilityMeasure (ν X i) :=
    (hsitedata X i).2.2.2.2.2.2.2.2
  have htilt (X : ParticleConfig d N) (i : Fin N) :
      ν X i=μ.withDensity (fun z => ENNReal.ofReal ((Z X i)⁻¹*r i (X,z))) :=
    (hsitedata X i).2.2.2.2.2.2.2.1
  have hUn (X : ParticleConfig d N) (i : Fin N) (z : OneParticle d) : 0 ≤ U X i z := by
    dsimp [U]
    exact Finset.sum_nonneg (fun j hj => mul_nonneg (div_nonneg hc (Nat.cast_nonneg N))
      ((RieszKernelBounds s ε hs hε.le).1 _))
  have hr (i : Fin N) (q : ParticleConfig d N × OneParticle d) : 0 ≤ r i q ∧ r i q ≤ 1 :=
    ⟨Real.exp_nonneg _,Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hUn q.1 i q.2))⟩
  have hrm (i : Fin N) : Measurable (r i) := by
    have hUm : Measurable (fun q : ParticleConfig d N × OneParticle d => U q.1 i q.2) := by
      dsimp [U]
      apply Finset.measurable_sum
      intro j hj
      apply Measurable.const_mul
      unfold RieszKernel
      simp only [ne_of_gt hε,if_false]
      unfold ParticlePosition
      fun_prop
    exact hUm.neg.exp
  have hbJ (i : Fin N) := NativeGibbsReplacementBalance d N μ s coupling ε hs hc hε i
  have hinsmeas (i : Fin N) : Measurable
      (fun q : ParticleConfig d N × OneParticle d => ParticleInsertion q.1 i q.2) :=
    measurable_fst.comp (hbJ i).1.measurable
  have insert_position (X : ParticleConfig d N) (i j : Fin N) (z : OneParticle d) :
      ParticlePosition (ParticleInsertion X i z) j = if j=i then z else ParticlePosition X j := by
    ext k
    by_cases hji : j=i <;> simp [ParticlePosition,ParticleInsertion,hji]
  have replace_self (X : ParticleConfig d N) (i : Fin N) : ParticleInsertion X i (ParticlePosition X i)=X := by
    ext jk
    rcases jk with ⟨j,k⟩
    by_cases hji : j=i
    · subst j; simp [ParticleInsertion,ParticlePosition]
    · simp [ParticleInsertion,hji]
  have replace_twice_same (X : ParticleConfig d N) (i : Fin N) (z v : OneParticle d) :
      ParticleInsertion (ParticleInsertion X i z) i v=ParticleInsertion X i v := by
    ext jk
    rcases jk with ⟨j,k⟩
    by_cases hji : j=i <;> simp [ParticleInsertion,hji]
  have hUinv (X : ParticleConfig d N) (i : Fin N) (z v : OneParticle d) :
      U (ParticleInsertion X i z) i v=U X i v := by
    dsimp [U]
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    rw [insert_position,if_neg hji]
  let delta (f : ParticleConfig d N → ℝ) (i : Fin N) (q : ParticleConfig d N × OneParticle d) :=
    f (ParticleInsertion q.1 i q.2)-f q.1
  let conditionalMean (f : ParticleConfig d N → ℝ) (X : ParticleConfig d N) (i : Fin N) :=
    (∫ z, r i (X,z)*f (ParticleInsertion X i z) ∂μ)/Z X i
  have conditional_mean_replacement (f : ParticleConfig d N → ℝ) (X : ParticleConfig d N)
      (i : Fin N) (z : OneParticle d) :
      conditionalMean f (ParticleInsertion X i z) i=conditionalMean f X i := by
    dsimp [conditionalMean,r,Z]
    simp_rw [hUinv,replace_twice_same]
  have joint_endpoint_L2 (f : ParticleConfig d N → ℝ) (hf : MemLp f 2 P) (i : Fin N) :
      MemLp (fun q : ParticleConfig d N × OneParticle d => f q.1) 2 (J i) ∧
      MemLp (fun q => f (ParticleInsertion q.1 i q.2)) 2 (J i) ∧ MemLp (delta f i) 2 (J i) := by
    have ho := (hf.mono_measure (hbJ i).2.1).comp_of_map measurable_fst.aemeasurable
    have hn := (hf.mono_measure (hbJ i).2.2).comp_of_map (hinsmeas i).aemeasurable
    exact ⟨ho,hn,hn.sub ho⟩
  have joint_integral_as_rows (i : Fin N) (g : ParticleConfig d N × OneParticle d → ℝ)
      (hg : Integrable g (J i)) :
      Integrable (fun q => r i q*g q) (P.prod μ) ∧
      (∫ q,g q ∂J i)=∫ X,∫ z,r i (X,z)*g (X,z) ∂μ ∂P := by
    have hm := (hrm i).ennreal_ofReal
    have hfin : ∀ᵐ q ∂P.prod μ, ENNReal.ofReal (r i q)<⊤ := Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
    have ht := (integrable_withDensity_iff_integrable_smul' hm hfin).mp hg
    simp only [ENNReal.toReal_ofReal (hr i _).1,smul_eq_mul] at ht
    refine ⟨ht,?_⟩
    change (∫ q,g q ∂(P.prod μ).withDensity _)=_
    rw [integral_withDensity_eq_integral_toReal_smul hm hfin]
    simp only [ENNReal.toReal_ofReal (hr i _).1,smul_eq_mul]
    exact integral_prod _ ht
  have joint_swap_integral (i : Fin N) (g : ParticleConfig d N × OneParticle d → ℝ)
      (hg : Integrable g (J i)) :
      (∫ q,g q ∂J i)=∫ q,g (ParticleInsertion q.1 i q.2,ParticlePosition q.1 i) ∂J i := by
    have hS : MeasurePreserving
        (fun q : ParticleConfig d N × OneParticle d =>
          (ParticleInsertion q.1 i q.2,ParticlePosition q.1 i)) (J i) (J i) := (hbJ i).1
    have hm : AEStronglyMeasurable g ((J i).map (fun q => (ParticleInsertion q.1 i q.2,ParticlePosition q.1 i))) := by
      rw [hS.map_eq];exact hg.1
    simpa only [hS.map_eq,Function.comp_def] using integral_map hS.measurable.aemeasurable hm
  have conditional_integral_formula (X : ParticleConfig d N) (i : Fin N) (g : OneParticle d → ℝ) :
      (∫ z,g z ∂ν X i)=(∫ z,r i (X,z)*g z ∂μ)/Z X i := by
    have hn (z : OneParticle d) : 0 ≤ (Z X i)⁻¹*r i (X,z) := mul_nonneg (inv_nonneg.mpr (hZ X i).le) (hr i (X,z)).1
    have hm : Measurable (fun z => ENNReal.ofReal ((Z X i)⁻¹*r i (X,z))) :=
      ((hrm i).comp (measurable_const.prodMk measurable_id)).const_mul _ |>.ennreal_ofReal
    have hfin : ∀ᵐ z ∂μ, ENNReal.ofReal ((Z X i)⁻¹*r i (X,z))<⊤ := Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
    rw [htilt X i,integral_withDensity_eq_integral_toReal_smul hm hfin]
    simp only [ENNReal.toReal_ofReal (hn _),smul_eq_mul]
    rw [← integral_div]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by simp only [div_eq_mul_inv];ring
  have conditional_slice_L2 (f : ParticleConfig d N → ℝ) (hf : MemLp f 2 P) (i : Fin N) :
      ∀ᵐ X ∂P, MemLp (fun z => f (ParticleInsertion X i z)) 2 (ν X i) := by
    have hj := (joint_endpoint_L2 f hf i).2.1
    have hw := WeightedJointRowL2 P μ (r i) (hrm i) (hr i) (fun q => f (ParticleInsertion q.1 i q.2)) hj
    have hAC : P.prod μ ≪ J i := withDensity_absolutelyContinuous' (hrm i).ennreal_ofReal.aemeasurable
      (Eventually.of_forall fun q => ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))
    have hfm := hj.aestronglyMeasurable.mono_ac hAC
    filter_upwards [hw.2.1.prod_right_ae,hfm.prodMk_left] with X hX hXm
    rw [htilt X i]
    have hn (z : OneParticle d) : 0 ≤ (Z X i)⁻¹*r i (X,z) := mul_nonneg (inv_nonneg.mpr (hZ X i).le) (hr i (X,z)).1
    have hm : Measurable (fun z => ENNReal.ofReal ((Z X i)⁻¹*r i (X,z))) :=
      ((hrm i).comp (measurable_const.prodMk measurable_id)).const_mul _ |>.ennreal_ofReal
    have hfin : ∀ᵐ z ∂μ, ENNReal.ofReal ((Z X i)⁻¹*r i (X,z))<⊤ := Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
    have hsq : Integrable (fun z => (f (ParticleInsertion X i z))^2) (μ.withDensity (fun z => ENNReal.ofReal ((Z X i)⁻¹*r i (X,z)))) := by
      apply (integrable_withDensity_iff_integrable_smul' hm hfin).mpr
      have h := hX.const_mul ((Z X i)⁻¹)
      simpa only [ENNReal.toReal_ofReal (hn _),smul_eq_mul,mul_assoc] using h
    exact (memLp_two_iff_integrable_sq (hXm.mono_ac (withDensity_absolutelyContinuous _ _))).mpr hsq
  have joint_dirichlet_identity (f : ParticleConfig d N → ℝ) (hf : MemLp f 2 P) (i : Fin N) :
      -(∫ q,f q.1*delta f i q ∂J i)=(1/2:ℝ)*(∫ q,(delta f i q)^2 ∂J i) := by 
    let J := J i
    let S := fun p : (ParticleConfig d N) × OneParticle d => (ParticleInsertion p.1 i p.2,ParticlePosition p.1 i)
    have hS : MeasurePreserving S J J := (hbJ i).1
    have hfJ := joint_endpoint_L2 f hf i
    have ho : Integrable (fun p => f p.1*delta f i p) J := hfJ.1.integrable_mul hfJ.2.2
    have hn : Integrable (fun p => f (ParticleInsertion p.1 i p.2)*(-delta f i p)) J := hfJ.2.1.integrable_mul hfJ.2.2.neg
    have he : (∫ p, f p.1*delta f i p ∂J) =
        ∫ p, f (ParticleInsertion p.1 i p.2)*(-delta f i p) ∂J := by
      calc
        _ = ∫ p, f (S p).1*delta f i (S p) ∂J := by
          have hm : AEStronglyMeasurable (fun p : (ParticleConfig d N) × OneParticle d => f p.1*delta f i p) (J.map S) := by
            rw [hS.map_eq]
            exact ho.aestronglyMeasurable
          have hh := integral_map hS.measurable.aemeasurable hm
          simpa only [hS.map_eq] using hh
        _ = _ := by
          apply integral_congr_ae
          exact Eventually.of_forall fun p => by
            dsimp [S,delta]
            rw [replace_twice_same,replace_self]
            ring
    have hsum : (∫ p, f p.1*delta f i p ∂J)+
        (∫ p, f (ParticleInsertion p.1 i p.2)*(-delta f i p) ∂J) =
        -(∫ p, (delta f i p)^2 ∂J) := by
      rw [← integral_add ho hn,← integral_neg]
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by dsimp [delta]; ring
    rw [← he] at hsum
    linarith
  have joint_conditional_variance_identity (f : ParticleConfig d N → ℝ) (hf : MemLp f 2 P) (i : Fin N) :
      Integrable (fun X => Z X i*ProbabilityTheory.variance (fun z => f (ParticleInsertion X i z)) (ν X i)) P ∧
      (1/2:ℝ)*(∫ q,(delta f i q)^2 ∂J i)=
        ∫ X,Z X i*ProbabilityTheory.variance (fun z => f (ParticleInsertion X i z)) (ν X i) ∂P := by 
    let J := J i
    let r := fun p : (ParticleConfig d N) × OneParticle d => Real.exp (-U p.1 i p.2)
    let Z := fun X => Z X i
    let M := fun X => ∫ z, r (X,z)*f (ParticleInsertion X i z) ∂μ
    let H := fun X => ∫ z, r (X,z)*(f (ParticleInsertion X i z))^2 ∂μ
    let m := fun X => conditionalMean f X i
    have : IsProbabilityMeasure P := inferInstance
    have hrm : Measurable r := hrm i
    have hr (p : (ParticleConfig d N) × OneParticle d) : 0 ≤ r p ∧ r p ≤ 1 :=
      ⟨Real.exp_nonneg _,Real.exp_le_one_iff.mpr
        (neg_nonpos.mpr (hUn p.1 i p.2))⟩
    have hZ (X : ParticleConfig d N) : 0 < Z X := hZ X i
    have hfJ := joint_endpoint_L2 f hf i
    have hw := WeightedJointRowL2 P μ r hrm hr (fun p => f (ParticleInsertion p.1 i p.2)) hfJ.2.1
    have hmJ := WeightedMeanJointL2 P μ r hrm hr hZ (fun p => f (ParticleInsertion p.1 i p.2)) hfJ.2.1
    have hmi (X : ParticleConfig d N) (z : OneParticle d) : m (ParticleInsertion X i z)=m X :=
      conditional_mean_replacement f X i z
    have hZm (X : ParticleConfig d N) : Z X*m X=M X := by
      dsimp [m,conditionalMean,M]
      exact mul_div_cancel₀ _ (hZ X).ne'
    have hmL : MemLp (fun p : (ParticleConfig d N) × OneParticle d => m p.1) 2 J := hmJ.1
    have hZi : Integrable (fun X => Z X*(m X)^2) P := hmJ.2
    have hHi : Integrable H P := hw.2.1.integral_prod_left
    have hom : Integrable (fun p : (ParticleConfig d N) × OneParticle d => f p.1*m p.1) J := hfJ.1.integrable_mul hmL
    have hnm : Integrable (fun p : (ParticleConfig d N) × OneParticle d => f (ParticleInsertion p.1 i p.2)*m p.1) J := hfJ.2.1.integrable_mul hmL
    have hon : Integrable (fun p : (ParticleConfig d N) × OneParticle d => f p.1*f (ParticleInsertion p.1 i p.2)) J := hfJ.1.integrable_mul hfJ.2.1
    have homswap : (∫ p, f p.1*m p.1 ∂J)=(∫ p, f (ParticleInsertion p.1 i p.2)*m p.1 ∂J) := by
      rw [joint_swap_integral i _ hom]
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by simp only [hmi]
    have homrow : (∫ p, f p.1*m p.1 ∂J)=∫ X, f X*M X ∂P := by
      rw [(joint_integral_as_rows i _ hom).2]
      apply integral_congr_ae
      exact Eventually.of_forall fun X => by
        change (∫ z, r (X,z)*(f X*m X) ∂μ)=f X*M X
        rw [integral_mul_const]
        change Z X*(f X*m X)=f X*M X
        rw [← hZm X]
        ring
    have hnmrow : (∫ p, f (ParticleInsertion p.1 i p.2)*m p.1 ∂J)=∫ X, Z X*(m X)^2 ∂P := by
      rw [(joint_integral_as_rows i _ hnm).2]
      apply integral_congr_ae
      exact Eventually.of_forall fun X => by
        have he : (fun z => r (X,z)*(f (ParticleInsertion X i z)*m X))=
            fun z => (r (X,z)*f (ParticleInsertion X i z))*m X := by funext z; ring
        change (∫ z, r (X,z)*(f (ParticleInsertion X i z)*m X) ∂μ)=_
        rw [he,integral_mul_const]
        change M X*m X=Z X*(m X)^2
        rw [← hZm X]
        ring
    have honrow : (∫ p, f p.1*f (ParticleInsertion p.1 i p.2) ∂J)=∫ X, f X*M X ∂P := by
      rw [(joint_integral_as_rows i _ hon).2]
      apply integral_congr_ae
      exact Eventually.of_forall fun X => by
        have he : (fun z => r (X,z)*(f X*f (ParticleInsertion X i z)))=
            fun z => f X*(r (X,z)*f (ParticleInsertion X i z)) := by funext z; ring
        change (∫ z, r (X,z)*(f X*f (ParticleInsertion X i z)) ∂μ)=_
        rw [he,integral_const_mul]
    have hcross : (∫ p, f p.1*f (ParticleInsertion p.1 i p.2) ∂J)=∫ X, Z X*(m X)^2 ∂P := by
      rw [honrow,← homrow,homswap,hnmrow]
    have hsquares : (∫ p, (f p.1)^2 ∂J)=∫ X, H X ∂P := by
      rw [joint_swap_integral i _ hfJ.1.integrable_sq]
      exact (joint_integral_as_rows i _ hfJ.2.1.integrable_sq).2
    have hvar : (fun X => Z X*ProbabilityTheory.variance
        (fun z => f (ParticleInsertion X i z)) (ν X i)) =ᵐ[P]
          fun X => H X-Z X*(m X)^2 := by
      filter_upwards [conditional_slice_L2 f hf i] with X hX
      have : IsProbabilityMeasure (ν X i) := hνprob X i
      rw [ProbabilityTheory.variance_eq_sub hX,
        conditional_integral_formula X i,
        conditional_integral_formula X i]
      change Z X*(H X/Z X-(m X)^2)=H X-Z X*(m X)^2
      field_simp [(hZ X).ne']
    have hVi : Integrable (fun X => Z X*ProbabilityTheory.variance
        (fun z => f (ParticleInsertion X i z)) (ν X i)) P := (hHi.sub hZi).congr hvar.symm
    refine ⟨hVi,?_⟩
    rw [← joint_dirichlet_identity f hf i]
    have he : (fun p : (ParticleConfig d N) × OneParticle d => f p.1*delta f i p)=
        fun p => f p.1*f (ParticleInsertion p.1 i p.2)-(f p.1)^2 := by
      funext p
      dsimp [delta]
      ring
    rw [he,integral_sub hon hfJ.1.integrable_sq,hcross,hsquares]
    rw [integral_congr_ae hvar,integral_sub hHi hZi]
    ring
  refine ⟨?_,?_⟩
  · intro i g hg
    rw [(joint_integral_as_rows i g hg).2]
    apply integral_congr_ae
    exact Eventually.of_forall fun X => by
      change (∫ z,r i (X,z)*g (X,z) ∂μ)=Z X i*(∫ z,g (X,z) ∂ν X i)
      rw [conditional_integral_formula X i]
      exact (mul_div_cancel₀ _ (hZ X i).ne').symm
  · intro f hf
    refine ⟨conditional_slice_L2 f hf,fun i => (joint_conditional_variance_identity f hf i).1,?_⟩
    rw [Finset.mul_sum,integral_finsetSum _ (fun i _ => (joint_conditional_variance_identity f hf i).1)]
    exact Finset.sum_congr rfl (fun i hi => (joint_conditional_variance_identity f hf i).2)
