module

public import Tablet.WeightedMeanJointL2
public import Tablet.WeightedJointRowL2
public import Tablet.NativeGibbsJumpVariance
public import Tablet.GibbsInsertionReference
public import Mathlib.Tactic

@[expose] public section
open MeasureTheory Filter Set
open scoped ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

-- [TABLET NODE: NativeGibbsSameLabel]
theorem NativeGibbsSameLabel (d : ℕ) (hd : 3 ≤ d) (s B κ L M1 : ℝ)
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
    ∀ (f : ParticleConfig d N → ℝ) (hf : MemLp f 2 P) (i : Fin N),
      Integrable (fun X => (Z X i)^2*
        ProbabilityTheory.variance (fun z => f (ParticleInsertion X i z)) (ν X i)) P ∧
      (∫ X,(∫ z,Real.exp (-U X i z)*(f (ParticleInsertion X i z)-f X) ∂μ)^2 ∂P)=
        ∫ X,(Z X i)^2*ProbabilityTheory.variance
          (fun z => f (ParticleInsertion X i z)) (ν X i) ∂P := by
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
    dsimp only [U]
    exact Finset.sum_nonneg (fun j hj => mul_nonneg (div_nonneg hc (Nat.cast_nonneg N))
      ((RieszKernelBounds s ε hs hε.le).1 _))
  have hr (i : Fin N) (q : ParticleConfig d N × OneParticle d) : 0 ≤ r i q ∧ r i q ≤ 1 :=
    ⟨Real.exp_nonneg _,Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hUn q.1 i q.2))⟩
  have hrm (i : Fin N) : Measurable (r i) := by
    have hUm : Measurable (fun q : ParticleConfig d N × OneParticle d => U q.1 i q.2) := by
      dsimp only [U]
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
    dsimp only [U]
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
    dsimp only [conditionalMean,r,Z]
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
      ∀ᵐ X ∂P, MemLp (fun z => f (ParticleInsertion X i z)) 2 (ν X i) :=
    ((NativeGibbsJumpVariance d hd s B κ L M1 hs hsd hB hκ hL V b hV hb hquad hlocal
      N hN coupling ε hc hcB hε).2 f hf).1 i
  have hri (X : ParticleConfig d N) (i : Fin N) : Integrable (fun z => r i (X,z)) μ := by
    apply (integrable_const (1:ℝ)).mono_nonneg
      (((hrm i).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    · exact Eventually.of_forall fun z => (hr i (X,z)).1
    · exact Eventually.of_forall fun z => (hr i (X,z)).2
  have hZle (X : ParticleConfig d N) (i : Fin N) : Z X i ≤ 1 := by
    change (∫ z,r i (X,z) ∂μ) ≤ 1
    calc
      _ ≤ ∫ _ : OneParticle d,(1:ℝ) ∂μ := integral_mono
        (hri X i)
        (integrable_const _) (fun z => (hr i (X,z)).2)
      _ = 1 := by simp
  intro f hf i
  let Ji := J i
  let ri := r i
  let Zi := fun X => Z X i
  let mi := fun X => conditionalMean f X i
  let νi := fun X => ν X i
  have hmi (X : ParticleConfig d N) (z : OneParticle d) : mi (ParticleInsertion X i z)=mi X :=
    conditional_mean_replacement f X i z
  have hzi (X : ParticleConfig d N) (z : OneParticle d) : Zi (ParticleInsertion X i z)=Zi X := by
    dsimp only [Zi,Z,r];simp_rw [hUinv]
  have hZm : Measurable Zi := (hrm i).stronglyMeasurable.integral_prod_right'.measurable
  have hfJ := joint_endpoint_L2 f hf i
  have hw := WeightedJointRowL2 P μ ri (hrm i) (hr i) (fun p => f (ParticleInsertion p.1 i p.2)) hfJ.2.1
  have hmJ := WeightedMeanJointL2 P μ ri (hrm i) (hr i) (fun X => (hZ X i))
    (fun p => f (ParticleInsertion p.1 i p.2)) hfJ.2.1
  have hmL : MemLp (fun p : (ParticleConfig d N) × OneParticle d => mi p.1) 2 Ji := hmJ.1
  let G₀ := fun p : (ParticleConfig d N) × OneParticle d => Zi p.1*(f p.1-mi p.1)^2
  let G₁ := fun p : (ParticleConfig d N) × OneParticle d => Zi p.1*(f (ParticleInsertion p.1 i p.2)-mi p.1)^2
  have hg₀ : Integrable G₀ Ji := by
    have hi := (hfJ.1.sub hmL).integrable_sq.bdd_mul
      (hZm.comp measurable_fst).aestronglyMeasurable (Eventually.of_forall fun p => by
        change ‖Zi p.1‖ ≤ (1:ℝ)
        rw [Real.norm_eq_abs,abs_of_pos (hZ p.1 i)]
        exact hZle p.1 i)
    apply hi.congr
    exact Eventually.of_forall fun p => by
      rfl
  have hg₁ : Integrable G₁ Ji := by
    have hi := (hfJ.2.1.sub hmL).integrable_sq.bdd_mul
      (hZm.comp measurable_fst).aestronglyMeasurable (Eventually.of_forall fun p => by
        change ‖Zi p.1‖ ≤ (1:ℝ)
        rw [Real.norm_eq_abs,abs_of_pos (hZ p.1 i)]
        exact hZle p.1 i)
    apply hi.congr
    exact Eventually.of_forall fun p => by
      rfl
  have hswap : (∫ p, G₀ p ∂Ji)=∫ p, G₁ p ∂Ji := by
    rw [joint_swap_integral i G₀ hg₀]
    apply integral_congr_ae
    exact Eventually.of_forall fun p => by dsimp only [G₀,G₁]; rw [hzi,hmi]
  have hcenter : ∀ᵐ X ∂P, (∫ z, ri (X,z)*(f (ParticleInsertion X i z)-mi X)^2 ∂μ)=
      Zi X*ProbabilityTheory.variance (fun z => f (ParticleInsertion X i z)) (νi X) := by
    filter_upwards [conditional_slice_L2 f hf i] with X hX
    have hm : (∫ z, f (ParticleInsertion X i z) ∂νi X)=mi X :=
      conditional_integral_formula X i _
    rw [ProbabilityTheory.variance_eq_integral hX.1.aemeasurable,hm,
      conditional_integral_formula X i]
    change _=Zi X*((∫ z, ri (X,z)*(f (ParticleInsertion X i z)-mi X)^2 ∂μ)/Zi X)
    field_simp [show Zi X ≠ 0 from (hZ X i).ne']
  have hrawsq : ∀ᵐ X ∂P, (∫ z, ri (X,z)*delta f i (X,z) ∂μ)^2=
      (Zi X)^2*(f X-mi X)^2 := by
    filter_upwards [hw.1.prod_right_ae] with X hX
    have he : (fun z => ri (X,z)*delta f i (X,z))=
        fun z => ri (X,z)*f (ParticleInsertion X i z)-ri (X,z)*f X := by funext z; dsimp only [delta]; ring
    rw [he,integral_sub hX ((hri X i).mul_const (f X)),integral_mul_const]
    change ((∫ z, ri (X,z)*f (ParticleInsertion X i z) ∂μ)-Zi X*f X)^2=
      (Zi X)^2*(f X-(∫ z, ri (X,z)*f (ParticleInsertion X i z) ∂μ)/Zi X)^2
    field_simp [show Zi X ≠ 0 from (hZ X i).ne']
    ring
  have hrow₀ : (fun X => ∫ z, ri (X,z)*G₀ (X,z) ∂μ)=
      fun X => (Zi X)^2*(f X-mi X)^2 := by
    funext X
    dsimp only [G₀]
    rw [integral_mul_const]
    change Zi X*(Zi X*(f X-mi X)^2)=(Zi X)^2*(f X-mi X)^2
    ring
  have hrow₁ : (fun X => ∫ z, ri (X,z)*G₁ (X,z) ∂μ) =ᵐ[P]
      fun X => (Zi X)^2*ProbabilityTheory.variance (fun z => f (ParticleInsertion X i z)) (νi X) := by
    filter_upwards [hcenter] with X hX
    change (∫ z, ri (X,z)*(Zi X*(f (ParticleInsertion X i z)-mi X)^2) ∂μ)=_
    have he : (fun z => ri (X,z)*(Zi X*(f (ParticleInsertion X i z)-mi X)^2))=
        fun z => (ri (X,z)*(f (ParticleInsertion X i z)-mi X)^2)*Zi X := by funext z; ring
    rw [he,integral_mul_const,hX]
    ring
  have hrv := joint_integral_as_rows i G₁ hg₁
  have hvarI : Integrable (fun X => (Zi X)^2*ProbabilityTheory.variance (fun z => f (ParticleInsertion X i z)) (νi X)) P :=
    hrv.1.integral_prod_left.congr hrow₁
  refine ⟨hvarI,?_⟩
  rw [integral_congr_ae hrawsq,← hrow₀,
    ← (joint_integral_as_rows i G₀ hg₀).2,hswap,hrv.2,
    integral_congr_ae hrow₁]
