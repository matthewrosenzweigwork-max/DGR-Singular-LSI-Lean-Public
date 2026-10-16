module

public import Tablet.RawL2OperatorDescent
public import Tablet.WeightedJointRowL2
public import Tablet.NativeGibbsReplacementBalance
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Tactic

@[expose] public section
open MeasureTheory Filter Set
open scoped InnerProduct ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

-- [TABLET NODE: NativeGibbsJumpOperator]
theorem NativeGibbsJumpOperator (d N : ℕ) (μ : Measure (OneParticle d))
    [IsProbabilityMeasure μ] (s coupling ε : ℝ) (hs : 0 < s) (hc : 0 ≤ coupling) (hε : 0 < ε) :
    let P := GibbsLaw (N:=N) μ s coupling ε
    let U := fun (X : ParticleConfig d N) (i : Fin N) (z : OneParticle d) =>
      ∑ j ∈ Finset.univ.erase i, (coupling/(N:ℝ))*RieszKernel s ε (z-ParticlePosition X j)
    let J := fun i => (P.prod μ).withDensity (fun q => ENNReal.ofReal (Real.exp (-U q.1 i q.2)))
    ∃! A : Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P,
      ‖A‖ ≤ 2*(N:ℝ) ∧
      (∀ v w, inner ℝ v (A w)=inner ℝ (A v) w) ∧
      (∀ v, 0 ≤ inner ℝ v (A v)) ∧
      (∀ (f : ParticleConfig d N → ℝ) (hf : MemLp f 2 P),
        A (hf.toLp f) =ᵐ[P] fun X => ∑ i : Fin N, ∫ z,
          Real.exp (-U X i z)*(f X-f (ParticleInsertion X i z)) ∂μ) ∧
      (∀ (f g : ParticleConfig d N → ℝ) (hf : MemLp f 2 P) (hg : MemLp g 2 P),
        inner ℝ (hf.toLp f) (A (hg.toLp g))=(1/2:ℝ)*∑ i : Fin N, ∫ q,
          (f (ParticleInsertion q.1 i q.2)-f q.1)*(g (ParticleInsertion q.1 i q.2)-g q.1) ∂J i) ∧
      (∀ (f : ParticleConfig d N → ℝ) (hf : MemLp f 2 P),
        inner ℝ (hf.toLp f) (A (hf.toLp f))=(1/2:ℝ)*∑ i : Fin N, ∫ q,
          (f (ParticleInsertion q.1 i q.2)-f q.1)^2 ∂J i) := by
-- BODY
  classical
  have real_L2_inner_toLp {α : Type} [MeasurableSpace α] {μ : Measure α} (f g : α → ℝ)
      (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
      inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
    simp [hfx, hgx, mul_comm]
  have real_L2_norm_sq_toLp {α : Type} [MeasurableSpace α] {μ : Measure α} (f : α → ℝ) (hf : MemLp f 2 μ) :
      ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, real_L2_inner_toLp]
    simp_rw [pow_two]
  have difference_form_operator {ι H : Type} [Fintype ι] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    {K : ι → Type} [∀ i, NormedAddCommGroup (K i)]
    [∀ i, InnerProductSpace ℝ (K i)] [∀ i, CompleteSpace (K i)] (D : ∀ i, H →L[ℝ] K i)
      (hD : ∀ i, ‖D i‖ ≤ 2) :
      ∃ L : H →L[ℝ] H,
        ‖L‖ ≤ 2 * Fintype.card ι ∧
        (∀ v w, inner ℝ v (L w) = inner ℝ (L v) w) ∧
        (∀ v, -inner ℝ v (L v) = (1 / 2 : ℝ) * ∑ i, ‖D i v‖ ^ 2) ∧
        (∀ v, 0 ≤ -inner ℝ v (L v)) ∧
        (∀ v, L v = 0 ↔ ∀ i, D i v = 0) ∧
        (∀ v w, inner ℝ v (L w) = (-1 / 2 : ℝ) * ∑ i, inner ℝ (D i v) (D i w)) := by
    classical
    let L : H →L[ℝ] H := (-1 / 2 : ℝ) • ∑ i, (D i)†.comp (D i)
    have hnorm : ‖L‖ ≤ 2 * Fintype.card ι := by
      calc
        ‖L‖ = (1 / 2 : ℝ) * ‖∑ i, (D i)†.comp (D i)‖ := by
          simp [L, norm_smul]
        _ ≤ (1 / 2 : ℝ) * ∑ i, ‖(D i)†.comp (D i)‖ := by
          gcongr
          exact norm_sum_le _ _
        _ = (1 / 2 : ℝ) * ∑ i, ‖D i‖ ^ 2 := by
          simp only [ContinuousLinearMap.norm_adjoint_comp_self, pow_two]
        _ ≤ (1 / 2 : ℝ) * ∑ _i : ι, (4 : ℝ) := by
          gcongr with i
          nlinarith [hD i, norm_nonneg (D i)]
        _ = 2 * Fintype.card ι := by simp; ring
    have hbilin (v w : H) : inner ℝ v (L w) =
        (-1 / 2 : ℝ) * ∑ i, inner ℝ (D i v) (D i w) := by
      simp [L, inner_smul_right, inner_sum, ContinuousLinearMap.adjoint_inner_right]
    have hsym (v w : H) : inner ℝ v (L w) = inner ℝ (L v) w := by
      conv_rhs => rw [real_inner_comm]
      rw [hbilin, hbilin]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact real_inner_comm _ _
    have henergy (v : H) : -inner ℝ v (L v) =
        (1 / 2 : ℝ) * ∑ i, ‖D i v‖ ^ 2 := by
      rw [hbilin]
      simp only [real_inner_self_eq_norm_sq]
      ring
    have hpos (v : H) : 0 ≤ -inner ℝ v (L v) := by
      rw [henergy]
      positivity
    have hzero (v : H) : L v = 0 ↔ ∀ i, D i v = 0 := by
      constructor
      · intro hv
        have hz : ∑ i, ‖D i v‖ ^ 2 = 0 := by
          have he := henergy v
          rw [hv, inner_zero_right] at he
          linarith
        have hi := (Finset.sum_eq_zero_iff_of_nonneg
          (fun i (_ : i ∈ (Finset.univ : Finset ι)) => sq_nonneg ‖D i v‖)).mp hz
        intro i
        exact norm_eq_zero.mp (sq_eq_zero_iff.mp (hi i (Finset.mem_univ i)))
      · intro hv
        simp [L, hv]
    exact ⟨L, hnorm, hsym, henergy, hpos, hzero, hbilin⟩
  have endpoint_norm_bound {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
       (P : Measure α) (J : Measure β) (T : β → α) (hT : Measurable T)
       (hdom : J.map T ≤ P) (f : α → ℝ) (hf : MemLp f 2 P) :
       let h := (hf.mono_measure hdom).comp_of_map hT.aemeasurable
       ‖h.toLp (f ∘ T)‖ ≤ ‖hf.toLp f‖ := by
     dsimp only
     rw [Lp.norm_toLp,Lp.norm_toLp]
     apply ENNReal.toReal_mono hf.2.ne
     rw [← eLpNorm_map_measure (hf.mono_measure hdom).1 hT.aemeasurable]
     exact eLpNorm_mono_measure f hdom
  dsimp only
  let P := GibbsLaw (N:=N) μ s coupling ε
  let U := fun (X : ParticleConfig d N) (i : Fin N) (z : OneParticle d) =>
    ∑ j ∈ Finset.univ.erase i, (coupling/(N:ℝ))*RieszKernel s ε (z-ParticlePosition X j)
  let r := fun i (q : ParticleConfig d N × OneParticle d) => Real.exp (-U q.1 i q.2)
  let J := fun i => (P.prod μ).withDensity (fun q => ENNReal.ofReal (r i q))
  let delta (f : ParticleConfig d N → ℝ) (i : Fin N) (q : ParticleConfig d N × OneParticle d) :=
    f (ParticleInsertion q.1 i q.2)-f q.1
  let jumpOperator (f : ParticleConfig d N → ℝ) (X : ParticleConfig d N) :=
    ∑ i : Fin N, ∫ z,r i (X,z)*delta f i (X,z) ∂μ
  haveI : IsProbabilityMeasure P := (SoftGibbsNormalization μ s coupling ε hs hc hε).2.2
  have hUn (X : ParticleConfig d N) (i : Fin N) (z : OneParticle d) : 0 ≤ U X i z := by
    dsimp [U]; exact Finset.sum_nonneg (fun j hj => mul_nonneg (div_nonneg hc (Nat.cast_nonneg N))
      ((RieszKernelBounds s ε hs hε.le).1 _))
  have hr (i : Fin N) (q : ParticleConfig d N × OneParticle d) : 0 ≤ r i q ∧ r i q ≤ 1 :=
    ⟨Real.exp_nonneg _,Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hUn q.1 i q.2))⟩
  have hrm (i : Fin N) : Measurable (r i) := by
    have hUm : Measurable (fun q : ParticleConfig d N × OneParticle d => U q.1 i q.2) := by
      dsimp [U]; apply Finset.measurable_sum; intro j hj; apply Measurable.const_mul
      simp only [RieszKernel,ne_of_gt hε,if_false]
      unfold ParticlePosition
      fun_prop
    exact hUm.neg.exp
  have hbJ (i : Fin N) := NativeGibbsReplacementBalance d N μ s coupling ε hs hc hε i
  have hinsmeas (i : Fin N) : Measurable (fun q : ParticleConfig d N × OneParticle d => ParticleInsertion q.1 i q.2) :=
    measurable_fst.comp (hbJ i).1.measurable
  have replace_self (X : ParticleConfig d N) (i : Fin N) : ParticleInsertion X i (ParticlePosition X i)=X := by
    ext jk;rcases jk with ⟨j,k⟩;by_cases hji : j=i
    · subst j;simp [ParticleInsertion,ParticlePosition]
    · simp [ParticleInsertion,hji]
  have replace_twice_same (X : ParticleConfig d N) (i : Fin N) (z v : OneParticle d) :
      ParticleInsertion (ParticleInsertion X i z) i v=ParticleInsertion X i v := by
    ext jk;rcases jk with ⟨j,k⟩;by_cases hji : j=i <;> simp [ParticleInsertion,hji]
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
  have labeled_difference_operator (i : Fin N) :
    ∃! D : Lp ℝ 2 P →L[ℝ] Lp ℝ 2 (J i), ‖D‖ ≤ 2 ∧
      ∀ f (hf : MemLp f 2 P), D (hf.toLp f)=ᵐ[J i] delta f i := by
 
    let J := J i
    have hb := hbJ i
    have hmem (f : (ParticleConfig d N) → ℝ) (hf : MemLp f 2 P) : MemLp (delta f i) 2 J :=
      (joint_endpoint_L2 f hf i).2.2
    have hae (f g : (ParticleConfig d N) → ℝ) (hf : MemLp f 2 P) (hg : MemLp g 2 P)
        (he : f =ᵐ[P] g) : delta f i =ᵐ[J] delta g i := by
      have ho := ae_eq_comp measurable_fst.aemeasurable ((Measure.absolutelyContinuous_of_le hb.2.1).ae_eq he)
      have hn := ae_eq_comp (hinsmeas i).aemeasurable ((Measure.absolutelyContinuous_of_le hb.2.2).ae_eq he)
      filter_upwards [ho,hn] with p hp hq
      change f p.1 = g p.1 at hp
      change f (ParticleInsertion p.1 i p.2) = g (ParticleInsertion p.1 i p.2) at hq
      simp only [delta,hp,hq]
    have hadd (f g : (ParticleConfig d N) → ℝ) (_hf : MemLp f 2 P) (_hg : MemLp g 2 P) :
        delta (f+g) i =ᵐ[J] delta f i+delta g i := by
      exact Eventually.of_forall fun p => by simp only [delta,Pi.add_apply]; ring
    have hsmul (c : ℝ) (f : (ParticleConfig d N) → ℝ) (_hf : MemLp f 2 P) :
        delta (c • f) i =ᵐ[J] c • delta f i := by
      exact Eventually.of_forall fun p => by simp only [delta,Pi.smul_apply,smul_eq_mul]; ring
    have hbound (f : (ParticleConfig d N) → ℝ) (hf : MemLp f 2 P) :
        ‖(hmem f hf).toLp (delta f i)‖ ≤ 2*‖hf.toLp f‖ := by
      have hs := joint_endpoint_L2 f hf i
      have ho := endpoint_norm_bound P J Prod.fst measurable_fst hb.2.1 f hf
      have hn := endpoint_norm_bound P J (fun p => ParticleInsertion p.1 i p.2)
        (hinsmeas i) hb.2.2 f hf
      dsimp only at ho hn
      simp only [Lp.norm_toLp] at ho hn ⊢
      simp only [Function.comp_def] at ho hn
      have htriangle : eLpNorm (delta f i) 2 J ≤
          eLpNorm (fun p => f (ParticleInsertion p.1 i p.2)) 2 J+eLpNorm (fun p => f p.1) 2 J :=
        eLpNorm_sub_le hs.2.1.1 hs.1.1 (by norm_num)
      calc
        _ ≤ (eLpNorm (fun p => f (ParticleInsertion p.1 i p.2)) 2 J+
            eLpNorm (fun p => f p.1) 2 J).toReal :=
          ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hs.2.1.2.ne,hs.1.2.ne⟩) htriangle
        _ = (eLpNorm (fun p => f (ParticleInsertion p.1 i p.2)) 2 J).toReal+
            (eLpNorm (fun p => f p.1) 2 J).toReal := ENNReal.toReal_add hs.2.1.2.ne hs.1.2.ne
        _ ≤ (eLpNorm f 2 P).toReal+(eLpNorm f 2 P).toReal := add_le_add hn ho
        _ = _ := by ring
    exact RawL2OperatorDescent (delta · i) 2 (by norm_num) hmem hae hadd hsmul hbound
  have joint_bilinear_dirichlet_identity (f g : ParticleConfig d N → ℝ)
    (hf : MemLp f 2 P) (hg : MemLp g 2 P) (i : Fin N) :
    (∫ q,f q.1*delta g i q ∂J i)=(-1/2:ℝ)*(∫ q,delta f i q*delta g i q ∂J i) := by
 
    let J := J i
    let S := fun p : (ParticleConfig d N) × OneParticle d => (ParticleInsertion p.1 i p.2,ParticlePosition p.1 i)
    have hS : MeasurePreserving S J J := (hbJ i).1
    have hfJ := joint_endpoint_L2 f hf i
    have hgJ := joint_endpoint_L2 g hg i
    have ho : Integrable (fun p => f p.1*delta g i p) J := hfJ.1.integrable_mul hgJ.2.2
    have hn : Integrable (fun p => f (ParticleInsertion p.1 i p.2)*(-delta g i p)) J := hfJ.2.1.integrable_mul hgJ.2.2.neg
    have he : (∫ p, f p.1*delta g i p ∂J) =
        ∫ p, f (ParticleInsertion p.1 i p.2)*(-delta g i p) ∂J := by
      calc
        _ = ∫ p, f (S p).1*delta g i (S p) ∂J := by
          have hm : AEStronglyMeasurable (fun p : (ParticleConfig d N) × OneParticle d => f p.1*delta g i p) (J.map S) := by
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
    have hsum : (∫ p, f p.1*delta g i p ∂J)+
        (∫ p, f (ParticleInsertion p.1 i p.2)*(-delta g i p) ∂J) =
        -(∫ p, delta f i p*delta g i p ∂J) := by
      rw [← integral_add ho hn,← integral_neg]
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by dsimp [delta]; ring
    rw [← he] at hsum
    linarith
  have jumpOperator_bilinear_pairing (f g : ParticleConfig d N → ℝ)
    (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    Integrable (fun X => f X*jumpOperator g X) P ∧
      (∫ X,f X*jumpOperator g X ∂P)=(-1/2:ℝ)*∑ i : Fin N,∫ q,delta f i q*delta g i q ∂J i := by
 
    let H := fun (i : Fin N) (X : ParticleConfig d N) =>
      ∫ z, Real.exp (-U X i z)*(f X*delta g i (X,z)) ∂μ
    have hi (i : Fin N) : Integrable (H i) P := by
      have hfo := (joint_endpoint_L2 f hf i).1
      have hgd := (joint_endpoint_L2 g hg i).2.2
      exact (joint_integral_as_rows i _ (hfo.integrable_mul hgd)).1.integral_prod_left
    have hfun : (fun X => f X*jumpOperator g X) = fun X => ∑ i : Fin N, H i X := by
      funext X
      dsimp only [jumpOperator,H,delta]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by ring
    have hint : Integrable (fun X => f X*jumpOperator g X) P := by
      rw [hfun]
      exact integrable_finsetSum _ (fun i _ => hi i)
    refine ⟨hint,?_⟩
    rw [hfun,integral_finsetSum _ (fun i _ => hi i),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hifin
    have hfo := (joint_endpoint_L2 f hf i).1
    have hgd := (joint_endpoint_L2 g hg i).2.2
    have hrow := (joint_integral_as_rows i _ (hfo.integrable_mul hgd)).2
    dsimp only [H]
    simp only [Pi.mul_apply] at hrow
    rw [← hrow]
    exact joint_bilinear_dirichlet_identity f g hf hg i
  have labeled_row_operator (i : Fin N) :
    ∃! R : Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P, ‖R‖ ≤ 2 ∧
      ∀ f (hf : MemLp f 2 P), R (hf.toLp f)=ᵐ[P] fun X =>∫ z,r i (X,z)*delta f i (X,z) ∂μ := by
 
    let J := J i
    let r := fun p : (ParticleConfig d N) × OneParticle d => Real.exp (-U p.1 i p.2)
    let T := fun (f : (ParticleConfig d N) → ℝ) X => ∫ z, r (X,z)*delta f i (X,z) ∂μ
    have : IsProbabilityMeasure P := inferInstance
    have hrm : Measurable r := hrm i
    have hr (p : (ParticleConfig d N) × OneParticle d) : 0 ≤ r p ∧ r p ≤ 1 :=
      ⟨Real.exp_nonneg _,Real.exp_le_one_iff.mpr
        (neg_nonpos.mpr (hUn p.1 i p.2))⟩
    have hd (f : (ParticleConfig d N) → ℝ) (hf : MemLp f 2 P) : MemLp (delta f i) 2 J :=
      (joint_endpoint_L2 f hf i).2.2
    have hw (f : (ParticleConfig d N) → ℝ) (hf : MemLp f 2 P) :=
      WeightedJointRowL2 P μ r hrm hr (delta f i) (hd f hf)
    have hmem (f : (ParticleConfig d N) → ℝ) (hf : MemLp f 2 P) : MemLp (T f) 2 P := (hw f hf).2.2.1
    have hb := hbJ i
    have hAC : P.prod μ ≪ J := withDensity_absolutelyContinuous' hrm.ennreal_ofReal.aemeasurable
      (Eventually.of_forall fun p => ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))
    have hae (f g : (ParticleConfig d N) → ℝ) (_hf : MemLp f 2 P) (_hg : MemLp g 2 P)
        (he : f =ᵐ[P] g) : T f =ᵐ[P] T g := by
      have ho := ae_eq_comp measurable_fst.aemeasurable ((Measure.absolutelyContinuous_of_le hb.2.1).ae_eq he)
      have hn := ae_eq_comp (hinsmeas i).aemeasurable ((Measure.absolutelyContinuous_of_le hb.2.2).ae_eq he)
      have hdelt : delta f i =ᵐ[J] delta g i := by
        filter_upwards [ho,hn] with p hp hq
        change f p.1=g p.1 at hp
        change f (ParticleInsertion p.1 i p.2)=g (ParticleInsertion p.1 i p.2) at hq
        simp only [delta,hp,hq]
      have hprod := hAC.ae_eq hdelt
      have hrows := Measure.ae_ae_of_ae_prod hprod
      exact hrows.mono fun X hX => integral_congr_ae (hX.mono fun z hz => by
        change r (X,z)*delta f i (X,z)=r (X,z)*delta g i (X,z)
        rw [hz])
    have hadd (f g : (ParticleConfig d N) → ℝ) (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
        T (f+g) =ᵐ[P] T f+T g := by
      filter_upwards [(hw f hf).1.prod_right_ae,(hw g hg).1.prod_right_ae] with X hX hY
      change (∫ z, r (X,z)*delta (f+g) i (X,z) ∂μ)=_
      have he : (fun z => r (X,z)*delta (f+g) i (X,z)) =
          fun z => r (X,z)*delta f i (X,z)+r (X,z)*delta g i (X,z) := by
        funext z
        simp only [delta,Pi.add_apply]
        ring
      rw [he,integral_add hX hY]
      rfl
    have hsmul (c : ℝ) (f : (ParticleConfig d N) → ℝ) (_hf : MemLp f 2 P) :
        T (c • f) =ᵐ[P] c • T f := by
      exact Eventually.of_forall fun X => by
        have he : (fun z => r (X,z)*delta (c • f) i (X,z)) =
            fun z => c*(r (X,z)*delta f i (X,z)) := by
          funext z
          simp only [delta,Pi.smul_apply,smul_eq_mul]
          ring
        change (∫ z, r (X,z)*delta (c • f) i (X,z) ∂μ)=_
        rw [he,integral_const_mul]
        rfl
    have hbound (f : (ParticleConfig d N) → ℝ) (hf : MemLp f 2 P) :
        ‖(hmem f hf).toLp (T f)‖ ≤ 2*‖hf.toLp f‖ := by
      have hs := (hw f hf).2.2.2
      change (∫ X, (T f X)^2 ∂P) ≤ ∫ p, (delta f i p)^2 ∂J at hs
      rw [← real_L2_norm_sq_toLp (T f) (hmem f hf),← real_L2_norm_sq_toLp (delta f i) (hd f hf)] at hs
      have hrow := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs
      obtain ⟨D,hD,_⟩ := labeled_difference_operator i
      have hrepr : D (hf.toLp f)=(hd f hf).toLp (delta f i) := by
        apply Lp.ext
        exact (hD.2 f hf).trans (MemLp.coeFn_toLp _).symm
      rw [← hrepr] at hrow
      exact hrow.trans ((D.le_opNorm _).trans (mul_le_mul_of_nonneg_right hD.1 (norm_nonneg _)))
    exact RawL2OperatorDescent T 2 (by norm_num) hmem hae hadd hsmul hbound
  let D := fun i : Fin N => (labeled_difference_operator i).choose
  have hD (i : Fin N) := (labeled_difference_operator i).choose_spec.1
  have hreprD (i : Fin N) (f : ParticleConfig d N → ℝ) (hf : MemLp f 2 P) :
      D i (hf.toLp f)=(joint_endpoint_L2 f hf i).2.2.toLp (delta f i) := by
    apply Lp.ext;exact ((hD i).2 f hf).trans (MemLp.coeFn_toLp _).symm
  obtain ⟨L,hLn,hLs,hLe,hLpos,hLzero,hLb⟩ := difference_form_operator D (fun i => (hD i).1)
  have hbil (f g : ParticleConfig d N → ℝ) (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
      inner ℝ (hf.toLp f) (L (hg.toLp g))=(-1/2:ℝ)*∑ i : Fin N,∫ q,delta f i q*delta g i q ∂J i := by
    rw [hLb];congr 1;apply Finset.sum_congr rfl;intro i hi
    rw [hreprD,hreprD];exact real_L2_inner_toLp _ _ _ _
  let R := fun i : Fin N => (labeled_row_operator i).choose
  have hR (i : Fin N) := (labeled_row_operator i).choose_spec.1
  let T : Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P := ∑ i : Fin N,R i
  have hreprT (f : ParticleConfig d N → ℝ) (hf : MemLp f 2 P) :
      T (hf.toLp f)=ᵐ[P] jumpOperator f := by
    have hall : ∀ᵐ X ∂P,∀ i : Fin N,
      R i (hf.toLp f) X=∫ z,r i (X,z)*delta f i (X,z) ∂μ := eventually_all.mpr fun i => (hR i).2 f hf
    have hsum := Lp.coeFn_fun_finsetSum Finset.univ (fun i : Fin N => R i (hf.toLp f))
    change (⇑(T (hf.toLp f)))=ᵐ[P] _
    simp only [T,sum_apply] at ⊢
    filter_upwards [hall,hsum] with X hX hXs
    rw [hXs];apply Finset.sum_congr rfl;intro i hi;exact hX i
  have heq : T=L := by
    apply ContinuousLinearMap.ext;intro v;apply ext_inner_left ℝ;intro w
    have ht : inner ℝ w (T v)=∫ X,w X*jumpOperator v X ∂P := by
      rw [L2.inner_def];apply integral_congr_ae
      have hh := hreprT v (Lp.memLp v);simp only [Lp.toLp_coeFn] at hh
      filter_upwards [hh] with X hX;simp [hX,mul_comm]
    rw [ht]
    have hb := (jumpOperator_bilinear_pairing w v (Lp.memLp w) (Lp.memLp v)).2
    have hl := hbil w v (Lp.memLp w) (Lp.memLp v)
    simp only [Lp.toLp_coeFn] at hl;exact hb.trans hl.symm
  let A := -L
  have hreprA (f : ParticleConfig d N → ℝ) (hf : MemLp f 2 P) :
      A (hf.toLp f)=ᵐ[P] fun X =>∑ i : Fin N,∫ z,r i (X,z)*(f X-f (ParticleInsertion X i z)) ∂μ := by
    have h := hreprT f hf
    rw [heq] at h
    have hn := Lp.coeFn_neg (L (hf.toLp f))
    filter_upwards [h,hn] with X hX hN
    change (-L (hf.toLp f)) X=_
    rw [hN]
    change -(L (hf.toLp f) X)=_
    rw [hX]
    simp only [jumpOperator,←Finset.sum_neg_distrib,←integral_neg]
    apply Finset.sum_congr rfl;intro i hi
    apply integral_congr_ae;exact Eventually.of_forall fun z => by dsimp [delta];ring
  have hbilA (f g : ParticleConfig d N → ℝ) (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
      inner ℝ (hf.toLp f) (A (hg.toLp g))=(1/2:ℝ)*∑ i : Fin N,∫ q,delta f i q*delta g i q ∂J i := by
    change inner ℝ (hf.toLp f) (-(L (hg.toLp g)))=_
    rw [inner_neg_right,hbil];ring
  refine ⟨A,⟨?_,?_,?_,hreprA,hbilA,?_⟩,?_⟩
  · simpa only [A,norm_neg,Fintype.card_fin] using hLn
  · intro v w;change inner ℝ v (-(L w))=inner ℝ (-(L v)) w
    rw [inner_neg_left,inner_neg_right,hLs]
  · intro v;change 0 ≤ inner ℝ v (-(L v));rw [inner_neg_right];exact hLpos v
  · intro f hf;rw [hbilA];congr 1;apply Finset.sum_congr rfl;intro i hi
    apply integral_congr_ae;exact Eventually.of_forall fun q => by dsimp [delta];ring
  · intro Q hQ;apply ContinuousLinearMap.ext;intro v;apply Lp.ext
    have hq := hQ.2.2.2.1 v (Lp.memLp v)
    have ha := hreprA v (Lp.memLp v)
    simp only [Lp.toLp_coeFn] at hq ha;exact hq.trans ha.symm
