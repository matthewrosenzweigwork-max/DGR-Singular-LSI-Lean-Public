module

public import Tablet.NativeGibbsBochner
public import Tablet.NativeGibbsJumpKernel
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Tactic

@[expose] public section
open MeasureTheory Filter Set
open scoped InnerProduct InnerProductSpace ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

-- [TABLET NODE: NativeGibbsLargeNJumpGap]
theorem NativeGibbsLargeNJumpGap (d : ℕ) (hd : 3 ≤ d) (s B κ L M1 : ℝ)
    (hs : 0 < s) (hsd : s ≤ (d:ℝ)-2) (hB : 0 ≤ B) (hκ : 0 < κ) (hL : 1 ≤ L) :
    ∃ γ : ℝ,0 < γ ∧ ∃ N_B : ℕ,2 ≤ N_B ∧
      ∀ (V b : OneParticle d → ℝ),Continuous V → BoundedMultiplier d L b →
        (∀ x,κ/2*‖x‖^2 ≤ V x-V 0) → (∀ x,‖x‖ ≤ 1 → V x-V 0 ≤ M1) →
      ∀ N : ℕ,N_B ≤ N → ∀ coupling ε : ℝ,
        0 ≤ coupling → coupling ≤ B → 0 < ε →
      let μ := ReferenceLaw V b
      let P := GibbsLaw (N:=N) μ s coupling ε
      let U := fun (X : ParticleConfig d N) (i : Fin N) (z : OneParticle d) =>
        ∑ j ∈ Finset.univ.erase i,(coupling/(N:ℝ))*RieszKernel s ε (z-ParticlePosition X j)
      let J := fun i => (P.prod μ).withDensity (fun q => ENNReal.ofReal (Real.exp (-U q.1 i q.2)))
      ∀ (f : ParticleConfig d N → ℝ),MemLp f 2 P →
        γ*ProbabilityTheory.variance f P ≤
          (1/2:ℝ)*∑ i : Fin N,∫ q,(f (ParticleInsertion q.1 i q.2)-f q.1)^2 ∂J i := by
-- BODY
  classical
  have NonnegativeOperatorGap {H : Type} [NormedAddCommGroup H]
      [InnerProductSpace ℝ H] [CompleteSpace H]
      (A : H →L[ℝ] H) (δ : ℝ) (hδ : 0 < δ)
      (hself : ∀ v w, inner ℝ v (A w) = inner ℝ (A v) w)
      (hpos : ∀ v, 0 ≤ inner ℝ v (A v))
      (hquad : ∀ v, δ * inner ℝ v (A v) ≤ ‖A v‖^2) :
      ∀ v, (∀ w, A w = 0 → inner ℝ v w = 0) →
        δ * ‖v‖^2 ≤ inner ℝ v (A v) := by
    intro v hv
    have hvorth : v ∈ (LinearMap.ker A.toLinearMap)ᗮ := by
      rw [Submodule.mem_orthogonal']
      intro w hw
      exact hv w hw
    have hrange (w : H) : δ * ‖A w‖ ^ 2 ≤ inner ℝ (A w) (A (A w)) := by
      have hp := hpos (A w - δ • w)
      have hexpand : inner ℝ (A w - δ • w) (A (A w - δ • w)) =
          inner ℝ (A w) (A (A w)) - 2 * δ * ‖A w‖ ^ 2 +
            δ ^ 2 * inner ℝ w (A w) := by
        simp only [map_sub, map_smul, inner_sub_left, inner_sub_right,
          inner_smul_left, inner_smul_right, RCLike.conj_to_real]
        rw [hself w (A w), real_inner_self_eq_norm_sq]
        ring
      rw [hexpand] at hp
      have hm := mul_le_mul_of_nonneg_left (hquad w) hδ.le
      nlinarith
    have hs : A.toLinearMap.IsSymmetric := fun x y => (hself x y).symm
    have hclosure : (LinearMap.range A.toLinearMap).topologicalClosure =
        (LinearMap.ker A.toLinearMap)ᗮ := by
      rw [← Submodule.orthogonal_orthogonal_eq_closure, hs.orthogonal_range]
    have hclosed : IsClosed {x : H | δ * ‖x‖ ^ 2 ≤ inner ℝ x (A x)} :=
      isClosed_le (continuous_const.mul (continuous_norm.pow 2))
        (continuous_id.inner A.continuous)
    have hincl : (LinearMap.range A.toLinearMap : Set H) ⊆
        {x : H | δ * ‖x‖ ^ 2 ≤ inner ℝ x (A x)} := by
      rintro x ⟨w, rfl⟩
      exact hrange w
    have hvclosure : v ∈ closure (LinearMap.range A.toLinearMap : Set H) := by
      rw [← Submodule.topologicalClosure_coe, hclosure]
      exact hvorth
    exact closure_minimal hincl hclosed hvclosure
  
  
  have probability_gap {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (L : Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P) (δ : ℝ) (hδ : 0 < δ)
      (hself : ∀v w,inner ℝ v (L w)=inner ℝ (L v) w)
      (hpos : ∀v,0 ≤ -inner ℝ v (L v))
      (hquad : ∀v,δ*(-inner ℝ v (L v)) ≤ ‖L v‖^2)
      (hker : ∀v,L v=0 ↔ ∃c:ℝ,∀ᵐx∂P,v x=c)
      (f : Ω→ℝ) (hf : MemLp f 2 P) :
      δ*ProbabilityTheory.variance f P ≤ -inner ℝ (hf.toLp f) (L (hf.toLp f)) := by
    let c := ∫x,f x∂P
    let g := fun x => f x-c
    have hc : MemLp (fun _:Ω => c) 2 P := memLp_const c
    have hg : MemLp g 2 P := hf.sub hc
    let v := hf.toLp f
    let w := hc.toLp (fun _:Ω=>c)
    let v₀ := hg.toLp g
    have hsub : v₀ = v-w := by exact hf.toLp_sub hc
    have hw : L w=0 := (hker w).2 ⟨c,hc.coeFn_toLp⟩
    have hLv : L v₀=L v := by rw [hsub,map_sub,hw,sub_zero]
    have hmean : ∫x,g x∂P=0 := by
      dsimp [g,c]
      rw [integral_sub (hf.integrable (by norm_num)) (integrable_const _)]
      simp
    let A := -L
    have hselfA : ∀v w,inner ℝ v (A w)=inner ℝ (A v) w := by
      intro v w; simpa [A] using congrArg Neg.neg (hself v w)
    have hposA : ∀v,0 ≤ inner ℝ v (A v) := by intro v; simpa [A] using hpos v
    have hquadA : ∀v,δ*inner ℝ v (A v) ≤ ‖A v‖^2 := by intro v; simpa [A] using hquad v
    have horth : ∀w,A w=0 → inner ℝ v₀ w=0 := by
      intro w hw
      have hwL : L w=0 := by simpa [A] using hw
      obtain ⟨b,hb⟩ := (hker w).1 hwL
      rw [L2.inner_def]
      have he : (fun x => inner ℝ (v₀ x) (w x)) =ᵐ[P] fun x => g x*b := by
        filter_upwards [hg.coeFn_toLp,hb] with x hx hy
        simp [v₀,hx,hy,mul_comm]
      rw [integral_congr_ae he,integral_mul_const,hmean,zero_mul]
    have hh := NonnegativeOperatorGap A δ hδ hselfA hposA hquadA v₀ horth
    have hnorm : ‖v₀‖^2 = ProbabilityTheory.variance f P := by
      rw [← real_inner_self_eq_norm_sq,L2.inner_def]
      have he : (fun x => inner ℝ (v₀ x) (v₀ x)) =ᵐ[P] fun x => (f x-c)^2 := by
        filter_upwards [hg.coeFn_toLp] with x hx
        simp [v₀,hx,g,pow_two]
      rw [integral_congr_ae he]
      simpa [c] using (ProbabilityTheory.variance_eq_integral hf.aestronglyMeasurable.aemeasurable).symm
    have hpair : inner ℝ v₀ (L v₀)=inner ℝ v (L v) := by
      rw [hLv,hsub,inner_sub_left]
      rw [hself w v,hw,inner_zero_left,sub_zero]
    simpa [A,hnorm,hpair,v] using hh
  obtain ⟨C,hC,hsmall⟩ := NativeGibbsBochner d hd s B κ L M1 hs hsd hB hκ hL
  let e := Real.exp (-(B*C))
  let η := e/(8*(B+1))
  have he : 0 < e := Real.exp_pos _
  have hη : 0 < η := div_pos he (by positivity)
  obtain ⟨a₀,ha₀,hmodels⟩ := hsmall η hη
  let a₁ := min a₀ (e/(8*(C+1)))
  have ha₁ : 0 < a₁ := lt_min ha₀ (div_pos he (by positivity))
  obtain ⟨K,hK⟩ := exists_nat_gt (B/a₁)
  refine ⟨e/2,by positivity,K+2,by omega,?_⟩
  intro V b hV hb hquad hlocal N hNN coupling ε hc hcB hε
  dsimp only
  let μ := ReferenceLaw V b
  let P := GibbsLaw (N:=N) μ s coupling ε
  let U := fun (X : ParticleConfig d N) (i : Fin N) (z : OneParticle d) =>
    ∑ j ∈ Finset.univ.erase i,(coupling/(N:ℝ))*RieszKernel s ε (z-ParticlePosition X j)
  let J := fun i => (P.prod μ).withDensity (fun q => ENNReal.ofReal (Real.exp (-U q.1 i q.2)))
  let energy := fun f : ParticleConfig d N → ℝ => (1/2:ℝ)*∑ i : Fin N,∫ q,
    (f (ParticleInsertion q.1 i q.2)-f q.1)^2 ∂J i
  let raw := fun (f : ParticleConfig d N → ℝ) X => ∑ i : Fin N,∫ z,
    Real.exp (-U X i z)*(f (ParticleInsertion X i z)-f X) ∂μ
  have hN : 2 ≤ N := by omega
  have hNp : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hKN : (K:ℝ) ≤ (N:ℝ) := by exact_mod_cast (show K ≤ N by omega)
  have hratio : coupling/(N:ℝ) ≤ a₁ := by
    apply (div_le_iff₀ hNp).mpr
    have h := (div_lt_iff₀ ha₁).mp (hK.trans_le hKN)
    nlinarith only [h,hcB]
  have hratio₀ : coupling/(N:ℝ) ≤ a₀ := hratio.trans (min_le_left _ _)
  have hfirst : 2*coupling*η ≤ e/4 := by
    dsimp only [η];rw [←mul_div_assoc]
    apply (div_le_iff₀ (show 0 < 8*(B+1) by positivity)).mpr
    nlinarith only [he,hB,hc,hcB]
  have hsecond : 2*(coupling/(N:ℝ))*C ≤ e/4 := by
    have hb := hratio.trans (min_le_right _ _)
    have h := (le_div_iff₀ (show 0 < 8*(C+1) by positivity)).mp hb
    have hn := div_nonneg hc hNp.le
    nlinarith only [h,hn,he]
  have hcoeff : e/2 ≤ Real.exp (-(B*C))-2*(coupling*η+(coupling/(N:ℝ))*C) := by
    dsimp only [e] at *;linarith only [hfirst,hsecond]
  obtain ⟨D,hD,href⟩ := ReferenceOffsetDensity d (by omega) s κ L M1 hs (by linarith) hκ hL
  haveI : IsProbabilityMeasure μ := (href V b hV hb hquad hlocal).2.2.1
  haveI : IsProbabilityMeasure P := (SoftGibbsNormalization μ s coupling ε hs hc hε).2.2
  obtain ⟨A,hA,_⟩ := NativeGibbsJumpOperator d N μ s coupling ε hs hc hε
  have hrepr := hA.2.2.2.1
  have hE := hA.2.2.2.2.2
  have hEn (g : ParticleConfig d N → ℝ) : 0 ≤ energy g :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun i hi => integral_nonneg fun q => sq_nonneg _)
  have hnorm (v : Lp ℝ 2 P) : ‖A v‖^2=∫ X,(raw v X)^2 ∂P := by
    rw [←real_inner_self_eq_norm_sq,L2.inner_def]
    have hr := hrepr v (Lp.memLp v);simp only [Lp.toLp_coeFn] at hr
    apply integral_congr_ae
    filter_upwards [hr] with X hX
    have he (X : ParticleConfig d N) : (∑ i : Fin N,∫ z,
        Real.exp (-U X i z)*(v X-v (ParticleInsertion X i z)) ∂μ)= -raw v X := by
      dsimp only [raw];rw [←Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl;intro i hi
      rw [←integral_neg]
      apply integral_congr_ae;exact Eventually.of_forall fun z => by ring
    rw [hX,he];simp [pow_two]
  let L := -A
  have hLs (v w : Lp ℝ 2 P) : inner ℝ v (L w)=inner ℝ (L v) w := by
    change inner ℝ v (-(A w))=inner ℝ (-(A v)) w
    rw [inner_neg_left,inner_neg_right,hA.2.1]
  have hLpos (v : Lp ℝ 2 P) : 0 ≤ -inner ℝ v (L v) := by
    change 0 ≤ -inner ℝ v (-(A v));rw [inner_neg_right,neg_neg];exact hA.2.2.1 v
  have hLquad (v : Lp ℝ 2 P) : (e/2)*(-inner ℝ v (L v)) ≤ ‖L v‖^2 := by
    change (e/2)*(-inner ℝ v (-(A v))) ≤ ‖-(A v)‖^2
    rw [inner_neg_right,neg_neg,norm_neg,hnorm]
    have hvE := hE v (Lp.memLp v);simp only [Lp.toLp_coeFn] at hvE
    rw [hvE]
    exact (mul_le_mul_of_nonneg_right hcoeff (hEn v)).trans
      (hmodels V b hV hb hquad hlocal N hN coupling ε hc hcB hε hratio₀ v (Lp.memLp v))
  have hLker (v : Lp ℝ 2 P) : L v=0 ↔ ∃ c : ℝ,∀ᵐ X ∂P,v X=c := by
    change -(A v)=0 ↔ _
    rw [neg_eq_zero]
    simpa only [Lp.toLp_coeFn] using NativeGibbsJumpKernel d N μ s coupling ε hs hc hε A hrepr v (Lp.memLp v)
  intro f hf
  have hgap := probability_gap P L (e/2) (by positivity) hLs hLpos hLquad hLker f hf
  change (e/2)*ProbabilityTheory.variance f P ≤ _
  have heq := hE f hf
  change inner ℝ (hf.toLp f) (A (hf.toLp f))=energy f at heq
  have hgap' : (e/2)*ProbabilityTheory.variance f P ≤ inner ℝ (hf.toLp f) (A (hf.toLp f)) := by
    simpa only [L,ContinuousLinearMap.neg_apply,inner_neg_right,neg_neg] using hgap
  exact hgap'.trans_eq heq
