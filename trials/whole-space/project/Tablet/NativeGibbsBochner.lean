import Tablet.WeightedJointRowL2
import Tablet.NativeGibbsMayerContribution
import Tablet.NativeGibbsSameLabel
import Tablet.NativeGibbsFourCorner
import Mathlib.Tactic
open MeasureTheory Filter Set
open scoped ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

-- [TABLET NODE: NativeGibbsBochner]
theorem NativeGibbsBochner (d : ℕ) (hd : 3 ≤ d) (s B κ L M1 : ℝ)
    (hs : 0 < s) (hsd : s ≤ (d:ℝ)-2) (hB : 0 ≤ B) (hκ : 0 < κ) (hL : 1 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → ∃ a₀ : ℝ, 0 < a₀ ∧
      ∀ (V b : OneParticle d → ℝ), Continuous V → BoundedMultiplier d L b →
        (∀ x,κ/2*‖x‖^2 ≤ V x-V 0) → (∀ x,‖x‖ ≤ 1 → V x-V 0 ≤ M1) →
      ∀ N : ℕ,2 ≤ N → ∀ coupling ε : ℝ,
        0 ≤ coupling → coupling ≤ B → 0 < ε → coupling/(N:ℝ) ≤ a₀ →
      let μ := ReferenceLaw V b
      let P := GibbsLaw (N:=N) μ s coupling ε
      let U := fun (X : ParticleConfig d N) (i : Fin N) (z : OneParticle d) =>
        ∑ j ∈ Finset.univ.erase i,(coupling/(N:ℝ))*RieszKernel s ε (z-ParticlePosition X j)
      let J := fun i => (P.prod μ).withDensity (fun q => ENNReal.ofReal (Real.exp (-U q.1 i q.2)))
      ∀ (f : ParticleConfig d N → ℝ),MemLp f 2 P →
        (Real.exp (-(B*C))-2*(coupling*δ+(coupling/(N:ℝ))*C))*
          ((1/2:ℝ)*∑ i : Fin N,∫ q,(f (ParticleInsertion q.1 i q.2)-f q.1)^2 ∂J i) ≤
        ∫ X,(∑ i : Fin N,∫ z,Real.exp (-U X i z)*(f (ParticleInsertion X i z)-f X) ∂μ)^2 ∂P := by
-- BODY
  classical
  obtain ⟨C,hC,hsmall⟩ := NativeGibbsMayerContribution d hd s B κ L M1 hs hsd hB hκ hL
  refine ⟨C,hC,?_⟩
  intro δ hδ
  obtain ⟨a₀,ha₀,hmodels⟩ := hsmall δ hδ
  refine ⟨a₀,ha₀,?_⟩
  intro V b hV hb hquad hlocal N hN coupling ε hc hcB hε ha₀bound
  dsimp only
  let μ := ReferenceLaw V b
  let P := GibbsLaw (N:=N) μ s coupling ε
  let a := coupling/(N:ℝ)
  let U := fun (X : ParticleConfig d N) (i : Fin N) (z : OneParticle d) =>
    ∑ j ∈ Finset.univ.erase i,a*RieszKernel s ε (z-ParticlePosition X j)
  let Z := fun X i => ∫ z,Real.exp (-U X i z) ∂μ
  let ν := fun X i => ReferenceLaw (fun z => V z+U X i z) b
  let J := fun i => (P.prod μ).withDensity (fun q => ENNReal.ofReal (Real.exp (-U q.1 i q.2)))
  obtain ⟨D,hD,href⟩ := ReferenceOffsetDensity d (by omega) s κ L M1 hs (by linarith) hκ hL
  haveI : IsProbabilityMeasure μ := (href V b hV hb hquad hlocal).2.2.1
  haveI : IsProbabilityMeasure P := (SoftGibbsNormalization μ s coupling ε hs hc hε).2.2
  have hmodel := hmodels V b hV hb hquad hlocal N hN coupling ε hc hcB hε ha₀bound
  intro f hf
  let F := fun (X : ParticleConfig d N) (i : Fin N) (z : OneParticle d) =>
    Real.exp (-U X i z)*(f (ParticleInsertion X i z)-f X)
  let A := fun i X => ∫ z,F X i z ∂μ
  let E := fun i j X => ∫ z,∫ v,Real.exp (-a*RieszKernel s ε (z-v))*F X i z*F X j v ∂μ ∂μ
  let M := fun i j X => ∫ z,∫ v,(1-Real.exp (-a*RieszKernel s ε (z-v)))*F X i z*F X j v ∂μ ∂μ
  have ht := NativeGibbsTransformedL2 d N μ s coupling ε hs hc hε f hf
  have hAm (i : Fin N) : MemLp (A i) 2 P := by
    have hw := WeightedJointRowL2 P μ (fun _ : ParticleConfig d N × OneParticle d => (1:ℝ))
      measurable_const (fun _ => ⟨zero_le_one,le_rfl⟩) (fun q => F q.1 i q.2)
      (by simpa only [ENNReal.ofReal_one,withDensity_const,one_smul] using (ht.1 i).1)
    simpa only [one_mul] using hw.2.2.1
  have hEi (i j : Fin N) : Integrable (E i j) P :=
    (ht.2.2 i j).1.integral_prod_left.integral_prod_left
  have hMi (i j : Fin N) : Integrable (M i j) P :=
    (ht.2.2 i j).2.integral_prod_left.integral_prod_left
  have hcross (i j : Fin N) : (∫ X,A i X*A j X ∂P)=(∫ X,E i j X ∂P)+(∫ X,M i j X ∂P) := by
    let Q := (P.prod μ).prod μ
    let g := fun q : (ParticleConfig d N × OneParticle d) × OneParticle d =>
      Real.exp (-a*RieszKernel s ε (q.1.2-q.2))*F q.1.1 i q.1.2*F q.1.1 j q.2
    let m := fun q : (ParticleConfig d N × OneParticle d) × OneParticle d =>
      (1-Real.exp (-a*RieszKernel s ε (q.1.2-q.2)))*F q.1.1 i q.1.2*F q.1.1 j q.2
    have hg : Integrable g Q := (ht.2.2 i j).1
    have hm : Integrable m Q := (ht.2.2 i j).2
    have hsum : (fun q => g q+m q)=fun q =>F q.1.1 i q.1.2*F q.1.1 j q.2 := by
      funext q;dsimp only [g,m];ring
    have hgi : Integrable (fun q : (ParticleConfig d N × OneParticle d) × OneParticle d =>
        F q.1.1 i q.1.2*F q.1.1 j q.2) Q := by rw [←hsum];exact hg.add hm
    calc
      _ = ∫ q,F q.1.1 i q.1.2*F q.1.1 j q.2 ∂Q := by
        rw [integral_prod _ hgi,integral_prod _ hgi.integral_prod_left]
        apply integral_congr_ae;exact Eventually.of_forall fun X => by
          simp only [integral_const_mul,integral_mul_const,A]
      _ = (∫ q,g q ∂Q)+(∫ q,m q ∂Q) := by rw [←hsum];exact integral_add hg hm
      _ = _ := by rw [integral_prod _ hg,integral_prod _ hg.integral_prod_left,
        integral_prod _ hm,integral_prod _ hm.integral_prod_left]
  have hrectangle (i j : Fin N) (hij : i ≠ j) : 0 ≤ ∫ X,E i j X ∂P :=
    (NativeGibbsFourCorner d N μ s coupling ε hs hc hε i j hij f hf).2.2.2.2
  have hdiag (i : Fin N) := NativeGibbsSameLabel d hd s B κ L M1 hs hsd hB hκ hL
    V b hV hb hquad hlocal N hN coupling ε hc hcB hε f hf i
  have hvar := (NativeGibbsJumpVariance d hd s B κ L M1 hs hsd hB hκ hL
    V b hV hb hquad hlocal N hN coupling ε hc hcB hε).2 f hf
  have hVI (i : Fin N) : Integrable (fun X => Z X i*
      ProbabilityTheory.variance (fun z => f (ParticleInsertion X i z)) (ν X i)) P := hvar.2.1 i
  have hVE : (1/2:ℝ)*(∑ i : Fin N,∫ q,(f (ParticleInsertion q.1 i q.2)-f q.1)^2 ∂J i)=
      ∫ X,∑ i : Fin N,Z X i*ProbabilityTheory.variance
        (fun z => f (ParticleInsertion X i z)) (ν X i) ∂P := hvar.2.2
  have hDE (i : Fin N) : (∫ X,(A i X)^2 ∂P)=∫ X,(Z X i)^2*
      ProbabilityTheory.variance (fun z => f (ParticleInsertion X i z)) (ν X i) ∂P := (hdiag i).2
  have hDlower : Real.exp (-(B*C))*((1/2:ℝ)*∑ i : Fin N,∫ q,
      (f (ParticleInsertion q.1 i q.2)-f q.1)^2 ∂J i) ≤
      ∑ i : Fin N,∫ X,(A i X)^2 ∂P := by
    rw [hVE,integral_finsetSum _ (fun i _ => hVI i),Finset.mul_sum]
    apply Finset.sum_le_sum;intro i hi
    rw [hDE i,←integral_const_mul]
    apply integral_mono ((hVI i).const_mul _) (hdiag i).1
    intro X
    have hz : 0 ≤ Z X i := integral_nonneg fun z => Real.exp_nonneg _
    have hv := ProbabilityTheory.variance_nonneg (fun z => f (ParticleInsertion X i z)) (ν X i)
    have h := mul_le_mul_of_nonneg_right (hmodel.1 X i) (mul_nonneg hz hv)
    nlinarith only [h]
  have hMbound := (hmodel.2 f hf).2
  have hMsum : (∫ X,∑ i : Fin N,∑ j : Fin N,if i=j then (0:ℝ) else M i j X ∂P)=
      ∑ i : Fin N,∑ j : Fin N,if i=j then (0:ℝ) else ∫ X,M i j X ∂P := by
    have hOi (i j : Fin N) : Integrable (fun X => if i=j then (0:ℝ) else M i j X) P := by
      by_cases hij : i=j
      · simp only [if_pos hij];exact integrable_const _
      · simpa only [if_neg hij] using hMi i j
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hOi i j))]
    apply Finset.sum_congr rfl;intro i hi
    rw [integral_finsetSum _ (fun j _ => hOi i j)]
    apply Finset.sum_congr rfl;intro j hj
    by_cases hij : i=j <;> simp [hij]
  have hPair (i j : Fin N) : Integrable (fun X => A i X*A j X) P := (hAm i).integrable_mul (hAm j)
  have hsumSq : (∫ X,(∑ i : Fin N,A i X)^2 ∂P)=
      (∑ i : Fin N,∫ X,(A i X)^2 ∂P)+
        (∑ i : Fin N,∑ j : Fin N,if i=j then 0 else ∫ X,A i X*A j X ∂P) := by
    have he (X : ParticleConfig d N) : (∑ i : Fin N,A i X)^2=
        ∑ i : Fin N,∑ j : Fin N,A i X*A j X := by rw [pow_two,Finset.sum_mul_sum]
    simp_rw [he]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hPair i j))]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl;intro i hi
    rw [integral_finsetSum _ (fun j _ => hPair i j)]
    have hd : (∫ X,(A i X)^2 ∂P)=∑ j : Fin N,if i=j then ∫ X,A i X*A j X ∂P else 0 := by
      simp [←pow_two]
    rw [hd,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl;intro j hj
    by_cases hij : i=j <;> simp [hij]
  have hOlower : (∑ i : Fin N,∑ j : Fin N,if i=j then (0:ℝ) else ∫ X,M i j X ∂P) ≤
      ∑ i : Fin N,∑ j : Fin N,if i=j then (0:ℝ) else ∫ X,A i X*A j X ∂P := by
    apply Finset.sum_le_sum;intro i hi;apply Finset.sum_le_sum;intro j hj
    by_cases hij : i=j
    · simp only [if_pos hij,le_refl]
    · simp only [if_neg hij];rw [hcross];exact le_add_of_nonneg_left (hrectangle i j hij)
  rw [hMsum] at hMbound
  have h := hMbound.trans hOlower
  change _ ≤ ∫ X,(∑ i : Fin N,A i X)^2 ∂P
  rw [hsumSq]
  nlinarith only [hDlower,h]
