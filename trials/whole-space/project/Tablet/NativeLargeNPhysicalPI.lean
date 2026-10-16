module

public import Tablet.NativeGibbsLargeNJumpGap
public import Tablet.GibbsJumpPhysicalComparison
public import Tablet.LawVariance

@[expose] public section
open MeasureTheory Filter Set
open scoped ENNReal BigOperators ContDiff
set_option autoImplicit false
set_option maxHeartbeats 2000000

-- [TABLET NODE: NativeLargeNPhysicalPI]
theorem NativeLargeNPhysicalPI (d : ℕ) (hd : 3 ≤ d) (s B κ L : ℝ)
    (hs : 0 < s) (hsd : s ≤ (d:ℝ)-2) (hB : 0 ≤ B) (hκ : 0 < κ) (hL : 1 ≤ L)
    (Ca Mloc : ℝ → ℝ) :
    ∃ ρ : ℝ,0 < ρ ∧ ∃ N_B : ℕ,2 ≤ N_B ∧
      ∀ V : OneParticle d → ℝ,PotentialBounds d κ V → (∀ x,V 0 ≤ V x) →
        (∀ R : ℝ,0 < R → ∀ x,‖x‖ ≤ R → V x-V 0 ≤ Mloc R) →
        (∀ a : ℝ,0 < a → ∀ x,EuclideanLaplacian V x ≤
          a*‖EuclideanGradient V x‖^(2/(s+1))+Ca a) →
      ∀ b : OneParticle d → ℝ,BoundedMultiplier d L b →
      ∀ N : ℕ,N_B ≤ N → ∀ coupling ε : ℝ,0 ≤ coupling → coupling ≤ B → 0 < ε →
      let P := GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε
      ∀ f : ParticleConfig d N → ℝ,ContDiff ℝ ∞ f → HasCompactSupport f →
        ρ*LawVariance P f ≤ PhysicalEnergy P f := by
-- BODY
  classical
  obtain ⟨γ,hγ,N_B,hNB,hgap⟩ := NativeGibbsLargeNJumpGap d hd s B κ L (Mloc 1) hs hsd hB hκ hL
  obtain ⟨σ,hσ,hphysical⟩ := GibbsJumpPhysicalComparison d hd s B κ L hs hsd hB hκ hL Ca Mloc
  refine ⟨σ*γ,mul_pos hσ hγ,N_B,hNB,?_⟩
  intro V hV hmin hM hgrowth b hb N hNN coupling ε hc hcB hε
  dsimp only
  let μ := ReferenceLaw V b
  let P := GibbsLaw (N:=N) μ s coupling ε
  have hN : 2 ≤ N := hNB.trans hNN
  obtain ⟨a,_,huniq,_,hq,_⟩ := (HessianMinimizer V κ hκ hV).2
  have hz : (0 : OneParticle d)=a := huniq 0 hmin
  subst a
  have hquad (x : OneParticle d) : κ/2*‖x‖^2 ≤ V x-V 0 := by
    have h := hq x
    simp only [sub_zero] at h
    linarith
  have hlocal := hM 1 (by norm_num)
  haveI : IsProbabilityMeasure μ := (ConvexReferenceNormalization V b κ L hκ hV hb).2.2
  haveI : IsProbabilityMeasure P := (SoftGibbsNormalization μ s coupling ε hs hc hε).2.2
  intro f hf hfc
  have hfLp : MemLp f 2 P := hf.continuous.memLp_of_hasCompactSupport hfc
  have hg := hgap V b hV.regularity.continuous hb hquad hlocal N hNN coupling ε hc hcB hε f hfLp
  have hp := hphysical V hV hmin hM hgrowth b hb N hN coupling ε hc hcB hε f hf hfc
  change (σ*γ)*ProbabilityTheory.variance f P ≤ PhysicalEnergy P f
  calc
    _ = σ*(γ*ProbabilityTheory.variance f P) := by ring
    _ ≤ σ*((1/2:ℝ)*∑ i : Fin N,∫ q,(f (ParticleInsertion q.1 i q.2)-f q.1)^2
        ∂(P.prod μ).withDensity (fun q => ENNReal.ofReal (Real.exp
          (-(∑ j ∈ Finset.univ.erase i,(coupling/(N:ℝ))*RieszKernel s ε (q.2-ParticlePosition q.1 j)))))) :=
      mul_le_mul_of_nonneg_left hg hσ.le
    _ ≤ PhysicalEnergy P f := hp
