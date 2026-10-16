import Tablet.BoundedHessianAllCutoffsClosedPI
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
noncomputable section
namespace WholeSpaceCollective
theorem common (d : ℕ) (hd : 3 ≤ d) (s B : ℝ) (hs : 0 < s) (hsd : s ≤ (d:ℝ)-2) (hB : 0 ≤ B) : ∀ (κ L : ℝ), 0 < κ → 1 ≤ L → ∀ (Ca Mloc : ℝ → ℝ),
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ V : OneParticle d → ℝ,
      GrowthClassPotential d s κ Mloc Ca V →
      ∀ b : OneParticle d → ℝ, BoundedMultiplier d L b →
      ∀ N : ℕ, 2 ≤ N → ∀ coupling ε : ℝ,
        0 ≤ coupling → coupling ≤ B → 0 ≤ ε →
      ∀ q ∈ ClosedGradientGraph (GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε),
        ρ*LawVariance (GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε) q.1 ≤
          ClosedPhysicalEnergy q := by
  intro κ L hκ hL Ca Mloc
  obtain ⟨rp,hrp,hp⟩ := (GrowthClassPositiveCutoffClosedPI d hd s B hs hsd hB).1 κ L hκ hL Ca Mloc
  obtain ⟨rz,hrz,hz⟩ := (GrowthClassZeroCutoffClosedPI d hd s B hs hsd hB).1 κ L hκ hL Ca Mloc
  refine ⟨min rp rz,lt_min hrp hrz,?_⟩
  intro V hV b hb N hN coupling ε hc hcB hε q hq
  have hv : 0 ≤ LawVariance (GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε) q.1 := ProbabilityTheory.variance_nonneg _ _
  by_cases he : ε = 0
  · exact (mul_le_mul_of_nonneg_right (min_le_right rp rz) hv).trans
      (hz V hV b hb N hN coupling ε hc hcB he q hq)
  · exact (mul_le_mul_of_nonneg_right (min_le_left rp rz) hv).trans
      (hp V hV b hb N hN coupling ε hc hcB (lt_of_le_of_ne hε (Ne.symm he)) q hq)
theorem fixed (d : ℕ) (hd : 3 ≤ d) (s B : ℝ) (hs : 0 < s) (hsd : s ≤ (d:ℝ)-2) (hB : 0 ≤ B) : ∀ (κ L : ℝ), 0 < κ → 1 ≤ L →
    ∀ (V : OneParticle d → ℝ) (hV : ContDiff ℝ 2 V)
    (hH : ∀ x u, κ*‖u‖^2 ≤ EuclideanHessian V x u u)
    (hGrowth : ∀ a : ℝ, 0 < a → ∃ C : ℝ, ∀ x,
      EuclideanLaplacian V x ≤ a*‖EuclideanGradient V x‖^(2/(s+1))+C),
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ b : OneParticle d → ℝ, BoundedMultiplier d L b →
      ∀ coupling ε : ℝ, 0 ≤ coupling → coupling ≤ B → 0 ≤ ε →
      ∀ q ∈ ClosedGradientGraph (GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε),
        ρ*LawVariance (GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε) q.1 ≤
          ClosedPhysicalEnergy q := by
  intro κ L hκ hL V hV hH hGrowth
  obtain ⟨rp,hrp,hp⟩ := (GrowthClassPositiveCutoffClosedPI d hd s B hs hsd hB).2.1 κ L hκ hL V hV hH hGrowth
  obtain ⟨rz,hrz,hz⟩ := (GrowthClassZeroCutoffClosedPI d hd s B hs hsd hB).2.1 κ L hκ hL V hV hH hGrowth
  refine ⟨min rp rz,lt_min hrp hrz,?_⟩
  intro N hN b hb coupling ε hc hcB hε q hq
  have hv : 0 ≤ LawVariance (GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε) q.1 := ProbabilityTheory.variance_nonneg _ _
  by_cases he : ε = 0
  · exact (mul_le_mul_of_nonneg_right (min_le_right rp rz) hv).trans
      (hz N hN b hb coupling ε hc hcB he q hq)
  · exact (mul_le_mul_of_nonneg_right (min_le_left rp rz) hv).trans
      (hp N hN b hb coupling ε hc hcB (lt_of_le_of_ne hε (Ne.symm he)) q hq)
theorem gaussian (d : ℕ) (hd : 3 ≤ d) (s B : ℝ) (hs : 0 < s) (hsd : s ≤ (d:ℝ)-2) (hB : 0 ≤ B) :     ∃ ρ : ℝ, 0 < ρ ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ coupling ε : ℝ, 0 ≤ coupling → coupling ≤ B → 0 ≤ ε →
      ∀ q ∈ ClosedGradientGraph
        (GibbsLaw (N:=N) (ProbabilityTheory.stdGaussian (OneParticle d)) s coupling ε),
        ρ*LawVariance
          (GibbsLaw (N:=N) (ProbabilityTheory.stdGaussian (OneParticle d)) s coupling ε) q.1 ≤
            ClosedPhysicalEnergy q := by
  skip
  obtain ⟨rp,hrp,hp⟩ := (GrowthClassPositiveCutoffClosedPI d hd s B hs hsd hB).2.2 
  obtain ⟨rz,hrz,hz⟩ := (GrowthClassZeroCutoffClosedPI d hd s B hs hsd hB).2.2 
  refine ⟨min rp rz,lt_min hrp hrz,?_⟩
  intro N hN coupling ε hc hcB hε q hq
  have hv : 0 ≤ LawVariance (GibbsLaw (N:=N) (ProbabilityTheory.stdGaussian (OneParticle d)) s coupling ε) q.1 := ProbabilityTheory.variance_nonneg _ _
  by_cases he : ε = 0
  · exact (mul_le_mul_of_nonneg_right (min_le_right rp rz) hv).trans
      (hz N hN coupling ε hc hcB he q hq)
  · exact (mul_le_mul_of_nonneg_right (min_le_left rp rz) hv).trans
      (hp N hN coupling ε hc hcB (lt_of_le_of_ne hε (Ne.symm he)) q hq)
theorem allCutoffs (d : ℕ) (hd : 3 ≤ d) (s B : ℝ)
    (hs : 0 < s) (hsd : s ≤ (d:ℝ)-2) (hB : 0 ≤ B) :
    (∀ (κ L : ℝ), 0 < κ → 1 ≤ L → ∀ (Ca Mloc : ℝ → ℝ),
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ V : OneParticle d → ℝ,
      GrowthClassPotential d s κ Mloc Ca V →
      ∀ b : OneParticle d → ℝ, BoundedMultiplier d L b →
      ∀ N : ℕ, 2 ≤ N → ∀ coupling ε : ℝ,
        0 ≤ coupling → coupling ≤ B → 0 ≤ ε →
      ∀ q ∈ ClosedGradientGraph (GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε),
        ρ*LawVariance (GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε) q.1 ≤
          ClosedPhysicalEnergy q) ∧
    (∀ (κ L : ℝ), 0 < κ → 1 ≤ L →
    ∀ (V : OneParticle d → ℝ) (hV : ContDiff ℝ 2 V)
    (hH : ∀ x u, κ*‖u‖^2 ≤ EuclideanHessian V x u u)
    (hGrowth : ∀ a : ℝ, 0 < a → ∃ C : ℝ, ∀ x,
      EuclideanLaplacian V x ≤ a*‖EuclideanGradient V x‖^(2/(s+1))+C),
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ b : OneParticle d → ℝ, BoundedMultiplier d L b →
      ∀ coupling ε : ℝ, 0 ≤ coupling → coupling ≤ B → 0 ≤ ε →
      ∀ q ∈ ClosedGradientGraph (GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε),
        ρ*LawVariance (GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε) q.1 ≤
          ClosedPhysicalEnergy q) ∧
    (∀ (κ K L : ℝ), 0 < κ → κ ≤ K → 1 ≤ L →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ V : OneParticle d → ℝ, TwoSidedPotential d κ K V →
      ∀ b : OneParticle d → ℝ, BoundedMultiplier d L b →
      ∀ N : ℕ, 2 ≤ N → ∀ coupling ε : ℝ,
        0 ≤ coupling → coupling ≤ B → 0 ≤ ε →
      ∀ q ∈ ClosedGradientGraph (GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε),
        ρ*LawVariance (GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε) q.1 ≤
          ClosedPhysicalEnergy q) ∧
    (    ∃ ρ : ℝ, 0 < ρ ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ coupling ε : ℝ, 0 ≤ coupling → coupling ≤ B → 0 ≤ ε →
      ∀ q ∈ ClosedGradientGraph
        (GibbsLaw (N:=N) (ProbabilityTheory.stdGaussian (OneParticle d)) s coupling ε),
        ρ*LawVariance
          (GibbsLaw (N:=N) (ProbabilityTheory.stdGaussian (OneParticle d)) s coupling ε) q.1 ≤
            ClosedPhysicalEnergy q) := by
  exact ⟨common d hd s B hs hsd hB,fixed d hd s B hs hsd hB,
    fun κ K L hκ hκK hL => BoundedHessianAllCutoffsClosedPI d hd s B κ K L hs hsd hB hκ hκK hL,
    gaussian d hd s B hs hsd hB⟩
end WholeSpaceCollective
