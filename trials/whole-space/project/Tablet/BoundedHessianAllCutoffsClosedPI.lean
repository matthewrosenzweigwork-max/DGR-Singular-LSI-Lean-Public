module

public import Tablet.GrowthClassPositiveCutoffClosedPI
public import Tablet.GrowthClassZeroCutoffClosedPI
public import Tablet.BoundedHessianGrowthData

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open MeasureTheory
noncomputable section
-- [TABLET NODE: BoundedHessianAllCutoffsClosedPI]
theorem BoundedHessianAllCutoffsClosedPI (d : ℕ) (hd : 3 ≤ d) (s B κ K L : ℝ)
    (hs : 0 < s) (hsd : s ≤ (d:ℝ)-2) (hB : 0 ≤ B)
    (hκ : 0 < κ) (hκK : κ ≤ K) (hL : 1 ≤ L) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ V : OneParticle d → ℝ, TwoSidedPotential d κ K V →
      ∀ b : OneParticle d → ℝ, BoundedMultiplier d L b →
      ∀ N : ℕ, 2 ≤ N → ∀ coupling ε : ℝ,
        0 ≤ coupling → coupling ≤ B → 0 ≤ ε →
      ∀ q ∈ ClosedGradientGraph (GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε),
        ρ*LawVariance (GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε) q.1 ≤
          ClosedPhysicalEnergy q := by
-- BODY
  obtain ⟨ρp,hρp,hp⟩ := (GrowthClassPositiveCutoffClosedPI d hd s B hs hsd hB).1
    κ L hκ hL (fun _ => (d:ℝ)*K) (fun R => K*R^2/2)
  obtain ⟨ρz,hρz,hz⟩ := (GrowthClassZeroCutoffClosedPI d hd s B hs hsd hB).1
    κ L hκ hL (fun _ => (d:ℝ)*K) (fun R => K*R^2/2)
  refine ⟨min ρp ρz, lt_min hρp hρz, ?_⟩
  intro V hV b hb N hN coupling ε hc hcB hε q hq
  have hclass := (BoundedHessianGrowthData V κ K s hκ hκK hV).2
  have hv : 0 ≤ LawVariance (GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε) q.1 :=
    ProbabilityTheory.variance_nonneg _ _
  by_cases he : ε = 0
  · exact (mul_le_mul_of_nonneg_right (min_le_right ρp ρz) hv).trans
      (hz V hclass b hb N hN coupling ε hc hcB he q hq)
  · exact (mul_le_mul_of_nonneg_right (min_le_left ρp ρz) hv).trans
      (hp V hclass b hb N hN coupling ε hc hcB
        (lt_of_le_of_ne hε (Ne.symm he)) q hq)
