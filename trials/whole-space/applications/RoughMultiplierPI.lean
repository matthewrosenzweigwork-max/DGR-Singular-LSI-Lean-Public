import Collective140
import Tablet.QuadraticGaussianClass
import Tablet.GibbsLaw
import Tablet.BoundedMultiplier

set_option autoImplicit false
set_option maxHeartbeats 1600000
open MeasureTheory Filter Set
open scoped ContDiff ENNReal
noncomputable section
namespace WholeSpaceAcceptedClassApplications

abbrev E := OneParticle 3

def roughHalfspaceMultiplier (L : ℝ) (x : E) : ℝ :=
  if 0 ≤ x 0 then L else 1

theorem roughHalfspaceMultiplier_measurable (L : ℝ) :
    Measurable (roughHalfspaceMultiplier L) := by
  apply Measurable.ite _ measurable_const measurable_const
  exact measurableSet_le measurable_const
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0).measurable

theorem roughHalfspaceMultiplier_bounds (L : ℝ) (hL : 1 ≤ L) (x : E) :
    1 ≤ roughHalfspaceMultiplier L x ∧ roughHalfspaceMultiplier L x ≤ L := by
  unfold roughHalfspaceMultiplier
  split_ifs <;> exact ⟨by linarith,by linarith⟩

theorem roughHalfspaceMultiplier_native (L : ℝ) (hL : 1 ≤ L) :
    BoundedMultiplier 3 L (roughHalfspaceMultiplier L) := by
  refine ⟨roughHalfspaceMultiplier_measurable L,1,L,by norm_num,hL,?_,?_⟩
  · simpa
  · exact roughHalfspaceMultiplier_bounds L hL

theorem roughHalfspaceMultiplier_origin (L : ℝ) : roughHalfspaceMultiplier L 0 = L := by
  simp [roughHalfspaceMultiplier]

theorem roughHalfspaceMultiplier_negative_basis (L : ℝ) :
    roughHalfspaceMultiplier L (-EuclideanSpace.basisFun (Fin 3) ℝ 0) = 1 := by
  simp [roughHalfspaceMultiplier,EuclideanSpace.basisFun_apply,EuclideanSpace.single_apply]

theorem roughHalfspaceMultiplier_not_continuousAt_origin (L : ℝ) (hL : 1 < L) :
    ¬ContinuousAt (roughHalfspaceMultiplier L) (0 : E) := by
  intro hc
  obtain ⟨δ,hδ,hbound⟩ := Metric.continuousAt_iff.mp hc ((L-1)/2) (by linarith)
  let y : E := -(δ/2) • EuclideanSpace.basisFun (Fin 3) ℝ 0
  have ht : -(δ/2) < 0 := by linarith
  have hy : roughHalfspaceMultiplier L y = 1 := by
    simp [y,roughHalfspaceMultiplier,EuclideanSpace.basisFun_apply,not_le_of_gt ht]
  have hdist : dist y (0:E) < δ := by
    dsimp [y]
    have he : ‖EuclideanSpace.basisFun (Fin 3) ℝ 0‖ = 1 := by
      simp [EuclideanSpace.basisFun_apply]
    rw [dist_zero_right,norm_smul,he,mul_one,
      Real.norm_eq_abs,abs_of_neg ht]
    linarith
  have hh := hbound hdist
  rw [hy,roughHalfspaceMultiplier_origin] at hh
  rw [Real.dist_eq,abs_of_neg (by linarith : 1-L < 0)] at hh
  linarith

theorem roughHalfspaceMultiplier_not_contDiff_one (L : ℝ) (hL : 1 < L) :
    ¬ContDiff ℝ 1 (roughHalfspaceMultiplier L) := by
  intro hc
  exact roughHalfspaceMultiplier_not_continuousAt_origin L hL hc.continuous.continuousAt


/-- Actual PI with a discontinuous measurable reference multiplier. -/
theorem actual_rough_multiplier_closed_PI (s B L : ℝ)
    (hs : 0<s) (hs1 : s≤1) (hB : 0≤B) (hL : 1≤L) :
    ∃ ρ : ℝ, 0<ρ ∧ ∀ N : ℕ, 2≤N → ∀ coupling ε : ℝ,
      0≤coupling → coupling≤B → 0≤ε →
      ∀ q∈ClosedGradientGraph (GibbsLaw (N:=N)
          (ReferenceLaw (fun x : E => ‖x‖^2/2) (roughHalfspaceMultiplier L)) s coupling ε),
        ρ*LawVariance (GibbsLaw (N:=N)
          (ReferenceLaw (fun x : E => ‖x‖^2/2) (roughHalfspaceMultiplier L)) s coupling ε) q.1
            ≤ ClosedPhysicalEnergy q := by
  obtain ⟨ρ,hρ,hPI⟩ := (WholeSpaceCollective.allCutoffs 3 (by norm_num) s B
    hs (by norm_num; exact hs1) hB).1 1 L zero_lt_one hL (fun _ => (3:ℝ)) (fun R => R^2/2)
  refine ⟨ρ,hρ,?_⟩
  intro N hN coupling ε hc hcB hε q hq
  exact hPI (fun x : E => ‖x‖^2/2) (QuadraticGaussianClass 3 s).2.2.2.2.2.2.2
    (roughHalfspaceMultiplier L) (roughHalfspaceMultiplier_native L hL) N hN coupling ε hc hcB hε q hq

end WholeSpaceAcceptedClassApplications
