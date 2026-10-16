import Tablet.NativeAllNRegularizedPI
import Tablet.SmoothCoreClosedPI
import Tablet.SoftGibbsNormalization
import Tablet.ConvexReferenceNormalization
import Tablet.GibbsClosedCoreEquality
import Tablet.GibbsClosedConstants
import Tablet.GibbsClosedGradientUnique
import Tablet.GrowthClassNormalization
import Tablet.ConfigurationLawTranslation
import Tablet.ConfigurationClosedGradientTransport
import Tablet.QuadraticGaussianClass
import Tablet.QuadraticGaussianReference
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped ContDiff ENNReal
noncomputable section
-- [TABLET NODE: GrowthClassPositiveCutoffClosedPI]
theorem GrowthClassPositiveCutoffClosedPI (d : ℕ) (hd : 3 ≤ d) (s B : ℝ)
    (hs : 0 < s) (hsd : s ≤ (d:ℝ)-2) (hB : 0 ≤ B) :
    (∀ (κ L : ℝ), 0 < κ → 1 ≤ L → ∀ (Ca Mloc : ℝ → ℝ),
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ V : OneParticle d → ℝ,
      GrowthClassPotential d s κ Mloc Ca V →
      ∀ b : OneParticle d → ℝ, BoundedMultiplier d L b →
      ∀ N : ℕ, 2 ≤ N → ∀ coupling ε : ℝ,
        0 ≤ coupling → coupling ≤ B → 0 < ε →
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
      ∀ coupling ε : ℝ, 0 ≤ coupling → coupling ≤ B → 0 < ε →
      ∀ q ∈ ClosedGradientGraph (GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε),
        ρ*LawVariance (GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε) q.1 ≤
          ClosedPhysicalEnergy q) ∧
    (    ∃ ρ : ℝ, 0 < ρ ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ coupling ε : ℝ, 0 ≤ coupling → coupling ≤ B → 0 < ε →
      ∀ q ∈ ClosedGradientGraph
        (GibbsLaw (N:=N) (ProbabilityTheory.stdGaussian (OneParticle d)) s coupling ε),
        ρ*LawVariance
          (GibbsLaw (N:=N) (ProbabilityTheory.stdGaussian (OneParticle d)) s coupling ε) q.1 ≤
            ClosedPhysicalEnergy q) := by
-- BODY
  classical
  have hCommon : ∀ (κ L : ℝ), 0 < κ → 1 ≤ L → ∀ (Ca Mloc : ℝ → ℝ),
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ V : OneParticle d → ℝ,
      GrowthClassPotential d s κ Mloc Ca V →
      ∀ b : OneParticle d → ℝ, BoundedMultiplier d L b →
      ∀ N : ℕ, 2 ≤ N → ∀ coupling ε : ℝ,
        0 ≤ coupling → coupling ≤ B → 0 < ε →
      ∀ q ∈ ClosedGradientGraph (GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε),
        ρ*LawVariance (GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε) q.1 ≤
          ClosedPhysicalEnergy q := by
    intro κ L hκ hL Ca Mloc
    classical
    obtain ⟨ρ,hρ,hregular⟩ := NativeAllNRegularizedPI d hd s B κ L hs hsd hB hκ hL Ca Mloc
    have hRoot : ∀ V : OneParticle d → ℝ, PotentialBounds d κ V →
        (∀ x, V 0 ≤ V x) →
        (∀ R : ℝ, 0 < R → ∀ x, ‖x‖ ≤ R → V x - V 0 ≤ Mloc R) →
        (∀ a : ℝ, 0 < a → ∀ x, EuclideanLaplacian V x ≤
          a * ‖EuclideanGradient V x‖ ^ (2 / (s + 1)) + Ca a) →
        ∀ b : OneParticle d → ℝ, BoundedMultiplier d L b →
        ∀ N : ℕ, 2 ≤ N → ∀ coupling ε : ℝ,
        0 ≤ coupling → coupling ≤ B → 0 < ε →
        ∀ q ∈ ClosedGradientGraph (GibbsLaw (N := N) (ReferenceLaw V b) s coupling ε),
          ρ * LawVariance (GibbsLaw (N := N) (ReferenceLaw V b) s coupling ε) q.1 ≤
            ClosedPhysicalEnergy q := by
      intro V hV hmin hlocal hgrowth b hb N hN coupling ε hc hcB hε q hq
      let μ := ReferenceLaw V b
      let P := GibbsLaw (N := N) μ s coupling ε
      haveI : IsProbabilityMeasure μ := (ConvexReferenceNormalization V b κ L hκ hV hb).2.2
      have hP : IsProbabilityMeasure P :=
        (SoftGibbsNormalization μ s coupling ε hs hc hε).2.2
      haveI : IsProbabilityMeasure P := hP
      have hcompact (δ : ℝ) (hδ : 0 < δ) (g : ParticleConfig d N → ℝ)
          (hgs : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
          LawVariance (GibbsLaw (N := N) μ s coupling δ) g ≤
            ρ⁻¹ * PhysicalEnergy (GibbsLaw (N := N) μ s coupling δ) g := by
        have h := (hregular V hV hmin hlocal hgrowth b hb N hN coupling δ hc hcB hδ g hgs hgc).2
        have hdiv := (le_div_iff₀ hρ).mpr (by simpa only [mul_comm] using h)
        simpa only [div_eq_mul_inv, mul_comm] using hdiv
      have hclosed : LawVariance P (q.1 : ParticleConfig d N → ℝ) ≤
          ρ⁻¹ * ClosedPhysicalEnergy q := by
        change ProbabilityTheory.variance (q.1 : ParticleConfig d N → ℝ) P ≤ ρ⁻¹ * ‖q.2‖ ^ 2
        apply SmoothCoreClosedPI P (ρ⁻¹) _ q.1 q.2 hq
        intro g hgs hgc _ _
        exact hcompact ε hε g hgs hgc
      have h := mul_le_mul_of_nonneg_left hclosed hρ.le
      calc
        ρ * LawVariance P (q.1 : ParticleConfig d N → ℝ) ≤
            ρ * (ρ⁻¹ * ClosedPhysicalEnergy q) := h
        _ = ClosedPhysicalEnergy q := by
          rw [← mul_assoc, mul_inv_cancel₀ hρ.ne', one_mul]
    refine ⟨ρ,hρ,?_⟩
    intro V hV b hb N hN coupling ε hc hcB hε
    obtain ⟨a,ha,hUnique,hZero,hMin,hCenter⟩ := GrowthClassNormalization V s κ Mloc Ca hκ hV
    obtain ⟨m,hm,hLocal⟩ := hV.localData
    have hmEq : m=a := hUnique m hm
    subst m
    let W := (ShiftedReference V b a).1
    let bc := (ShiftedReference V b a).2
    have hW : GrowthClassPotential d s κ Mloc Ca W := hCenter
    have hMinimum : ∀ x, W 0 ≤ W x := hMin
    have hLocalW : ∀ R : ℝ, 0 < R → ∀ x, ‖x‖ ≤ R → W x-W 0 ≤ Mloc R := by
      intro R hR x hx
      change (ShiftedReference V (fun _ => 1) a).1 x-
        (ShiftedReference V (fun _ => 1) a).1 0 ≤ Mloc R
      rw [hZero, sub_zero]
      exact hLocal R hR x hx
    have hGrowthW : ∀ r : ℝ, 0 < r → ∀ x,
        EuclideanLaplacian W x ≤ r*‖EuclideanGradient W x‖^(2/(s+1))+Ca r := by
      simpa only [ForceExponent] using hW.growth
    have hbc : BoundedMultiplier d L bc :=
      (CenteredPotentialDerivatives V b a).2.2.2.2.2 L hb
    have hNormalized := hRoot W hW.toPotentialBounds hMinimum hLocalW hGrowthW
      bc hbc N hN coupling ε hc hcB hε
    let P := GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε
    let e := (ConfigurationTranslation (N:=N) a).toMeasurableEquiv
    have hLaw : P.map e = GibbsLaw (N:=N) (ReferenceLaw W bc) s coupling ε :=
      (ConfigurationLawTranslation V b κ L hκ hV.toPotentialBounds hb a s coupling ε).2.2.1
    have hPIcenter : ∀ q ∈ ClosedGradientGraph (P.map e),
        ρ*LawVariance (P.map e) q.1 ≤ ClosedPhysicalEnergy q := by
      rw [hLaw]
      exact hNormalized
    have hTransport := ConfigurationClosedGradientTransport a P
    intro q hq
    have hImage : q ∈ Set.image (ConfigurationGradientPullback a P)
        (ClosedGradientGraph (P.map e)) := by
      rw [hTransport.2.1]
      exact hq
    obtain ⟨r,hr,hrq⟩ := hImage
    have hInvariant := hTransport.2.2.2.2 r
    rw [← hrq, hInvariant.1, hInvariant.2]
    exact hPIcenter r hr
  have hFixed : ∀ (κ L : ℝ), 0 < κ → 1 ≤ L →
    ∀ (V : OneParticle d → ℝ) (hV : ContDiff ℝ 2 V)
    (hH : ∀ x u, κ*‖u‖^2 ≤ EuclideanHessian V x u u)
    (hGrowth : ∀ a : ℝ, 0 < a → ∃ C : ℝ, ∀ x,
      EuclideanLaplacian V x ≤ a*‖EuclideanGradient V x‖^(2/(s+1))+C),
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ b : OneParticle d → ℝ, BoundedMultiplier d L b →
      ∀ coupling ε : ℝ, 0 ≤ coupling → coupling ≤ B → 0 < ε →
      ∀ q ∈ ClosedGradientGraph (GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε),
        ρ*LawVariance (GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε) q.1 ≤
          ClosedPhysicalEnergy q := by
    intro κ L hκ hL V hV hH hGrowth
    classical
    have hGrowth' : ∀ a : ℝ, 0 < a → ∃ C : ℝ, ∀ x,
        EuclideanLaplacian V x ≤ a*‖EuclideanGradient V x‖^ForceExponent s+C := by
      simpa only [ForceExponent] using hGrowth
    obtain ⟨m,hm,_,_,_,_⟩ := (HessianMinimizer V κ hκ ⟨hV,hH⟩).2
    have hw : Continuous (fun x => V (x+m)-V m) :=
      (hV.continuous.comp (continuous_id.add continuous_const)).sub continuous_const
    have hbound : ∀ R : ℝ, ∃ A : ℝ,
        ∀ x ∈ Metric.closedBall (0 : OneParticle d) (max R 0), ‖V (x+m)-V m‖ ≤ A := by
      intro R
      exact (isCompact_closedBall (0 : OneParticle d) (max R 0)).exists_bound_of_continuousOn hw.continuousOn
    choose A hA using hbound
    let Mloc : ℝ → ℝ := fun R => max (A R) 0
    have hlocal : ∀ R : ℝ, 0 < R → ∀ x, ‖x‖ ≤ R → V (x+m)-V m ≤ Mloc R := by
      intro R hR x hx
      have hmem : x ∈ Metric.closedBall (0 : OneParticle d) (max R 0) := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hx.trans (le_max_left R 0)
      have hnorm : |V (x+m)-V m| ≤ A R := by
        simpa only [Real.norm_eq_abs] using hA R x hmem
      exact (le_abs_self _).trans (hnorm.trans (le_max_left _ _))
    let Ca : ℝ → ℝ := fun a => if ha : 0 < a then max (Classical.choose (hGrowth' a ha)) 0 else 0
    have hgrowth : ∀ a : ℝ, 0 < a → ∀ x,
        EuclideanLaplacian V x ≤ a*‖EuclideanGradient V x‖^ForceExponent s+Ca a := by
      intro a ha x
      dsimp only [Ca]
      rw [dif_pos ha]
      exact (Classical.choose_spec (hGrowth' a ha) x).trans
        (add_le_add (le_refl _) (le_max_left _ _))
    have hclass : GrowthClassPotential d s κ Mloc Ca V :=
      ⟨⟨hV,hH⟩,⟨m,hm,hlocal⟩,hgrowth⟩
    obtain ⟨ρ,hρ,hPI⟩ := hCommon κ L hκ hL Ca Mloc
    refine ⟨ρ,hρ,?_⟩
    intro N hN b hb coupling ε hc hcB hε q hq
    exact hPI V hclass b hb N hN coupling ε hc hcB hε q hq
  refine ⟨hCommon, hFixed, ?_⟩
  let V : OneParticle d → ℝ := fun x => ‖x‖^2/2
  obtain ⟨ρ,hρ,hPI⟩ := hCommon 1 1 zero_lt_one le_rfl (fun _ => (d:ℝ)) (fun R => R^2/2)
  have hV : GrowthClassPotential d s 1 (fun R => R^2/2) (fun _ => (d:ℝ)) V :=
    (QuadraticGaussianClass d s).2.2.2.2.2.2.2
  have hb : BoundedMultiplier d 1 (fun _ : OneParticle d => (1:ℝ)) := by
    refine ⟨measurable_const,1,1,zero_lt_one,le_rfl,(by norm_num),?_⟩
    intro x
    exact ⟨le_rfl,le_rfl⟩
  have hGaussian : ReferenceLaw V (fun _ => (1:ℝ)) = ProbabilityTheory.stdGaussian (OneParticle d) :=
    (QuadraticGaussianReference d).2.1
  refine ⟨ρ,hρ,?_⟩
  intro N hN coupling ε hc hcB hε
  rw [← hGaussian]
  exact hPI V hV (fun _ => 1) hb N hN coupling ε hc hcB hε
