import Tablet.SplitStationarityTransfer
import Tablet.CenteredGibbsKernelRowProjection
import Tablet.CenteredEnergyProbabilityControls
import Tablet.RieszCenteredRowStationarity
import Tablet.CenteredConditionalIdentity
import Tablet.RieszPositiveConvolution
open MeasureTheory ProbabilityTheory

-- [TABLET NODE: RieszCenteredDisintegration]
theorem RieszCenteredDisintegration (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N)
    (s a ε l u rl ru β H Z : ℝ) (hs : 0 ≤ s) (hsd : s < (d : ℝ)) (ha : 0 < a) (hε : 0 < ε)
    (q : BoundedBackground d l u) (r : BoundedBackground d rl ru) (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (hZ : 0 < Z) (hh : Measurable (BackgroundPotential (RieszKernel d s a ε) r.density))
    (hhb : ∀ᵐ x ∂volume, |BackgroundPotential (RieszKernel d s a ε) r.density x| ≤ H)
    (hEL : ∀ᵐ x ∂volume, r.density x = q.density x *
      Real.exp (-β * BackgroundPotential (RieszKernel d s a ε) r.density x) / Z) :
    let μ := (volume : Measure (UnitAddTorus (Fin d))).withDensity (fun z => ENNReal.ofReal (r.density z))
    letI : IsProbabilityMeasure μ := by
      apply isProbabilityMeasure_iff.mpr
      rw [withDensity_apply _ MeasurableSet.univ]
      simp only [Measure.restrict_univ]
      rw [←ofReal_integral_eq_lintegral_ofReal (integrable_of_integral_eq_one r.mass) (r.bounds.mono fun _ hx => r.lower_pos.le.trans hx.1), r.mass]
      simp
    let P := CenteredCanonicalLaw (N := N) (RieszKernel d s a ε) r.density β
    IsProbabilityMeasure P ∧ ∀ i : Fin N,
      let κ := GibbsConditionalKernel (Measure.pi (fun _ : ({i} : Finset (Fin N)) => μ))
        (CenteredDeletionPotential (RieszKernel d s a ε) r.density β i)
      IsMarkovKernel κ ∧
      let T := P.map (SplitCoordinateEquivalence i)
      T = T.fst ⊗ₘ κ := by
-- BODY
  classical
  let g := RieszKernel d s a ε
  let μ := (volume : Measure (UnitAddTorus (Fin d))).withDensity (fun z => ENNReal.ofReal (r.density z))
  haveI : IsProbabilityMeasure μ := by
    apply isProbabilityMeasure_iff.mpr
    rw [withDensity_apply _ MeasurableSet.univ]
    simp only [Measure.restrict_univ]
    rw [←ofReal_integral_eq_lintegral_ofReal (integrable_of_integral_eq_one r.mass) (r.bounds.mono fun _ hx => r.lower_pos.le.trans hx.1), r.mass]
    simp
  let P := CenteredCanonicalLaw (N := N) g r.density β
  obtain ⟨c,hc,hfound⟩ := RieszL1Foundation d hd s a hs hsd ha
  have hF := hfound ε hε.le
  obtain ⟨C,hC,hgb,_⟩ := RieszPositiveConvolution d hd s a ε hs hsd ha hε
  have hgb' : ∀ z, |g z| ≤ C := fun z => by simpa only [Real.norm_eq_abs] using hgb z
  have hP := (CenteredEnergyProbabilityControls d N rl ru C β r g hF.1 hF.2.1 hF.2.2.2.1 hC.le hgb').2.2
  haveI : IsProbabilityMeasure P := hP
  obtain ⟨_,hrows⟩ := RieszCenteredRowStationarity d N hd hN s a ε l u rl ru β H Z hs hsd ha hε q r hβ hH hZ hh hhb hEL
  have hident := CenteredConditionalIdentity d N hN l u rl ru β Z q r g hF.1 hZ hh hEL
  refine ⟨hP,fun i => ?_⟩
  let K := fun X : Configuration d N => NormalizedTilt μ (fun z => Real.exp
    (-β/(N:ℝ)*∑j:Fin N,if j=i then 0 else CenteredKernel g r.density z (X j)))
  let κ := GibbsConditionalKernel (Measure.pi (fun _ : ({i} : Finset (Fin N)) => μ))
    (CenteredDeletionPotential g r.density β i)
  obtain ⟨hκ,hproj⟩ := CenteredGibbsKernelRowProjection d N rl ru C β r g hF.1 hF.2.1 hF.2.2.2.1 hC.le hgb' i
  haveI : IsMarkovKernel κ := hκ
  refine ⟨hκ,?_⟩
  apply SplitStationarityTransfer i P κ K hproj
  intro F hmF hbF
  have heq : K = fun X : Configuration d N => NormalizedTilt volume
      (fun z => q.density z * Real.exp (-β * BackgroundPotential g r.density z / (N:ℝ)) *
        Real.exp (-ConditionalPotential g β X i z)) := by
    funext X
    exact hident X i
  rw [heq]
  exact hrows i F hmF hbF
