module

public import Tablet.RieszCenteredDisintegration
public import Tablet.CenteredCanonicalEntropyLower
public import Tablet.BoundedGibbsRelativeEntropy
public import Tablet.SquareDensityRelativeEntropy
public import Tablet.GibbsConditionalKernelCompProd
public import Tablet.SplitConditionalSquareEntropyIdentity
public import Tablet.BoundedSquareEntropyProperties

@[expose] public section
open MeasureTheory ProbabilityTheory InformationTheory

-- [TABLET NODE: RieszCenteredSquareEntropyLower]
theorem RieszCenteredSquareEntropyLower (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N)
    (s a ε l u rl ru β H Z : ℝ) (hs : 0 ≤ s) (hsd : s < (d : ℝ)) (ha : 0 < a) (hε : 0 < ε)
    (q : BoundedBackground d l u) (r : BoundedBackground d rl ru) (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (hZ : 0 < Z) (hh : Measurable (BackgroundPotential (RieszKernel d s a ε) r.density))
    (hhb : ∀ᵐ x ∂volume, |BackgroundPotential (RieszKernel d s a ε) r.density x| ≤ H)
    (hEL : ∀ᵐ x ∂volume, r.density x = q.density x *
      Real.exp (-β * BackgroundPotential (RieszKernel d s a ε) r.density x) / Z)
    (f : Configuration d N → ℝ) (hfm : Measurable f) (R : ℝ) (hfb : ∀ X, |f X| ≤ R)
    :
    let g := RieszKernel d s a ε
    let μ := (volume : Measure (UnitAddTorus (Fin d))).withDensity (fun z => ENNReal.ofReal (r.density z))
    let P := CenteredCanonicalLaw (N := N) g r.density β
    let K := fun (i : Fin N) (X : Configuration d N) => NormalizedTilt μ
      (fun z => Real.exp (-β/(N:ℝ)*∑j:Fin N,if j=i then 0 else CenteredKernel g r.density z (X j)))
    Entropy P (fun X => f X^2) ≤
      2*(∑ i : Fin N, ∫ X, Entropy (K i X) (fun z => f (Replacement X i z)^2) ∂P) +
      (Real.log (∫ X, Real.exp (-β*CenteredPairEnergy g r.density X) ∂Measure.pi (fun _ : Fin N => μ)) +
       Real.log (∫ X, Real.exp (-(3*β)*CenteredPairEnergy g r.density X) ∂Measure.pi (fun _ : Fin N => μ))) *
      (∫ X, f X^2 ∂P) := by
-- BODY
  have finite_entropy_to_base {Ω : Type} [MeasurableSpace Ω]
      (μ S : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure S]
      (V : Ω → ℝ) (hV : Measurable V) (C : ℝ) (hC : ∀ x, |V x| ≤ C)
      (hfin : klDiv S (NormalizedTilt μ (fun x => Real.exp (-V x))) ≠ ⊤) :
      klDiv S μ ≠ ⊤ := by
    have hi : Integrable V S := by
      apply (integrable_const C).mono' hV.aestronglyMeasurable
      exact Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs] using hC x
    have he : Integrable (fun x => Real.exp (-V x)) μ := by
      apply (integrable_const (Real.exp C)).mono' hV.neg.exp.aestronglyMeasurable
      exact Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        change -V x ≤ C
        have hh := (abs_le.mp (hC x)).1
        linarith
    obtain ⟨hacP,hllrP⟩ := klDiv_ne_top_iff.mp hfin
    have hac : S ≪ μ := hacP.trans (tilted_absolutelyContinuous μ (fun x => -V x))
    have hh := hllrP.congr (llr_tilted_right (f := fun x => -V x) hac he)
    have hllr : Integrable (llr S μ) S := by
      have hh' := hh.sub (hi.add (integrable_const (Real.log (∫ x,Real.exp (-V x)∂μ))))
      convert hh' using 1
      funext x
      change llr S μ x = -(-V x)+Real.log (∫ z,Real.exp (-V z)∂μ)+llr S μ x -
        (V x+Real.log (∫ z,Real.exp (-V z)∂μ))
      ring
    exact klDiv_ne_top hac hllr
  have positive_square_case (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N)
      (s a ε l u rl ru β H Z : ℝ) (hs : 0 ≤ s) (hsd : s < (d : ℝ)) (ha : 0 < a) (hε : 0 < ε)
      (q : BoundedBackground d l u) (r : BoundedBackground d rl ru) (hβ : 0 ≤ β) (hH : 0 ≤ H)
      (hZ : 0 < Z) (hh : Measurable (BackgroundPotential (RieszKernel d s a ε) r.density))
      (hhb : ∀ᵐ x ∂volume, |BackgroundPotential (RieszKernel d s a ε) r.density x| ≤ H)
      (hEL : ∀ᵐ x ∂volume, r.density x = q.density x *
        Real.exp (-β * BackgroundPotential (RieszKernel d s a ε) r.density x) / Z)
      (f : Configuration d N → ℝ) (hfm : Measurable f) (R : ℝ) (hfb : ∀ X, |f X| ≤ R)
      (hpos : 0 < ∫ X, f X ^ 2 ∂CenteredCanonicalLaw (N := N) (RieszKernel d s a ε) r.density β) :
      let g := RieszKernel d s a ε
      let μ := (volume : Measure (UnitAddTorus (Fin d))).withDensity (fun z => ENNReal.ofReal (r.density z))
      let P := CenteredCanonicalLaw (N := N) g r.density β
      let K := fun (i : Fin N) (X : Configuration d N) => NormalizedTilt μ
        (fun z => Real.exp (-β/(N:ℝ)*∑j:Fin N,if j=i then 0 else CenteredKernel g r.density z (X j)))
      Entropy P (fun X => f X^2) ≤
        2*(∑ i : Fin N, ∫ X, Entropy (K i X) (fun z => f (Replacement X i z)^2) ∂P) +
        (Real.log (∫ X, Real.exp (-β*CenteredPairEnergy g r.density X) ∂Measure.pi (fun _ : Fin N => μ)) +
         Real.log (∫ X, Real.exp (-(3*β)*CenteredPairEnergy g r.density X) ∂Measure.pi (fun _ : Fin N => μ))) *
        (∫ X, f X^2 ∂P) := by
    classical
    let g := RieszKernel d s a ε
    let μ := (volume : Measure (UnitAddTorus (Fin d))).withDensity (fun z => ENNReal.ofReal (r.density z))
    haveI : IsProbabilityMeasure μ := by
      apply isProbabilityMeasure_iff.mpr
      rw [withDensity_apply _ MeasurableSet.univ]
      simp only [Measure.restrict_univ]
      have hn : ∀ᵐ z ∂(volume : Measure (UnitAddTorus (Fin d))), 0 ≤ r.density z :=
        r.bounds.mono fun _ hz => r.lower_pos.le.trans hz.1
      have hi : Integrable r.density volume := integrable_of_integral_eq_one r.mass
      rw [←ofReal_integral_eq_lintegral_ofReal hi hn,r.mass]
      simp
    let P := CenteredCanonicalLaw (N := N) g r.density β
    let K := fun (i : Fin N) (X : Configuration d N) => NormalizedTilt μ
      (fun z => Real.exp (-β/(N:ℝ)*∑j:Fin N,if j=i then 0 else CenteredKernel g r.density z (X j)))
    obtain ⟨hP,hdis⟩ := RieszCenteredDisintegration d N hd hN s a ε l u rl ru β H Z hs hsd ha hε q r hβ hH hZ hh hhb hEL
    haveI : IsProbabilityMeasure P := hP
    let m := ∫ X, f X^2 ∂P
    let S := P.withDensity (fun X => ENNReal.ofReal (f X^2/m))
    obtain ⟨hS,hfin,hEnt⟩ := SquareDensityRelativeEntropy P f hfm R hfb hpos
    haveI : IsProbabilityMeasure S := hS
    obtain ⟨c,_,hfound⟩ := RieszL1Foundation d hd s a hs hsd ha
    have hF := hfound ε hε.le
    obtain ⟨C,hC,hgb,_⟩ := RieszPositiveConvolution d hd s a ε hs hsd ha hε
    have hgb' : ∀ z, |g z| ≤ C := fun z => by simpa only [Real.norm_eq_abs] using hgb z
    obtain ⟨hmV,⟨Q,hbV⟩,_⟩ := CenteredEnergyProbabilityControls d N rl ru C β r g hF.1 hF.2.1 hF.2.2.2.1 hC.le hgb'
    have hfinbase : klDiv S (Measure.pi (fun _ : Fin N => μ)) ≠ ⊤ := by
      apply finite_entropy_to_base (Measure.pi (fun _ : Fin N => μ)) S
        (fun X => β*CenteredPairEnergy g r.density X) hmV Q hbV
      simpa only [P,S,m,CenteredCanonicalLaw,neg_mul] using hfin
    have hlower := CenteredCanonicalEntropyLower d N rl ru C β r g hF.1 hF.2.1 hF.2.2.2.1 hC.le hgb' S hfinbase
    obtain ⟨_,hmU,hbU,_⟩ := CenteredDeletionPotentialControls d N rl ru C β r g hF.1 hF.2.1 hF.2.2.2.1 hC.le hgb'
    let T := fun i : Fin N => S.map (SplitCoordinateEquivalence i)
    let κ := fun i : Fin N => GibbsConditionalKernel (Measure.pi (fun _ : ({i} : Finset (Fin N)) => μ))
      (CenteredDeletionPotential g r.density β i)
    have hRi (i : Fin N) : (T i).fst ⊗ₘ κ i =
        ((T i).fst.prod (Measure.pi (fun _ : ({i} : Finset (Fin N)) => μ))).withDensity
          (fun p => ENNReal.ofReal (Real.exp (-CenteredDeletionPotential g r.density β i p) /
            (∫ y, Real.exp (-CenteredDeletionPotential g r.density β i (p.1,y))
              ∂Measure.pi (fun _ : ({i} : Finset (Fin N)) => μ)))) := by
      haveI : IsProbabilityMeasure (T i) := (Measure.isProbabilityMeasure_map_iff (SplitCoordinateEquivalence i).measurable.aemeasurable).mpr inferInstance
      apply GibbsConditionalKernelCompProd _ _ _ (hmU i)
      intro x
      apply (integrable_const (Real.exp (|β/(N:ℝ)| *(N:ℝ)*(C+3*(ru*∫z,|g z|∂volume))))).mono'
        ((hmU i).comp (measurable_const.prodMk measurable_id)).neg.exp.aestronglyMeasurable
      exact Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        change -CenteredDeletionPotential g r.density β i (x,y) ≤ _
        have hb := (abs_le.mp (hbU i (x,y))).1
        linarith
    have hterms (i : Fin N) : m*(klDiv (T i) ((T i).fst⊗ₘκ i)).toReal =
        ∫ X, Entropy (K i X) (fun z => f (Replacement X i z)^2) ∂P := by
      obtain ⟨hκ,hd⟩ := hdis i
      haveI : IsMarkovKernel (κ i) := hκ
      have hproj := (CenteredGibbsKernelRowProjection d N rl ru C β r g hF.1 hF.2.1 hF.2.2.2.1 hC.le hgb' i).2
      exact (SplitConditionalSquareEntropyIdentity P i (κ i) (K i) hproj hd f hfm R hfb hpos).2
    have heq : (∑ i : Fin N, m*(klDiv (T i) ((T i).fst⊗ₘκ i)).toReal) =
        ∑ i : Fin N, ∫ X, Entropy (K i X) (fun z => f (Replacement X i z)^2) ∂P :=
      Finset.sum_congr rfl fun i _ => hterms i
    have hl : (klDiv S P).toReal ≤
        2*(∑ i : Fin N,(klDiv (T i) ((T i).fst⊗ₘκ i)).toReal) +
        Real.log (∫ X,Real.exp (-β*CenteredPairEnergy g r.density X) ∂Measure.pi (fun _ : Fin N => μ)) +
        Real.log (∫ X,Real.exp (-(3*β)*CenteredPairEnergy g r.density X) ∂Measure.pi (fun _ : Fin N => μ)) := by
      dsimp only at hlower
      change (klDiv S P).toReal ≤
        2*(∑ i : Fin N,(klDiv (T i)
          (((T i).fst.prod (Measure.pi (fun _ : ({i} : Finset (Fin N)) => μ))).withDensity
          (fun p => ENNReal.ofReal (Real.exp (-CenteredDeletionPotential g r.density β i p) /
            (∫ y,Real.exp (-CenteredDeletionPotential g r.density β i (p.1,y))
            ∂Measure.pi (fun _ : ({i} : Finset (Fin N)) => μ)))))).toReal) + _ + _ at hlower
      simpa only [← hRi] using hlower
    have hmul := mul_le_mul_of_nonneg_left hl hpos.le
    rw [hEnt] at hmul
    rw [← Finset.mul_sum] at heq
    dsimp only
    rw [← heq]
    change Entropy P (fun X => f X^2) ≤ _
    change Entropy P (fun X => f X^2) ≤ m*(2*(∑ i : Fin N,(klDiv (T i) ((T i).fst⊗ₘκ i)).toReal)+_+_) at hmul
    nlinarith only [hmul]
  classical
  let g := RieszKernel d s a ε
  let μ := (volume : Measure (UnitAddTorus (Fin d))).withDensity (fun z => ENNReal.ofReal (r.density z))
  haveI : IsProbabilityMeasure μ := by
    apply isProbabilityMeasure_iff.mpr
    rw [withDensity_apply _ MeasurableSet.univ]
    simp only [Measure.restrict_univ]
    have hn : ∀ᵐ z ∂(volume : Measure (UnitAddTorus (Fin d))), 0 ≤ r.density z :=
      r.bounds.mono fun _ hz => r.lower_pos.le.trans hz.1
    have hi : Integrable r.density volume := integrable_of_integral_eq_one r.mass
    rw [←ofReal_integral_eq_lintegral_ofReal hi hn,r.mass]
    simp
  let P := CenteredCanonicalLaw (N := N) g r.density β
  let K := fun (i : Fin N) (X : Configuration d N) => NormalizedTilt μ
    (fun z => Real.exp (-β/(N:ℝ)*∑j:Fin N,if j=i then 0 else CenteredKernel g r.density z (X j)))
  have hP := (RieszCenteredDisintegration d N hd hN s a ε l u rl ru β H Z hs hsd ha hε q r hβ hH hZ hh hhb hEL).1
  haveI : IsProbabilityMeasure P := hP
  have hm : 0 ≤ ∫X,f X^2 ∂P := integral_nonneg fun X => sq_nonneg _
  rcases hm.eq_or_lt with hm|hm
  · have hz := (BoundedSquareEntropyProperties P f hfm R hfb).2.2.2 hm.symm
    dsimp only
    rw [hz,hm.symm,mul_zero,add_zero]
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro i _
    apply integral_nonneg
    intro X
    obtain ⟨c,_,hfound⟩ := RieszL1Foundation d hd s a hs hsd ha
    have hF := hfound ε hε.le
    obtain ⟨C,hC,hgb,_⟩ := RieszPositiveConvolution d hd s a ε hs hsd ha hε
    have hgb' : ∀z,|g z|≤C := fun z => by simpa only [Real.norm_eq_abs] using hgb z
    obtain ⟨hκ,hproj⟩ := CenteredGibbsKernelRowProjection d N rl ru C β r g hF.1 hF.2.1 hF.2.2.2.1 hC.le hgb' i
    haveI := hκ
    have hprob : IsProbabilityMeasure (K i X) := by
      change IsProbabilityMeasure (NormalizedTilt μ (fun z => Real.exp (-β/(N:ℝ)*∑j:Fin N,if j=i then 0 else CenteredKernel g r.density z (X j))))
      rw [← hproj X]
      exact (Measure.isProbabilityMeasure_map_iff (MeasurableEquiv.funUnique ({i} : Finset (Fin N)) (UnitAddTorus (Fin d))).measurable.aemeasurable).mpr inferInstance
    haveI := hprob
    exact (BoundedSquareEntropyProperties (K i X) (fun z=>f (Replacement X i z))
      (hfm.comp (measurable_update X)) R (fun z=>hfb _)).2.2.1
  · exact positive_square_case d N hd hN s a ε l u rl ru β H Z
      hs hsd ha hε q r hβ hH hZ hh hhb hEL f hfm R hfb hm
