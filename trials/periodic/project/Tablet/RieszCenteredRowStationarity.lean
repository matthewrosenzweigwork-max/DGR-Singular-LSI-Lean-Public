module

public import Tablet.CenteredCanonicalRecenter
public import Tablet.CanonicalTiltRowStationarity
public import Tablet.BoundedTiltComposition
public import Tablet.RieszLocalStructure
public import Mathlib.Topology.Algebra.Group.Quotient

@[expose] public section
open MeasureTheory
-- [TABLET NODE: RieszCenteredRowStationarity]
theorem RieszCenteredRowStationarity (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N)
    (s a ε l u rl ru β H Z : ℝ) (hs : 0 ≤ s) (hsd : s < (d : ℝ)) (ha : 0 < a) (hε : 0 < ε)
    (q : BoundedBackground d l u) (r : BoundedBackground d rl ru) (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (hZ : 0 < Z) (hh : Measurable (BackgroundPotential (RieszKernel d s a ε) r.density))
    (hhb : ∀ᵐ x ∂volume, |BackgroundPotential (RieszKernel d s a ε) r.density x| ≤ H)
    (hEL : ∀ᵐ x ∂volume, r.density x = q.density x *
      Real.exp (-β * BackgroundPotential (RieszKernel d s a ε) r.density x) / Z) :
    let P := CenteredCanonicalLaw (N := N) (RieszKernel d s a ε) r.density β
    let ν := fun (i : Fin N) (X : Configuration d N) => NormalizedTilt volume
      (fun z => q.density z * Real.exp (-β * BackgroundPotential (RieszKernel d s a ε) r.density z / (N : ℝ)) *
        Real.exp (-ConditionalPotential (RieszKernel d s a ε) β X i z))
    (∀ i X, IsProbabilityMeasure (ν i X)) ∧
    ∀ i : Fin N, ∀ F : Configuration d N → ℝ, Measurable F → (∃ C : ℝ, ∀ X, |F X| ≤ C) →
      Integrable (fun X => ∫ z, F (Replacement X i z) ∂ν i X) P ∧
      (∫ X, ∫ z, F (Replacement X i z) ∂ν i X ∂P) = ∫ X, F X ∂P := by
-- BODY
  classical
  dsimp only
  haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp; infer_instance
  haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := inferInstance
  let G := RieszKernel d s a ε
  let h := BackgroundPotential G r.density
  let b : Configuration d N → ℝ := fun X => Real.exp (-β/(N : ℝ)*∑i:Fin N,h (X i))
  let W : Configuration d N → ℝ := fun X => b X * GibbsWeight G q.density β X
  have hnp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hcoords : ∀ᵐ X : Configuration d N ∂volume, ∀ i : Fin N, |h (X i)| ≤ H := by
    rw [Filter.eventually_all]; intro i
    exact (measurePreserving_eval (fun _ : Fin N => (volume : Measure (UnitAddTorus (Fin d)))) i).quasiMeasurePreserving.tendsto_ae hhb
  have hb : ∀ᵐ X : Configuration d N ∂volume, Real.exp (-β*H) ≤ b X ∧ b X ≤ Real.exp (β*H) := by
    filter_upwards [hcoords] with X hX
    have hlo : -(N : ℝ)*H ≤ ∑ i : Fin N,h (X i) := by
      have hh := Finset.sum_le_sum (s:=Finset.univ) fun i _ => (abs_le.mp (hX i)).1; simpa using hh
    have hhi : (∑ i : Fin N,h (X i)) ≤ (N : ℝ)*H := by
      have hh := Finset.sum_le_sum (s:=Finset.univ) fun i _ => (abs_le.mp (hX i)).2; simpa using hh
    have hdiv := div_nonneg hβ hnp.le
    have hl' := mul_le_mul_of_nonneg_left hlo hdiv
    have hu' := mul_le_mul_of_nonneg_left hhi hdiv
    have hlow : β/(N : ℝ)*(-(N : ℝ)*H)=-(β*H) := by field_simp
    have hhigh : β/(N : ℝ)*((N : ℝ)*H)=β*H := by field_simp
    rw [hlow] at hl'; rw [hhigh] at hu'
    change Real.exp (-β*H) ≤ Real.exp _ ∧ Real.exp _ ≤ Real.exp (β*H)
    constructor <;> apply Real.exp_le_exp.mpr
    · simpa only [neg_div,neg_mul] using neg_le_neg hu'
    · simpa only [neg_div,neg_mul,neg_neg] using neg_le_neg hl'
  have hbm : Measurable b :=
    (measurable_const.mul (Finset.measurable_fun_sum _ fun i _ => hh.comp (measurable_pi_apply i))).exp
  obtain ⟨c,hc,hfound⟩ := RieszL1Foundation d hd s a hs hsd ha
  have hF := hfound ε hε.le
  have hgl : ∀ᵐ x ∂volume,-c≤G x := Filter.Eventually.of_forall hF.2.2.2.2.1
  have hr := CenteredCanonicalRecenter d N hN l u rl ru β c H Z q r G hF.1 hF.2.1 hβ hc hgl hH hZ hh hhb hEL
  have hPair : Measurable (PairEnergy (N := N) G) := by
    unfold PairEnergy
    refine measurable_const.mul (Finset.measurable_fun_sum _ fun i _ => ?_)
    refine Finset.measurable_fun_sum _ fun j _ => ?_
    split_ifs; exact hF.1.comp ((measurable_pi_apply i).sub (measurable_pi_apply j)); exact measurable_const
  have hWm : Measurable (GibbsWeight (N := N) G q.density β) :=
    (measurable_const.mul hPair).exp.mul (ProductBackgroundFacts d N l u q).1
  have hWn : ∀ᵐ X : Configuration d N ∂volume,0≤GibbsWeight G q.density β X := by
    filter_upwards [(ProductBackgroundFacts d N l u q).2.2.2] with X hX
    exact mul_nonneg (Real.exp_pos _).le ((pow_nonneg q.lower_pos.le N).trans hX.1)
  have hnorm := GibbsNormalizerBounds d N hN l u q G hF.1 hF.2.1 c β hc hβ hgl
  have hZg : 0<∫X:Configuration d N,GibbsWeight G q.density β X := (Real.exp_pos _).trans_le hnorm.2.1
  have hmeasure : NormalizedTilt volume W = CenteredCanonicalLaw (N := N) G r.density β := by
    exact (BoundedTiltComposition volume (GibbsWeight G q.density β) b _ _ hWm hWn hnorm.1 hZg
      hbm (Real.exp_pos _) hb).trans hr.1.symm
  have quotient : IsOpenQuotientMap (TorusLift d) := by
    have hcq : IsOpenQuotientMap ((↑):ℝ→AddCircle (1:ℝ)) := QuotientAddGroup.isOpenQuotientMap_mk
    have hp := IsOpenQuotientMap.piMap (fun _:Fin d=>hcq)
    exact hp.comp (PiLp.homeomorph 2 (fun _:Fin d=>ℝ)).isOpenQuotientMap
  have hcont : Continuous G := quotient.continuous_comp_iff.mp
    (((RieszLocalStructure d hd s a hs hsd ha).2.1 ε hε).continuous)
  obtain ⟨K,hKb⟩ := (isCompact_univ : IsCompact (Set.univ : Set (UnitAddTorus (Fin d)))).exists_bound_of_continuousOn hcont.continuousOn
  have hK : 0≤K := (norm_nonneg (G 0)).trans (hKb 0 (Set.mem_univ _))
  have hgb : ∀x,|G x|≤K := fun x=>by simpa only [Real.norm_eq_abs] using hKb x (Set.mem_univ x)
  have hrows := CanonicalTiltRowStationarity d N hN l u β K H q hβ hK hH G h hF.1 hh hF.2.2.2.1 hgb hhb
  change _ ∧ ∀ i : Fin N, ∀ F : Configuration d N → ℝ, Measurable F → (∃ C : ℝ, ∀ X, |F X| ≤ C) →
    Integrable _ (CenteredCanonicalLaw (N := N) G r.density β) ∧
      (∫ X, _ ∂CenteredCanonicalLaw (N := N) G r.density β) = ∫ X, F X ∂CenteredCanonicalLaw (N := N) G r.density β
  rw [←hmeasure]
  exact hrows
