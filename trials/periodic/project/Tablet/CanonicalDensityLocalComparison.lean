import Tablet.CanonicalLawUniformBounds
import Tablet.RieszLocalStructure
import Tablet.CollisionSet
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Order.Compact
open MeasureTheory Set
open scoped ContDiff
-- [TABLET NODE: CanonicalDensityLocalComparison]
theorem CanonicalDensityLocalComparison (d N:ℕ) (hd:2≤d) (hN:2≤N)
    (s a l u β:ℝ) (hs:0≤s) (hsd:s<(d:ℝ)) (ha:0<a)
    (q:BoundedBackground d l u) (hβ:0≤β) (ε:ℝ) (hε:0≤ε) :
    let W := GibbsWeight (N := N) (RieszKernel d s a ε) q.density β
    let Z := ∫X,W X
    (∃M:ℝ,0≤M ∧ ∀ᵐX:Configuration d N∂volume,0≤W X/Z ∧ W X/Z≤M) ∧
    (∀K:Set (Configuration d N),IsCompact K → Disjoint K (CollisionSet d N) →
      ∃m:ℝ,0<m ∧ ∀ᵐX:Configuration d N∂volume,X∈K → m≤W X/Z) := by
-- BODY
  have kernel_continuous_offzero (d:ℕ) (hd:2≤d) (s a:ℝ) (hs:0≤s)
      (hsd:s<(d:ℝ)) (ha:0<a) (ε:ℝ) (hε:0≤ε) :
      ContinuousOn (RieszKernel d s a ε) {x|x≠0} := by
    have hq : IsOpenQuotientMap (TorusLift d) := by
      have hc : IsOpenQuotientMap ((↑):ℝ→AddCircle (1:ℝ)) :=
        QuotientAddGroup.isOpenQuotientMap_mk
      have hp : IsOpenQuotientMap
        (Pi.map (fun _ : Fin d=>((↑):ℝ→AddCircle (1:ℝ)))) :=
        IsOpenQuotientMap.piMap (fun _=>hc)
      exact hp.comp (PiLp.homeomorph 2 (fun _ : Fin d=>ℝ)).isOpenQuotientMap
    apply (hq.isQuotientMap.continuousOn_isOpen_iff isOpen_ne).mpr
    by_cases he : ε=0
    · subst ε
      exact (RieszLocalStructure d hd s a hs hsd ha).1.continuousOn
    · exact ((RieszLocalStructure d hd s a hs hsd ha).2.1 ε (lt_of_le_of_ne hε (Ne.symm he))).continuous.continuousOn
  have pair_continuous_compact (d N:ℕ) (g:UnitAddTorus (Fin d)→ℝ)
      (hg:ContinuousOn g {x|x≠0}) (K:Set (Configuration d N))
      (hK:Disjoint K (CollisionSet d N)) : ContinuousOn (PairEnergy g) K := by
    unfold PairEnergy
    apply ContinuousOn.const_mul
    apply continuousOn_finset_sum
    intro i _
    apply continuousOn_finset_sum
    intro j _
    by_cases hij:i<j
    · simp only [hij,ite_true]
      apply hg.comp ((continuous_apply i).sub (continuous_apply j)).continuousOn
      intro X hx
      change X i-X j≠0
      intro hzero
      exact (Set.disjoint_left.mp hK hx) ⟨i,j,hij,sub_eq_zero.mp hzero⟩
    · simp only [hij,ite_false]
      exact continuousOn_const
  let W := GibbsWeight (N := N) (RieszKernel d s a ε) q.density β
  let Z := ∫X,W X
  obtain ⟨L,M,hL,hM,hall⟩ := CanonicalLawUniformBounds d N hd hN s a l u β hs hsd ha q hβ
  have hZ : 0<Z := hL.trans_le (hall ε hε).2.2.1
  constructor
  · refine ⟨M/L,div_nonneg hM hL.le,?_⟩
    filter_upwards [(hall ε hε).2.2.2.1] with X hx
    exact ⟨div_nonneg hx.1 hZ.le,div_le_div₀ hM hx.2 hL (hall ε hε).2.2.1⟩
  · intro K hK hfree
    have hp := pair_continuous_compact d N (RieszKernel d s a ε)
      (kernel_continuous_offzero d hd s a hs hsd ha ε hε) K hfree
    obtain ⟨B,hB⟩ := hK.bddAbove_image hp
    let m := Real.exp (-β*B)*l^N/Z
    refine ⟨m,by dsimp [m];exact div_pos (mul_pos (Real.exp_pos _) (pow_pos q.lower_pos N)) hZ,?_⟩
    filter_upwards [(ProductBackgroundFacts d N l u q).2.2.2] with X hx
    intro hX
    have hb : PairEnergy (RieszKernel d s a ε) X≤B := hB (mem_image_of_mem _ hX)
    have he : Real.exp (-β*B)≤Real.exp (-β*PairEnergy (RieszKernel d s a ε) X) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hb hβ])
    apply (div_le_div_iff_of_pos_right hZ).mpr
    exact mul_le_mul he hx.1 (pow_nonneg q.lower_pos.le N) (Real.exp_nonneg _)
