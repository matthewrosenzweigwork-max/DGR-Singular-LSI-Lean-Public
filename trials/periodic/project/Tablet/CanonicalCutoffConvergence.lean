module

public import Tablet.CanonicalLawUniformBounds
public import Tablet.RieszCutoffContinuity
public import Tablet.CollisionSet
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section
open MeasureTheory Filter Set
open scoped Topology
-- [TABLET NODE: CanonicalCutoffConvergence]
theorem CanonicalCutoffConvergence (d N : ℕ) (hd : 2≤d) (hN : 2≤N)
    (s a l u β : ℝ) (hs : 0≤s) (hsd : s<(d:ℝ)) (ha : 0<a)
    (q : BoundedBackground d l u) (hβ : 0≤β) :
    (∀ε:ℝ,0≤ε → IsProbabilityMeasure
      (CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β)) ∧
    Tendsto (fun ε:ℝ=>∫X,GibbsWeight (N := N) (RieszKernel d s a ε) q.density β X)
      (𝓝[>]0) (𝓝 (∫X,GibbsWeight (N := N) (RieszKernel d s a 0) q.density β X)) ∧
    (let W := fun ε:ℝ=>GibbsWeight (N := N) (RieszKernel d s a ε) q.density β
     let Z := fun ε:ℝ=>∫X,W ε X
     Tendsto (fun ε:ℝ=>∫X,|W ε X/Z ε-W 0 X/Z 0|) (𝓝[>]0) (𝓝 0)) ∧
    (∀h:Configuration d N→ℝ,Measurable h → (∃C:ℝ,∀X,|h X|≤C) →
      Tendsto (fun ε:ℝ=>∫X,h X∂CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β)
        (𝓝[>]0) (𝓝 (∫X,h X∂CanonicalLaw (N := N) (RieszKernel d s a 0) q.density β))) := by
-- BODY
  classical
  have circle_probability : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
    infer_instance
  have circle_null : NullSingletonClass (volume : Measure (AddCircle (1 : ℝ))) := by
    constructor
    intro x
    have h := AddCircle.volume_closedBall (T := 1) (x := x) 0
    simpa using h
  have difference_preserving (d N : ℕ) (i j : Fin N) (hij : i ≠ j) :
      MeasurePreserving (fun X : Configuration d N => X i-X j) volume volume := by
    letI := circle_probability
    have hp : MeasurePreserving (fun X : Configuration d N => (X i,X j)) volume
        ((volume : Measure (UnitAddTorus (Fin d))).prod volume) := by
      have hi := (ProbabilityTheory.iIndepFun_pi (μ := fun _ : Fin N =>
        (volume : Measure (UnitAddTorus (Fin d)))) (X := fun _ => id)
        (fun _ => aemeasurable_id)).indepFun hij
      refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), ?_⟩
      change Measure.map (fun X : Configuration d N => (X i,X j))
        (Measure.pi (fun _ : Fin N => (volume : Measure (UnitAddTorus (Fin d))))) = _
      have h := hi.map_prod_eq_prod_map_map
        (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
      simpa only [(measurePreserving_eval (fun _ : Fin N =>
        (volume : Measure (UnitAddTorus (Fin d)))) i).map_eq,
        (measurePreserving_eval (fun _ : Fin N =>
        (volume : Measure (UnitAddTorus (Fin d)))) j).map_eq] using h
    exact (measurePreserving_fst.comp (measurePreserving_sub_prod volume volume)).comp hp
  have collision_haar_null (d N : ℕ) (hd : 0 < d) :
      (volume : Measure (Configuration d N)) (CollisionSet d N) = 0 := by
    letI := circle_probability
    letI := circle_null
    letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
    have hnull : NullSingletonClass (volume : Measure (UnitAddTorus (Fin d))) := by
      infer_instance
    letI := hnull
    have hp (i j : Fin N) : (volume : Measure (Configuration d N)) {X | i<j ∧ X i=X j} = 0 := by
      by_cases hij : i<j
      · have hm := (difference_preserving d N i j (ne_of_lt hij)).measure_preimage
          (measurableSet_singleton (0 : UnitAddTorus (Fin d))).nullMeasurableSet
        change volume {X : Configuration d N | X i-X j=0} = volume {(0 : UnitAddTorus (Fin d))} at hm
        simpa only [sub_eq_zero, hij, true_and, measure_singleton] using hm
      · simp [hij]
    have he : CollisionSet d N = ⋃ i : Fin N, ⋃ j : Fin N, {X | i<j ∧ X i=X j} := by
      ext X
      simp [CollisionSet]
    rw [he]
    exact measure_iUnion_null fun i => measure_iUnion_null (hp i)
  have canonical_limit_of_kernel_limit (d N : ℕ) (hd : 2≤d) (hN : 2≤N)
      (s a l u β : ℝ) (hs : 0≤s) (hsd : s<(d:ℝ)) (ha : 0<a)
      (q : BoundedBackground d l u) (hβ : 0≤β)
      (hkernel : ∀x:UnitAddTorus (Fin d),x≠0 →
        Tendsto (fun ε:ℝ=>RieszKernel d s a ε x) (𝓝[>]0) (𝓝 (RieszKernel d s a 0 x))) :
      Tendsto (fun ε:ℝ=>∫X,GibbsWeight (N := N) (RieszKernel d s a ε) q.density β X)
        (𝓝[>]0) (𝓝 (∫X,GibbsWeight (N := N) (RieszKernel d s a 0) q.density β X)) ∧
      (∀h:Configuration d N→ℝ,Measurable h → (∃C:ℝ,∀X,|h X|≤C) →
        Tendsto (fun ε:ℝ=>∫X,h X∂CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β)
          (𝓝[>]0) (𝓝 (∫X,h X∂CanonicalLaw (N := N) (RieszKernel d s a 0) q.density β))) := by
    letI := circle_probability
    let W := fun ε:ℝ=>GibbsWeight (N := N) (RieszKernel d s a ε) q.density β
    obtain ⟨L,M,hL,hM,hall⟩ := CanonicalLawUniformBounds d N hd hN s a l u β hs hsd ha q hβ
    have heps : ∀ᶠε:ℝ in 𝓝[>]0,0≤ε := by
      have hh : ∀ᶠ ε:ℝ in 𝓝[>]0, ε∈Ioi 0 := eventually_mem_nhdsWithin
      exact hh.mono fun _ h=>h.le
    have hfree : ∀ᵐX:Configuration d N∂volume,X∉CollisionSet d N := by
      rw [ae_iff]
      simpa using collision_haar_null d N (by omega)
    have hconv : ∀ᵐX:Configuration d N∂volume,Tendsto (fun ε=>W ε X) (𝓝[>]0) (𝓝 (W 0 X)) := by
      filter_upwards [hfree] with X hX
      have hp : Tendsto (fun ε:ℝ=>PairEnergy (RieszKernel d s a ε) X)
        (𝓝[>]0) (𝓝 (PairEnergy (RieszKernel d s a 0) X)) := by
        unfold PairEnergy
        apply Tendsto.const_mul
        apply tendsto_finset_sum
        intro i _
        apply tendsto_finset_sum
        intro j _
        by_cases hij : i<j
        · simp only [hij,ite_true]
          apply hkernel
          intro hzero
          exact hX ⟨i,j,hij,sub_eq_zero.mp hzero⟩
        · simp only [hij,ite_false]
          exact tendsto_const_nhds
      simpa only [W, GibbsWeight, Function.comp_apply] using (Real.continuous_exp.continuousAt.tendsto.comp (hp.const_mul (-β))).mul_const (ProductDensity q.density X)
    have hm : ∀ᶠε:ℝ in 𝓝[>]0,AEStronglyMeasurable (W ε) volume := by
      filter_upwards [heps] with ε hε
      exact (hall ε hε).1.aestronglyMeasurable
    have hb : ∀ᶠε:ℝ in 𝓝[>]0,∀ᵐX:Configuration d N∂volume,‖W ε X‖≤M := by
      filter_upwards [heps] with ε hε
      filter_upwards [(hall ε hε).2.2.2.1] with X hX
      rw [Real.norm_eq_abs,abs_of_nonneg hX.1]
      exact hX.2
    have hz := tendsto_integral_filter_of_dominated_convergence (fun _=>M) hm hb (integrable_const M) hconv
    refine ⟨hz,?_⟩
    intro h hh hbound
    obtain ⟨C,hC⟩ := hbound
    have hCi : 0≤C := (abs_nonneg (h 0)).trans (hC 0)
    have hnmeas : ∀ᶠε:ℝ in 𝓝[>]0,AEStronglyMeasurable (fun X=>h X*W ε X) volume :=
      hm.mono fun _ hε=>hh.aestronglyMeasurable.mul hε
    have hnb : ∀ᶠε:ℝ in 𝓝[>]0,∀ᵐX:Configuration d N∂volume,‖h X*W ε X‖≤C*M := by
      filter_upwards [hb] with ε hε
      filter_upwards [hε] with X hX
      rw [norm_mul,Real.norm_eq_abs (h X)]
      exact mul_le_mul (hC X) hX (norm_nonneg _) hCi
    have hnconv : ∀ᵐX:Configuration d N∂volume,
        Tendsto (fun ε=>h X*W ε X) (𝓝[>]0) (𝓝 (h X*W 0 X)) :=
      hconv.mono fun X hX=>hX.const_mul (h X)
    have hn := tendsto_integral_filter_of_dominated_convergence (fun _=>C*M) hnmeas hnb
      (integrable_const _) hnconv
    have hzero : 0<∫X,W 0 X := hL.trans_le (hall 0 (le_refl 0)).2.2.1
    have heq (ε:ℝ) (hε:0≤ε) :
        (∫X,h X∂CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β) =
        (∫X,h X*W ε X)/(∫X,W ε X) := by
      obtain ⟨hwm,hwi,hZ,hwb,hP⟩ := hall ε hε
      have hhi : Integrable (fun X=>h X*W ε X) volume := by
        apply hwi.bdd_mul hh.aestronglyMeasurable
        exact Eventually.of_forall fun X=>by simpa only [Real.norm_eq_abs] using hC X
      exact ((TiltNormalization volume (W ε) hwm (hwb.mono fun _ hv=>hv.1) hwi
        (hL.trans_le hZ)).2 h hh hhi).2
    have hratio := hn.div hz (ne_of_gt hzero)
    rw [heq 0 (le_refl 0)]
    apply hratio.congr'
    filter_upwards [heps] with ε hε
    exact (heq ε hε).symm
    -- The value at ε=0 is identified by the same normalization formula.
  have canonical_density_l1_of_kernel_limit (d N : ℕ) (hd : 2≤d) (hN : 2≤N)
      (s a l u β : ℝ) (hs : 0≤s) (hsd : s<(d:ℝ)) (ha : 0<a)
      (q : BoundedBackground d l u) (hβ : 0≤β)
      (hkernel : ∀x:UnitAddTorus (Fin d),x≠0 →
        Tendsto (fun ε:ℝ=>RieszKernel d s a ε x) (𝓝[>]0) (𝓝 (RieszKernel d s a 0 x))) :
      let W := fun ε:ℝ=>GibbsWeight (N := N) (RieszKernel d s a ε) q.density β
      let Z := fun ε:ℝ=>∫X,W ε X
      Tendsto (fun ε:ℝ=>∫X,|W ε X/Z ε-W 0 X/Z 0|) (𝓝[>]0) (𝓝 0) := by
    letI := circle_probability
    let W := fun ε:ℝ=>GibbsWeight (N := N) (RieszKernel d s a ε) q.density β
    let Z := fun ε:ℝ=>∫X,W ε X
    change Tendsto (fun ε:ℝ=>∫X,|W ε X/Z ε-W 0 X/Z 0|) (𝓝[>]0) (𝓝 0)
    obtain ⟨L,M,hL,hM,hall⟩ := CanonicalLawUniformBounds d N hd hN s a l u β hs hsd ha q hβ
    have heps : ∀ᶠε:ℝ in 𝓝[>]0,0≤ε := by
      have hh : ∀ᶠ ε:ℝ in 𝓝[>]0, ε∈Ioi 0 := eventually_mem_nhdsWithin
      exact hh.mono fun _ h=>h.le
    have hz : Tendsto Z (𝓝[>]0) (𝓝 (Z 0)) :=
      (canonical_limit_of_kernel_limit d N hd hN s a l u β hs hsd ha q hβ hkernel).1
    have hz0 : Z 0≠0 := ne_of_gt (hL.trans_le (hall 0 (le_refl 0)).2.2.1)
    have hfree : ∀ᵐX:Configuration d N∂volume,X∉CollisionSet d N := by
      rw [ae_iff]
      simpa using collision_haar_null d N (by omega)
    have hconv : ∀ᵐX:Configuration d N∂volume,Tendsto (fun ε=>W ε X) (𝓝[>]0) (𝓝 (W 0 X)) := by
      filter_upwards [hfree] with X hX
      have hp : Tendsto (fun ε:ℝ=>PairEnergy (RieszKernel d s a ε) X)
        (𝓝[>]0) (𝓝 (PairEnergy (RieszKernel d s a 0) X)) := by
        unfold PairEnergy
        apply Tendsto.const_mul
        apply tendsto_finsetSum
        intro i _
        apply tendsto_finsetSum
        intro j _
        by_cases hij : i<j
        · simp only [hij,ite_true]
          apply hkernel
          intro hzero
          exact hX ⟨i,j,hij,sub_eq_zero.mp hzero⟩
        · simp only [hij,ite_false]
          exact tendsto_const_nhds
      simpa only [W,GibbsWeight,Function.comp_apply] using
        (Real.continuous_exp.continuousAt.tendsto.comp (hp.const_mul (-β))).mul_const (ProductDensity q.density X)
    have hrbound (ε:ℝ) (hε:0≤ε) : ∀ᵐX:Configuration d N∂volume,|W ε X/Z ε|≤M/L := by
      filter_upwards [(hall ε hε).2.2.2.1] with X hX
      have hZ : 0<Z ε := hL.trans_le (hall ε hε).2.2.1
      rw [abs_of_nonneg (div_nonneg hX.1 hZ.le)]
      exact div_le_div₀ hM hX.2 hL (hall ε hε).2.2.1
    have hm : ∀ᶠε:ℝ in 𝓝[>]0,AEStronglyMeasurable
        (fun X:Configuration d N=>|W ε X/Z ε-W 0 X/Z 0|) volume := by
      filter_upwards [heps] with ε hε
      have hh : Measurable (fun X:Configuration d N=>W ε X/Z ε-W 0 X/Z 0) :=
        ((hall ε hε).1.div_const (Z ε)).sub ((hall 0 (le_refl 0)).1.div_const (Z 0))
      simpa only [Real.norm_eq_abs] using hh.norm.aestronglyMeasurable (μ := volume)
    have hb : ∀ᶠε:ℝ in 𝓝[>]0,∀ᵐX:Configuration d N∂volume,
        ‖|W ε X/Z ε-W 0 X/Z 0|‖≤2*(M/L) := by
      filter_upwards [heps] with ε hε
      filter_upwards [hrbound ε hε,hrbound 0 (le_refl 0)] with X hx hy
      rw [Real.norm_eq_abs,abs_abs]
      exact (abs_sub _ _).trans (by linarith)
    have hc : ∀ᵐX:Configuration d N∂volume,
        Tendsto (fun ε=>|W ε X/Z ε-W 0 X/Z 0|) (𝓝[>]0) (𝓝 (0:ℝ)) := by
      filter_upwards [hconv] with X hx
      simpa using ((hx.div hz hz0).sub_const (W 0 X/Z 0)).abs
    simpa using tendsto_integral_filter_of_dominated_convergence (fun _=>2*(M/L)) hm hb
      (integrable_const _) hc
  obtain ⟨L,M,hL,hM,hall⟩ := CanonicalLawUniformBounds d N hd hN s a l u β hs hsd ha q hβ
  have hk := RieszCutoffContinuity d s a hsd
  have ht := canonical_limit_of_kernel_limit d N hd hN s a l u β hs hsd ha q hβ hk
  exact ⟨fun ε hε=>(hall ε hε).2.2.2.2,ht.1,
    canonical_density_l1_of_kernel_limit d N hd hN s a l u β hs hsd ha q hβ hk,ht.2⟩
