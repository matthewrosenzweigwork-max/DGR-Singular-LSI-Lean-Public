import Tablet.HeatCenteredKernelAveraging
import Tablet.ProductDisjointBlockLaw
import Mathlib.MeasureTheory.Integral.Prod
import Tablet.CenteredPairEnergy
open MeasureTheory
-- [TABLET NODE: HeatCenteredEnergyAveraging]
theorem HeatCenteredEnergyAveraging (d N : ℕ) (t : ℝ) (ht : 0<t)
    (r : UnitAddTorus (Fin d)→ℝ) (M : ℝ) (hM : 1≤M) (hr : Measurable r)
    (hrb : ∀ᵐx∂(volume : Measure (UnitAddTorus (Fin d))),0≤r x∧r x≤M)
    (hrmass : ∫x,r x∂volume=1) (g : UnitAddTorus (Fin d)→ℝ)
    (hg : Measurable g) (hgi : Integrable g volume) (c : ℝ) (hc : 0≤c) (hgl : ∀x,-c≤g x) :
    let r':=HeatSemigroup d t r
    ∀X:Configuration d N,
    Integrable (fun Y:Configuration d N=>CenteredPairEnergy g r' (fun i=>X i+Y i)) (Measure.pi fun _:Fin N=>HeatIncrementLaw d t) ∧
    (∫Y:Configuration d N,CenteredPairEnergy g r' (fun i=>X i+Y i)∂Measure.pi (fun _:Fin N=>HeatIncrementLaw d t))=
      CenteredPairEnergy (HeatSemigroup d (t+t) g) r X := by
-- BODY
  classical
  let T:=UnitAddTorus (Fin d)
  let ν:=HeatIncrementLaw d t
  haveI : IsProbabilityMeasure ν := (HeatIncrementAveraging d t ht).1
  have pair_integral (i j : Fin N) (hij : i≠j) (f : T×T→ℝ)
      (hf : Integrable f (ν.prod ν)) :
      Integrable (fun Y : Configuration d N=>f (Y i,Y j)) (Measure.pi fun _:Fin N=>ν) ∧
      (∫Y : Configuration d N,f (Y i,Y j)∂Measure.pi (fun _:Fin N=>ν))=
        ∫p,f p∂ν.prod ν := by
    let s : Finset (Fin N) := {i}
    let q : Finset (Fin N) := {j}
    let is : s := ⟨i,by simp [s]⟩
    let jq : q := ⟨j,by simp [q]⟩
    have hd : Disjoint s q := by simp [s,q,hij]
    have hblock : MeasurePreserving
        (fun Y : Configuration d N => ((fun k:s=>Y k),(fun k:q=>Y k)))
        (Measure.pi fun _:Fin N=>ν)
        ((Measure.pi fun _:s=>ν).prod (Measure.pi fun _:q=>ν)) := by
      refine ⟨?_,ProductDisjointBlockLaw (fun _:Fin N=>ν) s q hd⟩
      exact (measurable_pi_lambda _ fun k=>measurable_pi_apply k.val).prodMk
        (measurable_pi_lambda _ fun k=>measurable_pi_apply k.val)
    have hleft := measurePreserving_eval (fun _:s=>ν) is
    have hright := measurePreserving_eval (fun _:q=>ν) jq
    have hp : MeasurePreserving (fun Y : Configuration d N=>(Y i,Y j))
        (Measure.pi fun _:Fin N=>ν) (ν.prod ν) :=
      (hleft.prod hright).comp hblock
    have hfm := hf
    rw [←hp.map_eq] at hfm
    refine ⟨hp.integrable_comp_of_integrable hf,?_⟩
    simpa only [hp.map_eq] using
      (integral_map hp.measurable.aemeasurable hfm.aestronglyMeasurable).symm
  let r':T→ℝ:=HeatSemigroup d t r
  have hk:=HeatCenteredKernelAveraging d t ht r M hM hr hrb hrmass g hg hgi c hc hgl
  dsimp only
  intro X
  have hp (i j:Fin N) (hij:i<j) := pair_integral i j (ne_of_lt hij)
    (fun p:T×T=>CenteredKernel g r' (X i+p.1) (X j+p.2)) (hk (X i) (X j)).1
  have hterm (i j:Fin N) : Integrable (fun Y:Configuration d N=>if i<j then CenteredKernel g r' (X i+Y i) (X j+Y j) else 0)
      (Measure.pi fun _:Fin N=>ν) :=by
    by_cases hij:i<j
    · simpa only [if_pos hij] using (hp i j hij).1
    · simp only [if_neg hij]
      exact integrable_const _
  have heach (i j:Fin N) :
      (∫Y:Configuration d N,(if i<j then CenteredKernel g r' (X i+Y i) (X j+Y j) else 0)∂Measure.pi (fun _:Fin N=>ν))=
      if i<j then CenteredKernel (HeatSemigroup d (t+t) g) r (X i) (X j) else 0 :=by
    by_cases hij:i<j
    · simp only [if_pos hij]
      exact (hp i j hij).2.trans (hk (X i) (X j)).2
    · simp [hij]
  have hiRows (i:Fin N) := integrable_finset_sum Finset.univ (fun j _=>hterm i j)
  have hiTotal := integrable_finset_sum Finset.univ (fun i _=>hiRows i)
  refine ⟨hiTotal.const_mul ((N:ℝ)⁻¹),?_⟩
  unfold CenteredPairEnergy
  rw [integral_const_mul,integral_finset_sum _ (fun i _=>hiRows i)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finset_sum _ (fun j _=>hterm i j)]
  exact Finset.sum_congr rfl (fun j _=>heach i j)
