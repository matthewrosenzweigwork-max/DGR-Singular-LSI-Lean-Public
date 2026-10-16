import Tablet.DisjointBlockMarginalEntropy
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
open MeasureTheory InformationTheory ProbabilityTheory

-- [TABLET NODE: ProductDeletionConditionalEntropy]
theorem ProductDeletionConditionalEntropy {I Ω : Type*}
    [Fintype I] [DecidableEq I] [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    (μ : I → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (S : Measure (I → Ω)) [IsProbabilityMeasure S] (i : I) :
    let s := (Finset.univ : Finset I).erase i
    let t := ({i} : Finset I)
    let T := S.map (fun x : I → Ω => ((fun j : s => x j), (fun j : t => x j)))
    klDiv S (Measure.pi μ) =
      klDiv (S.map (fun x : I → Ω => fun j : s => x j)) (Measure.pi (fun j : s => μ j)) +
      klDiv T ((S.map (fun x : I → Ω => fun j : s => x j)).prod (Measure.pi (fun j : t => μ j))) := by
-- BODY
  have full_coordinate_local   
      (μ : I → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
      (S : Measure (I → Ω)) [IsProbabilityMeasure S] :
      klDiv (S.map (fun x : I → Ω => fun i : (Finset.univ : Finset I) => x i))
        (Measure.pi (fun i : (Finset.univ : Finset I) => μ i)) = klDiv S (Measure.pi μ) := by

    classical
    let e : (I → Ω) ≃ᵐ (↥(Finset.univ : Finset I) → Ω) := {
      toEquiv := {
        toFun := fun x i => x i
        invFun := fun x i => x ⟨i, Finset.mem_univ i⟩
        left_inv := fun x => by funext i; rfl
        right_inv := fun x => by funext i; rfl }
      measurable_toFun := measurable_pi_lambda _ fun i => measurable_pi_apply i.val
      measurable_invFun := measurable_pi_lambda _ fun i => measurable_pi_apply (⟨i, Finset.mem_univ i⟩ : ↥(Finset.univ : Finset I)) }
    have hh := RelativeEntropyUnderMeasurableEquivalence S (Measure.pi μ) e
    change klDiv (S.map (fun x : I → Ω => fun i : (Finset.univ : Finset I) => x i))
      ((Measure.pi μ).map (fun x : I → Ω => fun i : (Finset.univ : Finset I) => x i)) = _ at hh
    rw [ProductRestrictionLaw μ Finset.univ] at hh
    exact hh

  classical
  let s := (Finset.univ : Finset I).erase i
  let t := ({i} : Finset I)
  let F : (I → Ω) → (s → Ω) × (t → Ω) := fun x => ((fun j => x j), (fun j => x j))
  have hm : Measurable F :=
    (measurable_pi_lambda _ fun j => measurable_pi_apply j.val).prodMk
      (measurable_pi_lambda _ fun j => measurable_pi_apply j.val)
  let T := S.map F
  haveI : IsProbabilityMeasure T := Measure.isProbabilityMeasure_map hm.aemeasurable
  have ht : T.fst = S.map (fun x : I → Ω => fun j : s => x j) := by
    rw [Measure.fst, Measure.map_map measurable_fst hm]
    rfl
  have hd : Disjoint s t := by simp [s, t]
  have hu : s ∪ t = Finset.univ := by
    dsimp [s, t]
    rw [Finset.union_singleton, Finset.insert_erase (Finset.mem_univ i)]
  have he := DisjointBlockMarginalEntropy μ S s t hd
  change klDiv T ((Measure.pi (fun j : s => μ j)).prod (Measure.pi (fun j : t => μ j))) = _ at he
  rw [hu, full_coordinate_local μ S] at he
  have hc := klDiv_compProd_eq_add T.fst (Measure.pi (fun j : s => μ j))
    T.condKernel (Kernel.const (s → Ω) (Measure.pi (fun j : t => μ j)))
  rw [T.disintegrate T.condKernel, Measure.compProd_const, Measure.compProd_const,
    ht, he] at hc
  exact hc
