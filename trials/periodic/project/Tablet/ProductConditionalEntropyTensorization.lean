import Tablet.ProductDeletionConditionalEntropy
import Tablet.FiniteProductEntropyShearer
open MeasureTheory InformationTheory

-- [TABLET NODE: ProductConditionalEntropyTensorization]
theorem ProductConditionalEntropyTensorization {I Ω : Type*}
    [Fintype I] [DecidableEq I] [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    (μ : I → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (S : Measure (I → Ω)) [IsProbabilityMeasure S]
    (hS : klDiv S (Measure.pi μ) ≠ ⊤) :
    (klDiv S (Measure.pi μ)).toReal ≤
      ∑ i : I, (klDiv
        (S.map (fun x : I → Ω => ((fun j : (Finset.univ : Finset I).erase i => x j),
          (fun j : ({i} : Finset I) => x j))))
        ((S.map (fun x : I → Ω => fun j : (Finset.univ : Finset I).erase i => x j)).prod
          (Measure.pi (fun j : ({i} : Finset I) => μ j)))).toReal := by
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
  have full_shearer_local 
          
      (μ : I → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
      (S : Measure (I → Ω)) [IsProbabilityMeasure S]
      (hS : klDiv S (Measure.pi μ) ≠ ⊤) :
      (∑ i : I, (klDiv (S.map (fun x : I → Ω => fun j : (Finset.univ : Finset I).erase i => x j))
        (Measure.pi (fun j : (Finset.univ : Finset I).erase i => μ j))).toReal) ≤
      ((Fintype.card I : ℝ)-1) * (klDiv S (Measure.pi μ)).toReal := by

    have hh := FiniteProductEntropyShearer μ S hS Finset.univ
    simpa only [Finset.card_univ, full_coordinate_local μ S] using hh

  classical
  let H := (klDiv S (Measure.pi μ)).toReal
  let D := fun i : I => klDiv
    (S.map (fun x : I → Ω => fun j : (Finset.univ : Finset I).erase i => x j))
    (Measure.pi (fun j : (Finset.univ : Finset I).erase i => μ j))
  let C := fun i : I => klDiv
    (S.map (fun x : I → Ω => ((fun j : (Finset.univ : Finset I).erase i => x j),
      (fun j : ({i} : Finset I) => x j))))
    ((S.map (fun x : I → Ω => fun j : (Finset.univ : Finset I).erase i => x j)).prod
      (Measure.pi (fun j : ({i} : Finset I) => μ j)))
  have he (i : I) : H = (D i).toReal + (C i).toReal := by
    have hh := ProductDeletionConditionalEntropy μ S i
    change klDiv S (Measure.pi μ) = D i + C i at hh
    have hf : D i + C i ≠ ⊤ := hh ▸ hS
    have hr := congrArg ENNReal.toReal hh
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.mp hf).1 (ENNReal.add_ne_top.mp hf).2] at hr
    exact hr
  have hsum : (Fintype.card I : ℝ) * H = (∑ i : I, (D i).toReal) + ∑ i : I, (C i).toReal := by
    calc
      _ = ∑ i : I, H := by simp
      _ = ∑ i : I, ((D i).toReal + (C i).toReal) := Finset.sum_congr rfl fun i _ => he i
      _ = _ := Finset.sum_add_distrib
  have hs := full_shearer_local μ S hS
  change (∑ i : I, (D i).toReal) ≤ ((Fintype.card I : ℝ)-1)*H at hs
  change H ≤ ∑ i : I, (C i).toReal
  nlinarith
