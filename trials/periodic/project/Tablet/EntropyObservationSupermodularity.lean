module

public import Tablet.ConditionalEntropyUnderObservation
public import Mathlib.InformationTheory.KullbackLeibler.ChainRule
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

-- [TABLET NODE: EntropyObservationSupermodularity]
theorem EntropyObservationSupermodularity {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [StandardBorelSpace Z] [Nonempty Z]
    (S : Measure (X × Z)) (ν : Measure X) (η : Measure Z)
    [IsProbabilityMeasure S] [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (f : X → Y) (hf : Measurable f) :
    klDiv S.fst ν + klDiv (S.map (Prod.map f id)) ((ν.map f).prod η) ≤
      klDiv S (ν.prod η) + klDiv (S.fst.map f) (ν.map f) := by
-- BODY
  let T : Measure (Y × Z) := S.map (Prod.map f id)
  have hTf : T.fst = S.fst.map f := by
    dsimp [T]
    rw [Measure.fst, Measure.map_map measurable_fst (hf.prodMap measurable_id),
      Measure.fst, Measure.map_map hf measurable_fst]
    rfl
  have hc := ConditionalEntropyUnderObservation S.fst η S.condKernel f hf
  rw [S.disintegrate S.condKernel] at hc
  have hS := klDiv_compProd_eq_add S.fst ν S.condKernel (Kernel.const X η)
  rw [S.disintegrate S.condKernel, Measure.compProd_const, Measure.compProd_const] at hS
  have hT := klDiv_compProd_eq_add T.fst (ν.map f) T.condKernel (Kernel.const Y η)
  rw [T.disintegrate T.condKernel, Measure.compProd_const, Measure.compProd_const] at hT
  change klDiv T ((S.fst.map f).prod η) ≤ klDiv S (S.fst.prod η) at hc
  rw [hS, show S.map (Prod.map f id) = T from rfl, hT, hTf]
  calc
    _ ≤ klDiv S.fst ν +
        (klDiv (S.fst.map f) (ν.map f) + klDiv S (S.fst.prod η)) :=
      add_le_add (le_refl _) (add_le_add (le_refl _) hc)
    _ = _ := by ac_rfl
