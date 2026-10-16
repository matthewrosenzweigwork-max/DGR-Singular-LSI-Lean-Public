module

public import Tablet.Preamble
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section
open MeasureTheory
-- [TABLET NODE: IndependentShiftPushforward]
theorem IndependentShiftPushforward {T : Type*} [MeasurableSpace T] [Add T] [MeasurableAdd₂ T]
    (N : ℕ) (μ η ν : Measure T) [IsProbabilityMeasure μ] [IsProbabilityMeasure η] [IsProbabilityMeasure ν]
    (hshift : Measure.map (fun p:T×T=>p.1+p.2) (μ.prod η)=ν) :
    Measure.map (fun p:(Fin N→T)×(Fin N→T)=>fun i=>p.1 i+p.2 i)
      ((Measure.pi fun _:Fin N=>μ).prod (Measure.pi fun _:Fin N=>η))=
      Measure.pi (fun _:Fin N=>ν) := by
-- BODY
  let E:=MeasurableEquiv.arrowProdEquivProdArrow T T (Fin N)
  have hE:=measurePreserving_arrowProdEquivProdArrow T T (Fin N) (fun _=>μ) (fun _=>η)
  have hadd:Measurable (fun p:T×T=>p.1+p.2):=measurable_fst.add measurable_snd
  haveI (i:Fin N):SigmaFinite ((μ.prod η).map (fun p:T×T=>p.1+p.2)):=by rw [hshift];infer_instance
  have hp:=Measure.pi_map_pi (μ:=fun _:Fin N=>μ.prod η) (f:=fun _ p=>p.1+p.2) (fun _=>hadd.aemeasurable)
  have hm:Measurable (fun p:(Fin N→T)×(Fin N→T)=>fun i=>p.1 i+p.2 i):=by fun_prop
  rw [←hE.map_eq,Measure.map_map hm hE.measurable]
  rw [hshift] at hp
  convert hp using 1
  congr 1
