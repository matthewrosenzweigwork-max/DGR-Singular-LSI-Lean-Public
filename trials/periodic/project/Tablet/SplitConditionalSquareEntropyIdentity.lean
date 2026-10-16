module

public import Tablet.ConditionalSquareRelativeEntropy
public import Tablet.EntropyPushforwardEquivalence
public import Tablet.MeasurePreservingDensityTransport
public import Tablet.SplitCoordinateEquivalence

@[expose] public section
universe u
open MeasureTheory ProbabilityTheory InformationTheory
-- [TABLET NODE: SplitConditionalSquareEntropyIdentity]
theorem SplitConditionalSquareEntropyIdentity {I Ω:Type u}[Fintype I][DecidableEq I][MeasurableSpace Ω]
    [StandardBorelSpace Ω][Nonempty Ω]
    (P:Measure (I→Ω))[IsProbabilityMeasure P](i:I)
    (κ:Kernel ((Finset.univ:Finset I).erase i→Ω) (({i}:Finset I)→Ω))[IsMarkovKernel κ]
    (K:(I→Ω)→Measure Ω)
    (hproj:∀X,(κ (fun j:((Finset.univ:Finset I).erase i)=>X j)).map
      (MeasurableEquiv.funUnique ({i}:Finset I) Ω)=K X)
    (hdis:P.map (SplitCoordinateEquivalence i)=(P.map (SplitCoordinateEquivalence i)).fst⊗ₘκ)
    (f:(I→Ω)→ℝ)(hf:Measurable f)(R:ℝ)(hR:∀X,|f X|≤R)(ha:0<∫X,f X^2∂P) :
    let a:=∫X,f X^2∂P
    let S:=P.withDensity (fun X=>ENNReal.ofReal (f X^2/a))
    let T:=S.map (SplitCoordinateEquivalence i)
    klDiv T (T.fst⊗ₘκ)≠⊤ ∧
      a*(klDiv T (T.fst⊗ₘκ)).toReal=
      ∫X,Entropy (K X) (fun z=>f (Function.update X i z)^2)∂P := by
-- BODY
  have density_equiv_local {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y]
      (μ : Measure X) (e : X ≃ᵐ Y) (w : X → ENNReal) (hw : Measurable w) :
      (μ.withDensity w).map e = (μ.map e).withDensity (fun y => w (e.symm y)) := by
    have hp : MeasurePreserving e μ (μ.map e) := ⟨e.measurable, rfl⟩
    have hh := MeasurePreservingDensityTransport μ (μ.map e) e hp
      (fun y => w (e.symm y)) (hw.comp e.symm.measurable)
    simpa only [Function.comp_def, MeasurableEquiv.symm_apply_apply] using hh
  have replacement_eval_local    
      (x : I → Ω) (i : I) (z : Ω) :
      SplitCoordinateEquivalence i (Function.update x i z) =
        ((fun j : (Finset.univ : Finset I).erase i => x j),(fun _ : ({i} : Finset I) => z)) ∧
      (SplitCoordinateEquivalence i).symm
        ((fun j : (Finset.univ : Finset I).erase i => x j),(fun _ : ({i} : Finset I) => z)) =
        Function.update x i z := by

    classical
    have hf : SplitCoordinateEquivalence i (Function.update x i z) =
        ((fun j : (Finset.univ : Finset I).erase i => x j),(fun _ : ({i} : Finset I) => z)) := by
      change ((fun j : (Finset.univ : Finset I).erase i => Function.update x i z j),
        (fun j : ({i} : Finset I) => Function.update x i z j)) = _
      apply Prod.ext
      · funext j
        exact Function.update_of_ne (Finset.ne_of_mem_erase j.property) z x
      · funext j
        have hj : j.val=i := Finset.mem_singleton.mp j.property
        change Function.update x i z j.val = z
        rw [hj,Function.update_self]
    refine ⟨hf,?_⟩
    apply (SplitCoordinateEquivalence i).injective
    rw [MeasurableEquiv.apply_symm_apply]
    exact hf.symm

  classical
  let e:=SplitCoordinateEquivalence (Ω:=Ω) i
  let P':=P.map e
  haveI:IsProbabilityMeasure P':=Measure.isProbabilityMeasure_map e.measurable.aemeasurable
  let μ:=P'.fst
  haveI:IsProbabilityMeasure μ:=inferInstance
  let F:=fun p=>f (e.symm p)
  let a:=∫X,f X^2∂P
  let S:=P.withDensity (fun X=>ENNReal.ofReal (f X^2/a))
  let T:=S.map e
  have hF:Measurable F:=hf.comp e.symm.measurable
  have hFR:∀p,|F p|≤R:=fun p=>hR _
  have hPe:P'=μ⊗ₘκ:=hdis
  have haeq:(∫p,F p^2∂μ⊗ₘκ)=a:=by
    rw[←hPe]
    change (∫p,F p^2∂P.map e)=a
    rw[integral_map_equiv e]
    simp [F,a]
  have hTe:T=(μ⊗ₘκ).withDensity (fun p=>ENNReal.ofReal (F p^2/(∫p,F p^2∂μ⊗ₘκ))):=by
    rw[haeq,←hPe]
    exact density_equiv_local P e (fun X=>ENNReal.ofReal (f X^2/a))
      ((hf.pow_const 2).div_const a).ennreal_ofReal
  have hc:=ConditionalSquareRelativeEntropy μ κ F hF R hFR (by rw[haeq];exact ha)
  dsimp only at hc
  rw[←hTe,haeq] at hc
  refine ⟨hc.2.1,hc.2.2.trans ?_⟩
  let Φ:=fun x=>Entropy (κ x) (fun y=>F (x,y)^2)
  have hΦm:Measurable Φ:=by
    have hm:Measurable (fun x=>∫y,F (x,y)^2∂κ x):=
      ((hF.pow_const 2).stronglyMeasurable.integral_kernel_prod_right').measurable
    have hl:Measurable (fun x=>∫y,F (x,y)^2*Real.log (F (x,y)^2)∂κ x):=
      (((hF.pow_const 2).mul ((hF.pow_const 2).log)).stronglyMeasurable.integral_kernel_prod_right').measurable
    exact hl.sub (hm.mul hm.log)
  have hmap:(∫x,Φ x∂μ)=∫p,Φ p.1∂P':=
    integral_map (μ:=P') measurable_fst.aemeasurable hΦm.aestronglyMeasurable
  rw[hmap]
  change (∫p,Φ p.1∂P.map e)=_
  rw[integral_map_equiv e]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun X=>by
    let es:=MeasurableEquiv.funUnique ({i}:Finset I) Ω
    have hrow:=EntropyPushforwardEquivalence (κ (e X).1) es
      (fun z=>f (Function.update X i z)^2)
    have hproj':(κ (e X).1).map es=K X:=hproj X
    rw[hproj'] at hrow
    change Entropy (κ (e X).1) (fun y=>F ((e X).1,y)^2)=Entropy (K X) (fun z=>f (Function.update X i z)^2)
    rw[hrow]
    apply congrArg (Entropy (κ (e X).1))
    funext y
    have hy:y=(fun _:({i}:Finset I)=>es y):=by
      funext j
      have hj:j=(⟨i,by simp⟩:({i}:Finset I)):=Subtype.ext (Finset.mem_singleton.mp j.property)
      rw[hj]
      rfl
    have he:e.symm ((e X).1,y)=Function.update X i (es y):=by
      rw[hy]
      exact (replacement_eval_local X i (es y)).2
    simp only[Φ,F,Function.comp_apply]
    rw[he]
