import Tablet.ConfigurationCalculus
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
open MeasureTheory
open scoped ContDiff
-- [TABLET NODE: ConditionalFisherAggregation]
theorem ConditionalFisherAggregation (d N:ℕ)(P:Measure (Configuration d N))
    [IsFiniteMeasure P] (K:Fin N→Configuration d N→Measure (UnitAddTorus (Fin d)))
    (hrow:∀i:Fin N,∀F:Configuration d N→ℝ,Measurable F→
      (∃C:ℝ,∀X,|F X|≤C)→
      Integrable (fun X=>∫z,F (Replacement X i z)∂K i X) P ∧
      (∫X,∫z,F (Replacement X i z)∂K i X∂P)=(∫X,F X∂P))
    (f:Configuration d N→ℝ)(hf:f∈SmoothCore d N) :
    (∀i:Fin N,Integrable (fun X=>∫z,‖TorusGradient (fun y=>f (Replacement X i y)) z‖^2∂K i X) P) ∧
      (∑i:Fin N,∫X,∫z,‖TorusGradient (fun y=>f (Replacement X i y)) z‖^2∂K i X∂P)=
        PhysicalEnergy P f := by
-- BODY
  classical
  have configurationLift_quotient (d N : ℕ) :
      IsOpenQuotientMap (ConfigurationLift d N) := by
    have hc : IsOpenQuotientMap ((↑) : ℝ → AddCircle (1 : ℝ)) :=
      QuotientAddGroup.isOpenQuotientMap_mk
    have hp : IsOpenQuotientMap
        (Pi.map (fun _ : Fin N × Fin d => ((↑) : ℝ → AddCircle (1 : ℝ)))) :=
      IsOpenQuotientMap.piMap (fun _ => hc)
    have he := (PiLp.homeomorph 2 (fun _ : Fin N × Fin d => ℝ)).isOpenQuotientMap
    have hh := (Homeomorph.piCurry (X := Fin N) (Y := Fin d)
      (Z := AddCircle (1 : ℝ))).isOpenQuotientMap
    exact hh.comp (hp.comp he)

  have smoothCore_continuous {d N : ℕ} {f : Configuration d N → ℝ}
      (hf : f ∈ SmoothCore d N) : Continuous f := by
    apply (configurationLift_quotient d N).continuous_comp_iff.mp
    exact (show ContDiff ℝ ∞ (fun y => f (ConfigurationLift d N y)) from hf).continuous

  have smoothCore_bounded {d N : ℕ} {f : Configuration d N → ℝ}
      (hf : f ∈ SmoothCore d N) : ∃ C : ℝ, ∀ X, |f X| ≤ C := by
    have hc := (smoothCore_continuous hf).abs
    rcases isCompact_univ.exists_isMaxOn Set.univ_nonempty hc.continuousOn with ⟨X0,hX0,hmax⟩
    exact ⟨|f X0|, fun X => hmax (Set.mem_univ X)⟩

  -- Derivative descent is the only remaining topological step.
  have lift_translation_eq {d N : ℕ} (y z : EuclideanSpace ℝ (Fin N × Fin d))
      (h : ConfigurationLift d N y = ConfigurationLift d N z)
      (x : EuclideanSpace ℝ (Fin N × Fin d)) :
      ConfigurationLift d N (x + (z-y)) = ConfigurationLift d N x := by
    funext i j
    have hj := congrFun (congrFun h i) j
    change (y (i,j) : AddCircle (1 : ℝ)) = (z (i,j) : AddCircle (1 : ℝ)) at hj
    simp only [ConfigurationLift, PiLp.add_apply, PiLp.sub_apply]
    rw [AddCircle.coe_add, AddCircle.coe_sub, ← hj, sub_self, add_zero]

  have lift_fderiv_eq {d N : ℕ} (f : Configuration d N → ℝ)
      (y z : EuclideanSpace ℝ (Fin N × Fin d))
      (h : ConfigurationLift d N y = ConfigurationLift d N z) :
      fderiv ℝ (fun x => f (ConfigurationLift d N x)) y =
        fderiv ℝ (fun x => f (ConfigurationLift d N x)) z := by
    let q := fun x => f (ConfigurationLift d N x)
    have hfun : (fun x => q (x+(z-y))) = q := by
      funext x
      exact congrArg f (lift_translation_eq y z h x)
    have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := q) (x := y) (z-y)
    rw [hfun] at hd
    simpa using hd

  have coordinateGradient_on_lift {d N : ℕ} (f : Configuration d N → ℝ)
      (y : EuclideanSpace ℝ (Fin N × Fin d)) (ij : Fin N × Fin d) :
      CoordinateGradient f (ConfigurationLift d N y) ij =
        fderiv ℝ (fun x => f (ConfigurationLift d N x)) y
          (EuclideanSpace.single ij 1) := by
    let z : EuclideanSpace ℝ (Fin N × Fin d) := WithLp.toLp 2
      (fun ij => (AddCircle.equivIco (1 : ℝ) 0 (ConfigurationLift d N y ij.1 ij.2) : ℝ))
    have hz : ConfigurationLift d N z = ConfigurationLift d N y := by
      funext i j
      simp [ConfigurationLift, z, AddCircle.coe_equivIco]
    change fderiv ℝ (fun x => f (ConfigurationLift d N x)) z (EuclideanSpace.single ij 1) = _
    rw [lift_fderiv_eq f z y hz]

  have cg:Continuous (CoordinateGradient f):=by
    apply (configurationLift_quotient d N).continuous_comp_iff.mp
    have hF:ContDiff ℝ ∞ (fun y=>f (ConfigurationLift d N y)):=hf
    have he:(fun y=>CoordinateGradient f (ConfigurationLift d N y))=
        (fun y:EuclideanSpace ℝ (Fin N×Fin d)=>WithLp.toLp 2
          (fun ij=>fderiv ℝ (fun x=>f (ConfigurationLift d N x)) y (EuclideanSpace.single ij 1))):=by
      funext y
      ext ij
      exact coordinateGradient_on_lift f y ij
    change Continuous (fun y => CoordinateGradient f (ConfigurationLift d N y))
    rw[he]
    apply (PiLp.continuous_toLp 2 (fun _:Fin N×Fin d=>ℝ)).comp
    apply continuous_pi
    intro ij
    exact (hF.continuous_fderiv_apply (by simp)).comp
      (continuous_id.prodMk continuous_const)
  let e:=fun (i:Fin N)(X:Configuration d N)=>∑j:Fin d,(CoordinateGradient f X (i,j))^2
  have ec:∀i:Fin N,Continuous (e i):=by
    intro i
    apply continuous_finsetSum
    intro j hj
    exact ((PiLp.continuous_apply 2 (fun _ : Fin N×Fin d=>ℝ) (i,j)).comp cg).pow 2
  have eb:∀i:Fin N,∃C:ℝ,∀X,|e i X|≤C:=by
    intro i
    obtain ⟨C,hC⟩:=isCompact_univ.exists_bound_of_continuousOn (ec i).continuousOn
    exact ⟨C,fun X=>by simpa only [Real.norm_eq_abs] using hC X (Set.mem_univ X)⟩
  have ei:∀i:Fin N,Integrable (e i) P:=fun i=>(ec i).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hcalc:=(ConfigurationCalculus d N).2.2.2 f hf
  have hsplit:∀X i z,‖TorusGradient (fun y=>f (Replacement X i y)) z‖^2=
      e i (Replacement X i z):=by
    intro X i z
    exact (hcalc.2.2.2.2.2.2.1 X i).2 z
  have hsum:∀X,∑i:Fin N,e i X=‖CoordinateGradient f X‖^2:=by
    intro X
    exact (hcalc.2.2.2.2.2.2.2 X).symm
  have hd:∀i:Fin N,Integrable (fun X=>∫z,e i (Replacement X i z)∂K i X) P ∧
      (∫X,∫z,e i (Replacement X i z)∂K i X∂P)=(∫X,e i X∂P):=
    fun i=>hrow i (e i) (ec i).measurable (eb i)
  constructor
  · intro i
    simp_rw[hsplit]
    exact (hd i).1
  · simp_rw[hsplit, (hd _).2]
    rw[←integral_finsetSum _ (fun i _=>ei i)]
    simp_rw[hsum]
    rfl
