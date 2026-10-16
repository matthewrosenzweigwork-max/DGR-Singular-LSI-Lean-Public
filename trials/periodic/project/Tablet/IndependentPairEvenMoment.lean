module

public import Tablet.FiniteRademacherEvenMoment
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section
open MeasureTheory
open scoped BigOperators
-- [TABLET NODE: IndependentPairEvenMoment]
theorem IndependentPairEvenMoment {Ω:Type*}[MeasurableSpace Ω]
    (N:ℕ)(μ:Fin N→Measure Ω)[∀i,IsProbabilityMeasure (μ i)]
    (Z:Fin N→Ω→ℝ)(hZ:∀i,Measurable (Z i))(m:ℕ)(hm:1≤m)
    (hi:Integrable (fun v:Fin N→Ω×Ω=>(∑i:Fin N,(Z i (v i).1-Z i (v i).2)^2)^m)
      (Measure.pi (fun i=>(μ i).prod (μ i)))) :
    (∫v:Fin N→Ω×Ω,(∑i:Fin N,(Z i (v i).1-Z i (v i).2))^(2*m)
      ∂Measure.pi (fun i=>(μ i).prod (μ i)))≤
    (6*(m:ℝ))^m*(∫v:Fin N→Ω×Ω,(∑i:Fin N,(Z i (v i).1-Z i (v i).2)^2)^m
      ∂Measure.pi (fun i=>(μ i).prod (μ i))) := by
-- BODY
  classical
  let P:=Measure.pi (fun i=>(μ i).prod (μ i))
  let D:=fun (v:Fin N→Ω×Ω)(i:Fin N)=>Z i (v i).1-Z i (v i).2
  let F:=fun (σ:Fin N→Bool)(v:Fin N→Ω×Ω)=>(∑i:Fin N,(if σ i then 1 else -1)*D v i)^(2*m)
  let C:ℝ:=Fintype.card (Fin N→Bool)
  let R:=fun v:Fin N→Ω×Ω=>(∑i:Fin N,(D v i)^2)^m
  have hCp:0<C:=by dsimp[C];exact_mod_cast Fintype.card_pos
  have hFn:∀σ v,0≤F σ v:=by intro σ v;dsimp[F];rw[pow_mul];exact pow_nonneg (sq_nonneg _) m
  have hFm:∀σ,Measurable (F σ):=by
    intro σ
    apply Measurable.pow_const
    apply Finset.measurable_fun_sum
    intro i hi
    exact measurable_const.mul (((hZ i).comp (measurable_fst.comp (measurable_pi_apply i))).sub
      ((hZ i).comp (measurable_snd.comp (measurable_pi_apply i))))
  have hpoint:∀v,C⁻¹*(∑σ:Fin N→Bool,F σ v)≤(6*(m:ℝ))^m*R v:=
    fun v=>FiniteRademacherEvenMoment N (D v) m hm
  have hFi:∀σ,Integrable (F σ) P:=by
    intro σ
    apply ((hi.const_mul ((6*(m:ℝ))^m)).const_mul C).mono' (hFm σ).aestronglyMeasurable
    filter_upwards [] with v
    rw[Real.norm_eq_abs,abs_of_nonneg (hFn σ v)]
    have hsingle:F σ v≤∑τ:Fin N→Bool,F τ v:=
      Finset.single_le_sum (fun τ _=>hFn τ v) (Finset.mem_univ σ)
    have hscale:=mul_le_mul_of_nonneg_left (hpoint v) hCp.le
    rw[←mul_assoc,mul_inv_cancel₀ hCp.ne',one_mul] at hscale
    exact hsingle.trans hscale
  have hswap:∀σ,∫v,F σ v∂P=∫v,F (fun _=>true) v∂P:=by
    intro σ
    let e:∀i:Fin N,(Ω×Ω)≃ᵐ(Ω×Ω):=fun i=>if σ i then MeasurableEquiv.refl _ else MeasurableEquiv.prodComm
    let E:=MeasurableEquiv.piCongrRight e
    have hmp:MeasurePreserving E P P:=by
      apply measurePreserving_pi
      intro i
      dsimp[e]
      split_ifs
      · exact MeasurePreserving.id _
      · exact Measure.measurePreserving_swap
    have hid:∀v,F (fun _=>true) (E v)=F σ v:=by
      intro v
      dsimp only [F]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      dsimp[F,D,E,MeasurableEquiv.piCongrRight,e]
      cases h:σ i <;>simp[h,MeasurableEquiv.prodComm,Equiv.prodComm] <;>ring
    have hh:=hmp.integral_comp E.measurableEmbedding (F (fun _=>true))
    simpa only[hid] using hh
  have hs: (∫v,F (fun _=>true) v∂P)=C⁻¹*(∑σ:Fin N→Bool,∫v,F σ v∂P):=by
    simp_rw[hswap]
    simp[C,hCp.ne']
  calc
    (∫v,(∑i:Fin N,D v i)^(2*m)∂P)=∫v,F (fun _=>true) v∂P:=by simp[F]
    _=C⁻¹*(∑σ:Fin N→Bool,∫v,F σ v∂P):=hs
    _=∫v,C⁻¹*(∑σ:Fin N→Bool,F σ v)∂P:=by
      rw[integral_const_mul,integral_finset_sum _ (fun σ _=>hFi σ)]
    _≤∫v,(6*(m:ℝ))^m*R v∂P:=
      integral_mono ((integrable_finset_sum _ (fun σ _=>hFi σ)).const_mul C⁻¹)
        (hi.const_mul _) hpoint
    _=(6*(m:ℝ))^m*(∫v,R v∂P):=integral_const_mul _ _
