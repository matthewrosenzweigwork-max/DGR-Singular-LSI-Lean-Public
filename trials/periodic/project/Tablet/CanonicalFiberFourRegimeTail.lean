import Tablet.CanonicalUStatisticNoInflationEvenMoment
import Tablet.GLZEvenMomentToTail
open MeasureTheory
universe u
-- [TABLET NODE: CanonicalFiberFourRegimeTail]
/-- Actual canonical tail with loose Hilbert/operator envelopes H=D=F.
This does not assert the sharp independent-H,D GLZ theorem. -/
theorem CanonicalFiberFourRegimeTail : ∃L:ℝ,1≤L ∧
    ∀{Ω:Type u} [MeasurableSpace Ω] (μ:Measure Ω) [IsProbabilityMeasure μ]
      (N:ℕ),0<N → ∀(q:Ω→Ω→ℝ),Measurable (fun v:Ω×Ω=>q v.1 v.2) →
      ∀(A F:ℝ),0<A → 0<F → (∀x y,|q x y|≤A) →
      (∀x,(∫y,q x y ∂μ)=0) → (∀y,(∫x,q x y ∂μ)=0) →
      (∀x,(∫y,(q x y)^2 ∂μ)≤F^2) → (∀y,(∫x,(q x y)^2 ∂μ)≤F^2) →
      ∀t:ℝ,0<t →
      (Measure.pi (fun _:Fin N=>μ)).real {X:Fin N→Ω |
        t≤|(∑i,∑j,if i=j then (0:ℝ) else q (X i) (X j))/(N:ℝ)|}≤
      L*Real.exp (-(1/L)*min (min (t^2/F^2) (t/F))
        (min (((N:ℝ)*t^2/F^2)^((3:ℝ)⁻¹)) (((N:ℝ)*t/A)^((2:ℝ)⁻¹)))) := by
-- BODY
  obtain ⟨L,hL,hTail⟩:=GLZEvenMomentToTail 1000000000 (by norm_num)
  refine ⟨L,hL,?_⟩
  intro Ω _ μ _ N hN q hq A F hA hF hb hc hc' hv hv' t ht
  classical
  let ν:=Measure.pi (fun _:Fin N=>μ)
  let U (X:Fin N→Ω):=∑i,∑j,if i=j then (0:ℝ) else q (X i) (X j)
  let S (X:Fin N→Ω):=U X/(N:ℝ)
  have hNp : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hUm : Measurable U := by
    apply Finset.measurable_fun_sum
    intro i hi
    apply Finset.measurable_fun_sum
    intro j hj
    by_cases h:i=j
    · simp only[h,ite_true];exact measurable_const
    · simp only[h,ite_false]
      have hp : Measurable (fun X : Fin N → Ω => (X i, X j)) :=
        (measurable_pi_apply i).prodMk (measurable_pi_apply j)
      exact hq.comp hp
  have hUb (X:Fin N→Ω):|U X|≤(N:ℝ)^2*A := by
    calc
      _≤∑i,|∑j,if i=j then (0:ℝ) else q (X i) (X j)| := Finset.abs_sum_le_sum_abs _ _
      _≤∑_:Fin N,(N:ℝ)*A := Finset.sum_le_sum fun i _=>by
        calc
          _≤∑j,|if i=j then (0:ℝ) else q (X i) (X j)| := Finset.abs_sum_le_sum_abs _ _
          _≤∑_:Fin N,A := Finset.sum_le_sum fun j _=>by
            split_ifs
            · simpa using hA.le
            · exact hb _ _
          _=_ := by simp
      _=_ := by simp;ring
  have hSb (X:Fin N→Ω):|S X|≤(N:ℝ)*A := by
    dsimp[S]
    rw[abs_div,abs_of_pos hNp]
    apply (div_le_iff₀ hNp).mpr
    simpa only[pow_two,mul_assoc,mul_comm,mul_left_comm] using hUb X
  let η:=Real.sqrt (N:ℝ)
  have hη : 0<η := Real.sqrt_pos.mpr hNp
  have hηsq : η^2=(N:ℝ) := Real.sq_sqrt hNp.le
  have hBsq : (F/η)^2=F^2/(N:ℝ) := by rw[div_pow,hηsq]
  have hAsq : (A/(N:ℝ))^2=A^2/(N:ℝ)^2 := div_pow _ _ _
  have hmom : ∀m:ℕ,1≤m → Integrable (fun X=>(S X)^(2*m)) ν ∧
      (∫X,(S X)^(2*m) ∂ν)≤
        (1000000000*((m:ℝ)*F^2+(m:ℝ)^2*F^2+(m:ℝ)^3*(F/η)^2+
          (m:ℝ)^4*(A/(N:ℝ))^2))^m := by
    intro m hm
    have hi : Integrable (fun X=>(S X)^(2*m)) ν :=
      Integrable.of_bound ((hUm.div_const _).pow_const _).aestronglyMeasurable
        (((N:ℝ)*A)^(2*m)) (Filter.Eventually.of_forall fun X=>by
          rw[Real.norm_eq_abs,abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (hSb X) _)
    refine ⟨hi,?_⟩
    have hb:=CanonicalUStatisticNoInflationEvenMoment μ N hN q hq A F hA hF hb hc hc' hv hv' m hm
    change (∫X,(S X)^(2*m) ∂ν)≤_ at hb
    apply hb.trans
    apply pow_le_pow_left₀ (by positivity)
    rw[hBsq,hAsq]
    have hx:0≤(m:ℝ)*F^2 := by positivity
    have he:(m:ℝ)^3*(F^2/(N:ℝ))=(m:ℝ)^3*F^2/(N:ℝ) := by ring
    have he':(m:ℝ)^4*(A^2/(N:ℝ)^2)=(m:ℝ)^4*A^2/(N:ℝ)^2 := by ring
    rw[he,he']
    nlinarith only[hx]
  have htail:=hTail ν S (A/(N:ℝ)) (F/η) F F (div_pos hA hNp) (div_pos hF hη) hF hF hmom t ht
  have hthird : t^2/(F/η)^2=(N:ℝ)*t^2/F^2 := by rw[hBsq];field_simp
  have hfourth : t/(A/(N:ℝ))=(N:ℝ)*t/A := by field_simp
  rw[hthird,hfourth] at htail
  exact htail
