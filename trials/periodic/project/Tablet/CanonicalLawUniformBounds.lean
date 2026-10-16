module

public import Tablet.RieszL1Foundation
public import Tablet.GibbsNormalizerBounds

@[expose] public section
open MeasureTheory Filter Set
-- [TABLET NODE: CanonicalLawUniformBounds]
theorem CanonicalLawUniformBounds (d N : ℕ) (hd : 2≤d) (hN : 2≤N)
    (s a l u β : ℝ) (hs : 0≤s) (hsd : s<(d:ℝ)) (ha : 0<a)
    (q : BoundedBackground d l u) (hβ : 0≤β) :
    ∃ L M : ℝ, 0<L ∧ 0≤M ∧ ∀ε:ℝ,0≤ε →
      Measurable (GibbsWeight (N := N) (RieszKernel d s a ε) q.density β) ∧
      Integrable (GibbsWeight (N := N) (RieszKernel d s a ε) q.density β) volume ∧
      L ≤ (∫X,GibbsWeight (N := N) (RieszKernel d s a ε) q.density β X) ∧
      (∀ᵐX:Configuration d N∂volume,
        0≤GibbsWeight (RieszKernel d s a ε) q.density β X ∧
        GibbsWeight (RieszKernel d s a ε) q.density β X≤M) ∧
      IsProbabilityMeasure (CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β) := by
-- BODY
  have pair_measurable {d N : ℕ} (g : UnitAddTorus (Fin d) → ℝ) (hg : Measurable g) :
      Measurable (PairEnergy (N := N) g) := by
    unfold PairEnergy
    refine measurable_const.mul (Finset.measurable_fun_sum _ fun i _ => ?_)
    refine Finset.measurable_fun_sum _ fun j _ => ?_
    split_ifs
    · exact hg.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))
    · exact measurable_const
  have raw_measurable {d N : ℕ} (g q : UnitAddTorus (Fin d) → ℝ)
      (hg : Measurable g) (hq : Measurable q) (β : ℝ) :
      Measurable (GibbsWeight (N := N) g q β) := by
    unfold GibbsWeight ProductDensity
    exact (measurable_const.mul (pair_measurable g hg)).exp.mul
      (Finset.measurable_fun_prod _ fun i _ => hq.comp (measurable_pi_apply i))
  have pair_lower {d N : ℕ} (hN : 0<N) (g : UnitAddTorus (Fin d) → ℝ)
      (c : ℝ) (hc : 0≤c) (hg : ∀x,-c≤g x) (X : Configuration d N) :
      -c*N ≤ PairEnergy g X := by
    have hsum : -c*(N:ℝ)^2 ≤ ∑i:Fin N,∑j:Fin N,if i<j then g (X i-X j) else 0 := by
      calc
        _ = ∑i:Fin N,∑j:Fin N,-c := by simp;ring
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          split_ifs
          · exact hg _
          · linarith
    have hNr : 0<(N:ℝ) := by exact_mod_cast hN
    have h := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hNr.le)
    unfold PairEnergy
    calc
      -c*N = (N:ℝ)⁻¹*(-c*(N:ℝ)^2) := by field_simp <;> ring
      _ ≤ _ := h
  obtain ⟨c,hc,hall⟩ := RieszL1Foundation d hd s a hs hsd ha
  let k : ℝ := β*((N:ℝ)-1)/2*u^2
  let L : ℝ := Real.exp (-k*(∫x,|RieszKernel d s a 0 x|))
  let M : ℝ := Real.exp (β*c*N)*u^N
  have hu : 0≤u := zero_le_one.trans q.one_le_upper
  refine ⟨L,M,Real.exp_pos _,by dsimp [M];positivity,?_⟩
  intro ε hε
  obtain ⟨hgm,hgi,hmean,hge,hgl,hga,hgs⟩ := hall ε hε
  have hgb := GibbsNormalizerBounds d N hN l u q (RieszKernel d s a ε) hgm hgi c β hc hβ
    (Eventually.of_forall hgl)
  have hk : 0≤k := by
    have hh : 2≤(N:ℝ) := by exact_mod_cast hN
    have hn : 0≤(N:ℝ)-1 := by linarith
    dsimp [k]
    positivity
  have hlower : L ≤ ∫X,GibbsWeight (N := N) (RieszKernel d s a ε) q.density β X := by
    calc
      L ≤ Real.exp (-k*(∫x,|RieszKernel d s a ε x|)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hga (neg_nonpos.mpr hk))
      _ = Real.exp (-β*((N:ℝ)-1)/2*u^2*(∫x,|RieszKernel d s a ε x|)) := by
        congr 1
        dsimp [k]
        ring
      _ ≤ _ := hgb.2.1
  refine ⟨raw_measurable _ _ hgm q.measurable β,hgb.1,hlower,?_,hgb.2.2.2⟩
  filter_upwards [(ProductBackgroundFacts d N l u q).2.2.2] with X hX
  have hQ : 0≤ProductDensity q.density X := (pow_nonneg q.lower_pos.le N).trans hX.1
  have hA := pair_lower (by omega : 0<N) (RieszKernel d s a ε) c hc hgl X
  have hex : Real.exp (-β*PairEnergy (RieszKernel d s a ε) X) ≤ Real.exp (β*c*N) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hA hβ]
  exact ⟨mul_nonneg (Real.exp_nonneg _) hQ,
    mul_le_mul hex hX.2 hQ (Real.exp_nonneg _)⟩
