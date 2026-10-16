module

public import Tablet.JumpConditionalBalance
public import Tablet.JumpL2Construction
public import Tablet.JumpConditionalL2Moments
public import Tablet.JumpL2VarianceEnergy

@[expose] public section
-- [TABLET NODE: JumpL2Extension]
theorem JumpL2Extension (d N : ℕ) (hN : 2 ≤ N) (l u β : ℝ)
    (q : BoundedBackground d l u) (hβ : 0 ≤ β)
    (G : UnitAddTorus (Fin d) → ℝ) (hG : Measurable G)
    (hGi : MeasureTheory.Integrable G MeasureTheory.volume)
    (hGn : ∀ x, 0 ≤ G x) (hGe : ∀ x, G (-x) = G x) :
    let P := CanonicalLaw (N := N) G q.density β
    let Z := fun (X : Configuration d N) (i : Fin N) =>
      ∫ z, Real.exp (-ConditionalPotential G β X i z) * q.density z
    let ν := fun (X : Configuration d N) (i : Fin N) =>
      NormalizedTilt MeasureTheory.volume
        (fun z => q.density z * Real.exp (-ConditionalPotential G β X i z))
    ∃! L : MeasureTheory.Lp ℝ 2 P →L[ℝ] MeasureTheory.Lp ℝ 2 P,
      ‖L‖ ≤ 2 * (N : ℝ) ∧
      (∀ v w, inner ℝ v (L w) = inner ℝ (L v) w) ∧
      (∀ v, L v = 0 ↔ ∃ c : ℝ, ∀ᵐ X ∂P, v X = c) ∧
      (∀ (f : Configuration d N → ℝ) (hf : MeasureTheory.MemLp f 2 P),
        MeasureTheory.MemLp (JumpOperator G q.density β f) 2 P ∧
        (⇑(L (hf.toLp f)) =ᵐ[P] JumpOperator G q.density β f) ∧
        (∀ i, ∀ᵐ X ∂P,
          MeasureTheory.MemLp (fun z => f (Replacement X i z)) 2 (ν X i)) ∧
        let E := -inner ℝ (hf.toLp f) (L (hf.toLp f))
        E = (1 / 2 : ℝ) * ∑ i : Fin N,
          ∫ X, (∫ z, Real.exp (-ConditionalPotential G β X i z) *
            (f (Replacement X i z) - f X)^2 * q.density z) ∂P ∧
        E = ∑ i : Fin N, ∫ X, Z X i *
          ProbabilityTheory.variance (fun z => f (Replacement X i z)) (ν X i) ∂P ∧
        0 ≤ E ∧ E ≤ 2 * (N : ℝ) * ‖hf.toLp f‖^2 ∧
        (E = 0 ↔ ∃ c : ℝ, ∀ᵐ X ∂P, f X = c)) := by
-- BODY
  classical
  intro P Z ν
  have hVar := JumpL2VarianceEnergy d N hN l u β q hβ G hG hGi hGn hGe
  obtain ⟨L, hL, hUnique⟩ := JumpL2Construction d N hN l u β q hβ G hG hGi hGn hGe
  refine ⟨L, ⟨hL.1, hL.2.1, hL.2.2.1, ?_⟩, ?_⟩
  · intro f hf
    obtain ⟨hm, hr, he, hp, hb, hz⟩ := hL.2.2.2 f hf
    have hfiber := JumpConditionalL2Moments d N hN l u β q hβ G hG hGi hGn hGe f hf
    refine ⟨hm, hr, ?_, he, he.trans (hVar f hf), hp, hb, hz⟩
    intro i
    exact (hfiber i).2.2.mono fun X hX => hX.1
  · intro M hM
    apply hUnique M
    refine ⟨hM.1, hM.2.1, hM.2.2.1, ?_⟩
    intro f hf
    obtain ⟨hm, hr, hfi, he, hv, hp, hb, hz⟩ := hM.2.2.2 f hf
    exact ⟨hm, hr, he, hp, hb, hz⟩

