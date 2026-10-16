import Tablet.Preamble
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
open MeasureTheory Filter
set_option autoImplicit false

universe u v
-- [TABLET NODE: RawL2OperatorDescent]
theorem RawL2OperatorDescent {α : Type u} [MeasurableSpace α] {μ : Measure α}
    {Ω : Type v} [MeasurableSpace Ω] {η : Measure Ω}
    (T : (α → ℝ) → Ω → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hmem : ∀ f, MemLp f 2 μ → MemLp (T f) 2 η)
    (hae : ∀ f g, MemLp f 2 μ → MemLp g 2 μ → f =ᵐ[μ] g → T f =ᵐ[η] T g)
    (hadd : ∀ f g, MemLp f 2 μ → MemLp g 2 μ → T (f + g) =ᵐ[η] T f + T g)
    (hsmul : ∀ (c : ℝ) f, MemLp f 2 μ → T (c • f) =ᵐ[η] c • T f)
    (hbound : ∀ f (hf : MemLp f 2 μ),
      ‖(hmem f hf).toLp (T f)‖ ≤ C * ‖hf.toLp f‖) :
    ∃! L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 η,
      ‖L‖ ≤ C ∧ ∀ f (hf : MemLp f 2 μ), L (hf.toLp f) =ᵐ[η] T f := by
-- BODY
  let A : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 η :=
    { toFun := fun v => (hmem v (Lp.memLp v)).toLp (T v)
      map_add' := by
        intro v w
        apply Lp.ext
        calc
          ⇑((hmem ⇑(v + w) (Lp.memLp (v + w))).toLp (T ⇑(v + w)))
              =ᵐ[η] T ⇑(v + w) := MemLp.coeFn_toLp _
          _ =ᵐ[η] T (⇑v + ⇑w) :=
            hae _ _ (Lp.memLp (v + w)) ((Lp.memLp v).add (Lp.memLp w)) (Lp.coeFn_add v w)
          _ =ᵐ[η] T v + T w := hadd _ _ (Lp.memLp v) (Lp.memLp w)
          _ =ᵐ[η] ⇑((hmem v (Lp.memLp v)).toLp (T v) +
              (hmem w (Lp.memLp w)).toLp (T w)) :=
            ((Lp.coeFn_add _ _).trans
              ((MemLp.coeFn_toLp _).add (MemLp.coeFn_toLp _))).symm
      map_smul' := by
        intro c v
        apply Lp.ext
        calc
          ⇑((hmem ⇑(c • v) (Lp.memLp (c • v))).toLp (T ⇑(c • v)))
              =ᵐ[η] T ⇑(c • v) := MemLp.coeFn_toLp _
          _ =ᵐ[η] T (c • ⇑v) :=
            hae _ _ (Lp.memLp (c • v)) ((Lp.memLp v).const_smul c) (Lp.coeFn_smul c v)
          _ =ᵐ[η] c • T v := hsmul c _ (Lp.memLp v)
          _ =ᵐ[η] ⇑(c • (hmem v (Lp.memLp v)).toLp (T v)) :=
            ((Lp.coeFn_smul _ _).trans
              ((MemLp.coeFn_toLp _).const_smul c)).symm }
  have hAbound : ∀ v, ‖A v‖ ≤ C * ‖v‖ := by
    intro v
    simpa only [A, LinearMap.coe_mk, AddHom.coe_mk, Lp.toLp_coeFn] using hbound v (Lp.memLp v)
  let L := A.mkContinuous C hAbound
  have hrepr : ∀ f (hf : MemLp f 2 μ), L (hf.toLp f) =ᵐ[η] T f := by
    intro f hf
    exact (MemLp.coeFn_toLp (hmem (hf.toLp f) (Lp.memLp (hf.toLp f)))).trans
      (hae _ _ (Lp.memLp (hf.toLp f)) hf hf.coeFn_toLp)
  refine ⟨L, ⟨LinearMap.mkContinuous_norm_le A hC hAbound, hrepr⟩, ?_⟩
  intro M hM
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  simpa only [Lp.toLp_coeFn] using
    (hM.2 v (Lp.memLp v)).trans (hrepr v (Lp.memLp v)).symm
