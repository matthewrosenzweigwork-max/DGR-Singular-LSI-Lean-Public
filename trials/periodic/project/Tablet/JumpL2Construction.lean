module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Tablet.ReplacementJointBalance
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Tablet.JumpOperator
public import Tablet.ReplacementHaarInvariant

@[expose] public section

open MeasureTheory

-- [TABLET NODE: JumpL2Construction]
theorem JumpL2Construction (d N : ℕ) (hN : 2 ≤ N) (l u β : ℝ)
    (q : BoundedBackground d l u) (hβ : 0 ≤ β)
    (G : UnitAddTorus (Fin d) → ℝ) (hG : Measurable G)
    (hGi : Integrable G volume) (hGn : ∀ x, 0 ≤ G x)
    (hGe : ∀ x, G (-x) = G x) :
    let P := CanonicalLaw (N := N) G q.density β
    ∃! L : Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P,
      ‖L‖ ≤ 2 * (N : ℝ) ∧
      (∀ v w, inner ℝ v (L w) = inner ℝ (L v) w) ∧
      (∀ v, L v = 0 ↔ ∃ c : ℝ, ∀ᵐ X ∂P, v X = c) ∧
      (∀ f (hf : MemLp f 2 P),
        MemLp (JumpOperator G q.density β f) 2 P ∧
        L (hf.toLp f) =ᵐ[P] JumpOperator G q.density β f ∧
        let E := -inner ℝ (hf.toLp f) (L (hf.toLp f))
        E = (1 / 2 : ℝ) * ∑ i : Fin N,
          ∫ X, (∫ z, Real.exp (-ConditionalPotential G β X i z) *
            (f (Replacement X i z) - f X)^2 * q.density z) ∂P ∧
        0 ≤ E ∧ E ≤ 2 * (N : ℝ) * ‖hf.toLp f‖^2 ∧
        (E = 0 ↔ ∃ c : ℝ, ∀ᵐ X ∂P, f X = c)) := by
-- BODY
  classical
  have raw_operator_to_L2 {α : Type} [MeasurableSpace α] {μ : Measure α}
      {Ω : Type} [MeasurableSpace Ω] {η : Measure Ω}
      (T : (α → ℝ) → Ω → ℝ) (C : ℝ) (hC : 0 ≤ C)
      (hmem : ∀ f, MemLp f 2 μ → MemLp (T f) 2 η)
      (hae : ∀ f g, MemLp f 2 μ → MemLp g 2 μ → f =ᵐ[μ] g → T f =ᵐ[η] T g)
      (hadd : ∀ f g, MemLp f 2 μ → MemLp g 2 μ → T (f + g) =ᵐ[η] T f + T g)
      (hsmul : ∀ (c : ℝ) f, MemLp f 2 μ → T (c • f) =ᵐ[η] c • T f)
      (hbound : ∀ f (hf : MemLp f 2 μ),
        ‖(hmem f hf).toLp (T f)‖ ≤ C * ‖hf.toLp f‖) :
      ∃! L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 η,
        ‖L‖ ≤ C ∧ ∀ f (hf : MemLp f 2 μ), L (hf.toLp f) =ᵐ[η] T f := by
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

  have real_L2_inner_toLp {α : Type} [MeasurableSpace α] {μ : Measure α} (f g : α → ℝ)
      (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
      inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
    simp [hfx, hgx, mul_comm]

  have real_L2_norm_sq_toLp {α : Type} [MeasurableSpace α] {μ : Measure α} (f : α → ℝ) (hf : MemLp f 2 μ) :
      ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, real_L2_inner_toLp]
    simp_rw [pow_two]

  have dominated_marginal_pullback {α Ω : Type} [MeasurableSpace α] [MeasurableSpace Ω]
    {μ : Measure α} {J : Measure Ω} (r : Ω → α) (hr : AEMeasurable r J)
      (hdom : J.map r ≤ μ) (f : α → ℝ) (hf : MemLp f 2 μ) :
      MemLp (f ∘ r) 2 J ∧
        (∫ x, f (r x) ^ 2 ∂J) ≤ ∫ a, f a ^ 2 ∂μ := by
    have hfr : MemLp f 2 (J.map r) := MemLp.mono_measure hdom hf
    refine ⟨hfr.comp_of_map hr, ?_⟩
    rw [← integral_map hr hfr.integrable_sq.aestronglyMeasurable]
    exact integral_mono_measure hdom (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
      hf.integrable_sq

  have dominated_marginal_ae {α Ω : Type} [MeasurableSpace α] [MeasurableSpace Ω]
    {μ : Measure α} {J : Measure Ω} (r : Ω → α) (hr : AEMeasurable r J)
      (hdom : J.map r ≤ μ) {f g : α → ℝ} (hfg : f =ᵐ[μ] g) :
      f ∘ r =ᵐ[J] g ∘ r := by
    exact ae_eq_comp hr ((Measure.absolutelyContinuous_of_le hdom).ae_eq hfg)

  have dominated_marginal_difference {α Ω : Type} [MeasurableSpace α] [MeasurableSpace Ω]
    {μ : Measure α} {J : Measure Ω} (r s : Ω → α)
      (hr : AEMeasurable r J) (hs : AEMeasurable s J)
      (hdomr : J.map r ≤ μ) (hdoms : J.map s ≤ μ)
      (f : α → ℝ) (hf : MemLp f 2 μ) :
      MemLp (fun x => f (r x) - f (s x)) 2 J ∧
        (∫ x, (f (r x) - f (s x)) ^ 2 ∂J) ≤ 4 * ∫ a, f a ^ 2 ∂μ := by
    obtain ⟨hfr, hbr⟩ := dominated_marginal_pullback r hr hdomr f hf
    obtain ⟨hfs, hbs⟩ := dominated_marginal_pullback s hs hdoms f hf
    have hdiff : MemLp (fun x => f (r x) - f (s x)) 2 J := hfr.sub hfs
    have hir : Integrable (fun x => f (r x) ^ 2) J := hfr.integrable_sq
    have his : Integrable (fun x => f (s x) ^ 2) J := hfs.integrable_sq
    refine ⟨hdiff, ?_⟩
    calc
      (∫ x, (f (r x) - f (s x)) ^ 2 ∂J)
          ≤ ∫ x, 2 * f (r x) ^ 2 + 2 * f (s x) ^ 2 ∂J := by
            apply integral_mono hdiff.integrable_sq
              ((hir.const_mul 2).add (his.const_mul 2))
            intro x
            dsimp
            nlinarith [sq_nonneg (f (r x) + f (s x))]
      _ = 2 * (∫ x, f (r x) ^ 2 ∂J) + 2 * (∫ x, f (s x) ^ 2 ∂J) := by
            rw [integral_add (hir.const_mul 2)
              (his.const_mul 2), integral_const_mul, integral_const_mul]
      _ ≤ 4 * ∫ a, f a ^ 2 ∂μ := by linarith

  have dominated_marginal_difference_operator {α Ω : Type} [MeasurableSpace α] [MeasurableSpace Ω]
    {μ : Measure α} {J : Measure Ω} (r s : Ω → α)
      (hr : AEMeasurable r J) (hs : AEMeasurable s J)
      (hdomr : J.map r ≤ μ) (hdoms : J.map s ≤ μ) :
      ∃! D : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 J,
        ‖D‖ ≤ 2 ∧ ∀ f (hf : MemLp f 2 μ),
          D (hf.toLp f) =ᵐ[J] (fun x => f (r x) - f (s x)) := by
    let T : (α → ℝ) → Ω → ℝ := fun f x => f (r x) - f (s x)
    have hmem (f : α → ℝ) (hf : MemLp f 2 μ) : MemLp (T f) 2 J :=
      (dominated_marginal_difference r s hr hs hdomr hdoms f hf).1
    apply raw_operator_to_L2 T 2 (by norm_num) hmem
    · intro f g hf hg hfg
      exact (dominated_marginal_ae r hr hdomr hfg).sub
        (dominated_marginal_ae s hs hdoms hfg)
    · intro f g hf hg
      apply Filter.Eventually.of_forall
      intro x
      dsimp [T]
      ring
    · intro c f hf
      apply Filter.Eventually.of_forall
      intro x
      dsimp [T]
      ring
    · intro f hf
      have hb := (dominated_marginal_difference r s hr hs hdomr hdoms f hf).2
      have hsq : ‖(hmem f hf).toLp (T f)‖ ^ 2 ≤ 4 * ‖hf.toLp f‖ ^ 2 := by
        simpa only [real_L2_norm_sq_toLp, T] using hb
      nlinarith [norm_nonneg ((hmem f hf).toLp (T f)), norm_nonneg (hf.toLp f)]

  have difference_form_operator {ι H : Type} [Fintype ι] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    {K : ι → Type} [∀ i, NormedAddCommGroup (K i)]
    [∀ i, InnerProductSpace ℝ (K i)] [∀ i, CompleteSpace (K i)] (D : ∀ i, H →L[ℝ] K i)
      (hD : ∀ i, ‖D i‖ ≤ 2) :
      ∃ L : H →L[ℝ] H,
        ‖L‖ ≤ 2 * Fintype.card ι ∧
        (∀ v w, inner ℝ v (L w) = inner ℝ (L v) w) ∧
        (∀ v, -inner ℝ v (L v) = (1 / 2 : ℝ) * ∑ i, ‖D i v‖ ^ 2) ∧
        (∀ v, 0 ≤ -inner ℝ v (L v)) ∧
        (∀ v, L v = 0 ↔ ∀ i, D i v = 0) ∧
        (∀ v w, inner ℝ v (L w) = (-1 / 2 : ℝ) * ∑ i, inner ℝ (D i v) (D i w)) := by
    classical
    let L : H →L[ℝ] H := (-1 / 2 : ℝ) • ∑ i, (ContinuousLinearMap.adjoint (D i)).comp (D i)
    have hnorm : ‖L‖ ≤ 2 * Fintype.card ι := by
      calc
        ‖L‖ = (1 / 2 : ℝ) * ‖∑ i, (ContinuousLinearMap.adjoint (D i)).comp (D i)‖ := by
          simp [L, norm_smul]
        _ ≤ (1 / 2 : ℝ) * ∑ i, ‖(ContinuousLinearMap.adjoint (D i)).comp (D i)‖ := by
          gcongr
          exact norm_sum_le _ _
        _ = (1 / 2 : ℝ) * ∑ i, ‖D i‖ ^ 2 := by
          simp only [ContinuousLinearMap.norm_adjoint_comp_self, pow_two]
        _ ≤ (1 / 2 : ℝ) * ∑ _i : ι, (4 : ℝ) := by
          gcongr with i
          nlinarith [hD i, norm_nonneg (D i)]
        _ = 2 * Fintype.card ι := by simp; ring
    have hbilin (v w : H) : inner ℝ v (L w) =
        (-1 / 2 : ℝ) * ∑ i, inner ℝ (D i v) (D i w) := by
      simp [L, inner_smul_right, inner_sum, ContinuousLinearMap.adjoint_inner_right]
    have hsym (v w : H) : inner ℝ v (L w) = inner ℝ (L v) w := by
      conv_rhs => rw [real_inner_comm]
      rw [hbilin, hbilin]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact real_inner_comm _ _
    have henergy (v : H) : -inner ℝ v (L v) =
        (1 / 2 : ℝ) * ∑ i, ‖D i v‖ ^ 2 := by
      rw [hbilin]
      simp only [real_inner_self_eq_norm_sq]
      ring
    have hpos (v : H) : 0 ≤ -inner ℝ v (L v) := by
      rw [henergy]
      positivity
    have hzero (v : H) : L v = 0 ↔ ∀ i, D i v = 0 := by
      constructor
      · intro hv
        have hz : ∑ i, ‖D i v‖ ^ 2 = 0 := by
          have he := henergy v
          rw [hv, inner_zero_right] at he
          linarith
        have hi := (Finset.sum_eq_zero_iff_of_nonneg
          (fun i (_ : i ∈ (Finset.univ : Finset ι)) => sq_nonneg ‖D i v‖)).mp hz
        intro i
        exact norm_eq_zero.mp (sq_eq_zero_iff.mp (hi i (Finset.mem_univ i)))
      · intro hv
        simp [L, hv]
    exact ⟨L, hnorm, hsym, henergy, hpos, hzero, hbilin⟩

  have negative_energy_norm_bound {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (L : H →L[ℝ] H) (C : ℝ) (hL : ‖L‖ ≤ C) :
      ∀ v, -inner ℝ v (L v) ≤ C * ‖v‖ ^ 2 := by
    intro v
    calc
      -inner ℝ v (L v) ≤ |inner ℝ v (L v)| := neg_le_abs _
      _ ≤ ‖v‖ * ‖L v‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖v‖ * (C * ‖v‖) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact (L.le_opNorm v).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
      _ = C * ‖v‖ ^ 2 := by ring

  have canonical_jump_haar_equivalence  (d N : ℕ) (hN : 2 ≤ N) (l u β : ℝ)
      (q : BoundedBackground d l u) (hβ : 0 ≤ β)
      (G : UnitAddTorus (Fin d) → ℝ) (hG : Measurable G)
      (hGi : Integrable G volume) (hGn : ∀ x, 0 ≤ G x) :
      let M := (volume : Measure (Configuration d N))
      let m := (volume : Measure (UnitAddTorus (Fin d)))
      let P := CanonicalLaw (N := N) G q.density β
      P ≪ M ∧ M ≪ P ∧
        ∀ i : Fin N, M.prod m ≪ (P.prod m).withDensity
          (fun p => ENNReal.ofReal
            (Real.exp (-ConditionalPotential G β p.1 i p.2) * q.density p.2)) := by
    classical
    intro M m P
    let W := GibbsWeight (N := N) G q.density β
    let Z := ∫ X, W X ∂M
    have hgibbs := GibbsNormalizerBounds d N hN l u q G hG hGi 0 β
      (le_refl 0) hβ (Filter.Eventually.of_forall fun x => by simpa using hGn x)
    have hZ : 0 < Z := lt_of_lt_of_le (Real.exp_pos _) hgibbs.2.1
    have hAm : Measurable (PairEnergy (N := N) G) := by
      unfold PairEnergy
      refine measurable_const.mul (Finset.measurable_fun_sum _ fun i _ => ?_)
      refine Finset.measurable_fun_sum _ fun j _ => ?_
      split_ifs
      · exact hG.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))
      · exact measurable_const
    have hWm : Measurable W :=
      ((hAm.const_mul (-β)).exp).mul (ProductBackgroundFacts d N l u q).1
    have hWp : ∀ᵐ X ∂M, 0 < W X := by
      filter_upwards [(ProductBackgroundFacts d N l u q).2.2.2] with X hX
      exact mul_pos (Real.exp_pos _) ((pow_pos q.lower_pos N).trans_le hX.1)
    have hPd : P = M.withDensity (fun X => ENNReal.ofReal (W X / Z)) := rfl
    have hPM : P ≪ M := by
      rw [hPd]
      exact withDensity_absolutelyContinuous _ _
    have hMP : M ≪ P := by
      rw [hPd]
      apply withDensity_absolutelyContinuous' (hWm.div_const Z).ennreal_ofReal.aemeasurable
      filter_upwards [hWp] with X hX
      exact (ENNReal.ofReal_pos.mpr (div_pos hX hZ)).ne'
    refine ⟨hPM, hMP, ?_⟩
    intro i
    have hUm : Measurable (fun p : Configuration d N × UnitAddTorus (Fin d) =>
        ConditionalPotential G β p.1 i p.2) := by
      unfold ConditionalPotential
      refine measurable_const.mul (Finset.measurable_fun_sum _ fun j _ => ?_)
      split_ifs
      · exact measurable_const
      · exact hG.comp (measurable_snd.sub ((measurable_pi_apply j).comp measurable_fst))
    have hwm := (hUm.neg.exp).mul (q.measurable.comp measurable_snd)
    have hqp : ∀ᵐ p : Configuration d N × UnitAddTorus (Fin d) ∂P.prod m,
        0 < q.density p.2 := by
      apply (Measure.ae_prod_iff_ae_ae
        (measurableSet_lt measurable_const (q.measurable.comp measurable_snd))).mpr
      exact Filter.Eventually.of_forall fun _ =>
        q.bounds.mono fun z hz => q.lower_pos.trans_le hz.1
    have hJ : P.prod m ≪ (P.prod m).withDensity
        (fun p => ENNReal.ofReal
          (Real.exp (-ConditionalPotential G β p.1 i p.2) * q.density p.2)) := by
      apply withDensity_absolutelyContinuous' hwm.ennreal_ofReal.aemeasurable
      filter_upwards [hqp] with p hp
      exact (ENNReal.ofReal_pos.mpr (mul_pos (Real.exp_pos _) hp)).ne'
    exact (hMP.prod Measure.AbsolutelyContinuous.rfl).trans hJ

  have weighted_integrable_fubini {Ω B : Type} [MeasurableSpace Ω] [MeasurableSpace B]
    {μ : Measure Ω} {ν : Measure B} [SFinite μ] [SFinite ν] (w : Ω × B → ℝ) (hw : Measurable w)
      (hwn : ∀ᵐ p ∂μ.prod ν, 0 ≤ w p) (h : Ω × B → ℝ)
      (hh : Integrable h ((μ.prod ν).withDensity (fun p => ENNReal.ofReal (w p)))) :
      Integrable (fun p => w p * h p) (μ.prod ν) ∧
        (∫ p, h p ∂((μ.prod ν).withDensity (fun p => ENNReal.ofReal (w p)))) =
          ∫ X, (∫ z, w (X, z) * h (X, z) ∂ν) ∂μ ∧
        (∀ᵐ X ∂μ, Integrable (fun z => w (X, z) * h (X, z)) ν) := by
    have hfin : ∀ᵐ p ∂μ.prod ν, ENNReal.ofReal (w p) < ⊤ :=
      Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
    have hreal : (fun p => (ENNReal.ofReal (w p)).toReal • h p) =ᵐ[μ.prod ν]
        (fun p => w p * h p) := by
      filter_upwards [hwn] with p hp
      simp only [ENNReal.toReal_ofReal hp, smul_eq_mul]
    have hint : Integrable (fun p => w p * h p) (μ.prod ν) :=
      ((integrable_withDensity_iff_integrable_smul' hw.ennreal_ofReal hfin).mp hh).congr hreal
    refine ⟨hint, ?_, hint.prod_right_ae⟩
    calc
      _ = ∫ p, (ENNReal.ofReal (w p)).toReal • h p ∂μ.prod ν :=
        integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal hfin _
      _ = ∫ p, w p * h p ∂μ.prod ν := integral_congr_ae hreal
      _ = ∫ X, (∫ z, w (X, z) * h (X, z) ∂ν) ∂μ := integral_prod _ hint

  have weighted_square_fubini {Ω B : Type} [MeasurableSpace Ω] [MeasurableSpace B]
    {μ : Measure Ω} {ν : Measure B} [SFinite μ] [SFinite ν] (w : Ω × B → ℝ) (hw : Measurable w)
      (hwn : ∀ᵐ p ∂μ.prod ν, 0 ≤ w p) (h : Ω × B → ℝ)
      (hh : MemLp h 2 ((μ.prod ν).withDensity (fun p => ENNReal.ofReal (w p)))) :
      Integrable (fun p => w p * h p ^ 2) (μ.prod ν) ∧
        (∫ p, h p ^ 2 ∂((μ.prod ν).withDensity (fun p => ENNReal.ofReal (w p)))) =
          ∫ X, (∫ z, w (X, z) * h (X, z) ^ 2 ∂ν) ∂μ ∧
        (∀ᵐ X ∂μ, Integrable (fun z => w (X, z) * h (X, z) ^ 2) ν) := by
    have hfin : ∀ᵐ p ∂μ.prod ν, ENNReal.ofReal (w p) < ⊤ :=
      Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
    have hreal : (fun p => (ENNReal.ofReal (w p)).toReal • h p ^ 2) =ᵐ[μ.prod ν]
        (fun p => w p * h p ^ 2) := by
      filter_upwards [hwn] with p hp
      simp only [ENNReal.toReal_ofReal hp, smul_eq_mul]
    have hint : Integrable (fun p => w p * h p ^ 2) (μ.prod ν) :=
      ((integrable_withDensity_iff_integrable_smul' hw.ennreal_ofReal hfin).mp
        hh.integrable_sq).congr hreal
    refine ⟨hint, ?_, hint.prod_right_ae⟩
    calc
      _ = ∫ p, (ENNReal.ofReal (w p)).toReal • h p ^ 2 ∂μ.prod ν :=
        integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal hfin _
      _ = ∫ p, w p * h p ^ 2 ∂μ.prod ν := integral_congr_ae hreal
      _ = ∫ X, (∫ z, w (X, z) * h (X, z) ^ 2 ∂ν) ∂μ := integral_prod _ hint

  have symmetric_edge_bilinear_identity {α Ω : Type} [MeasurableSpace α] [MeasurableSpace Ω]
    {P : Measure α} {J : Measure Ω}
      (r s : Ω → α) (hr : AEMeasurable r J) (hs : AEMeasurable s J)
      (hdomr : J.map r ≤ P) (hdoms : J.map s ≤ P)
      (S : Ω → Ω) (hS : MeasurePreserving S J J)
      (hSr : ∀ p, r (S p) = s p) (hSs : ∀ p, s (S p) = r p)
      (f g : α → ℝ) (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
      (-1 / 2 : ℝ) * (∫ p, (g (r p) - g (s p)) *
        (f (r p) - f (s p)) ∂J) = ∫ p, g (s p) * (f (r p) - f (s p)) ∂J := by
    have hdiff := (dominated_marginal_difference r s hr hs hdomr hdoms f hf).1
    have hgr := (dominated_marginal_pullback r hr hdomr g hg).1
    have hgs := (dominated_marginal_pullback s hs hdoms g hg).1
    have hir : Integrable (fun p => g (r p) * (f (r p) - f (s p))) J :=
      hgr.integrable_mul hdiff
    have his : Integrable (fun p => g (s p) * (f (r p) - f (s p))) J :=
      hgs.integrable_mul hdiff
    have he : (∫ p, g (r p) * (f (r p) - f (s p)) ∂J) =
        -(∫ p, g (s p) * (f (r p) - f (s p)) ∂J) := by
      calc
        _ = ∫ p, g (r (S p)) * (f (r (S p)) - f (s (S p))) ∂J := by
          have hi := integral_map hS.aemeasurable
            (hS.map_eq.symm ▸ hir.aestronglyMeasurable)
          simpa only [hS.map_eq] using hi
        _ = ∫ p, -(g (s p) * (f (r p) - f (s p))) ∂J := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun p => by dsimp; rw [hSs, hSr]; ring
        _ = _ := integral_neg _
    have hexpand : (∫ p, (g (r p) - g (s p)) * (f (r p) - f (s p)) ∂J) =
        (∫ p, g (r p) * (f (r p) - f (s p)) ∂J) -
        (∫ p, g (s p) * (f (r p) - f (s p)) ∂J) := by
      calc
        _ = ∫ p, g (r p) * (f (r p) - f (s p)) -
            g (s p) * (f (r p) - f (s p)) ∂J := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun _ => by ring
        _ = _ := integral_sub hir his
    rw [hexpand, he]
    ring

  have identify_integrable_formula {α : Type} [MeasurableSpace α] {P : Measure α} [IsFiniteMeasure P] (v : Lp ℝ 2 P) (F : α → ℝ)
      (hF : Integrable F P)
      (hpair : ∀ g (hg : MemLp g 2 P),
        inner ℝ (hg.toLp g) v = ∫ x, g x * F x ∂P) :
      MemLp F 2 P ∧ v =ᵐ[P] F := by
    have hv : Integrable (⇑v) P := (Lp.memLp v).integrable (by norm_num)
    have heq : v =ᵐ[P] F := by
      apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ hv hF
      intro s hs hsf
      let g : α → ℝ := s.indicator (fun _ => 1)
      have hg : MemLp g 2 P := (memLp_const (1 : ℝ)).indicator hs
      have hh := hpair g hg
      have hi := real_L2_inner_toLp g v hg (Lp.memLp v)
      simp only [Lp.toLp_coeFn] at hi
      rw [hi] at hh
      have hleft : (∫ x, g x * v x ∂P) = ∫ x in s, v x ∂P := by
        rw [← integral_indicator hs]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          by_cases hx : x ∈ s <;> simp [g, hx]
      have hright : (∫ x, g x * F x ∂P) = ∫ x in s, F x ∂P := by
        rw [← integral_indicator hs]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          by_cases hx : x ∈ s <;> simp [g, hx]
      rwa [hleft, hright] at hh
    exact ⟨(Lp.memLp v).ae_eq heq, heq⟩

  have weighted_edge_row_pairing {α B : Type} [MeasurableSpace α] [MeasurableSpace B]
    {P : Measure α} [IsFiniteMeasure P] {m : Measure B} [SFinite m]
      (w : α × B → ℝ) (hw : Measurable w) (hwn : ∀ᵐ p ∂P.prod m, 0 ≤ w p)
      (r : α × B → α) (hr : Measurable r) (S : α × B → α × B)
      (hSr : ∀ p, r (S p) = p.1) (hSs : ∀ p, (S p).1 = r p)
      (f : α → ℝ) (hf : MemLp f 2 P) :
      let J := (P.prod m).withDensity (fun p => ENNReal.ofReal (w p))
      MeasurePreserving S J J → J.map r ≤ P → J.map Prod.fst ≤ P →
      let H := fun X => ∫ z, w (X, z) * (f (r (X, z)) - f X) ∂m
      Integrable H P ∧ ∀ g (hg : MemLp g 2 P),
        Integrable (fun X => g X * H X) P ∧
        (-1 / 2 : ℝ) * (∫ p, (g (r p) - g p.1) * (f (r p) - f p.1) ∂J) =
          ∫ X, g X * H X ∂P := by
    intro J hS hdomr hdoms H
    haveI : IsFiniteMeasure (J.map Prod.fst) := isFiniteMeasure_of_le P hdoms
    haveI : IsFiniteMeasure J := Measure.isFiniteMeasure_of_map measurable_fst.aemeasurable
    have hdiff := (dominated_marginal_difference r Prod.fst hr.aemeasurable
      measurable_fst.aemeasurable hdomr hdoms f hf).1
    have hfirst := weighted_integrable_fubini w hw hwn
      (fun p => f (r p) - f p.1) (hdiff.integrable (by norm_num))
    refine ⟨hfirst.1.integral_prod_left, ?_⟩
    intro g hg
    have hgs := (dominated_marginal_pullback Prod.fst measurable_fst.aemeasurable hdoms g hg).1
    have hgf : Integrable (fun p => g p.1 * (f (r p) - f p.1)) J := hgs.integrable_mul hdiff
    have hweighted := weighted_integrable_fubini w hw hwn _ hgf
    have hrow : (fun X => ∫ z, w (X, z) * (g X * (f (r (X, z)) - f X)) ∂m) =
        (fun X => g X * H X) := by
      funext X
      change (∫ z, w (X, z) * (g X * (f (r (X, z)) - f X)) ∂m) =
        g X * ∫ z, w (X, z) * (f (r (X, z)) - f X) ∂m
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun _ => by ring
    refine ⟨hrow ▸ hweighted.1.integral_prod_left, ?_⟩
    calc
      _ = ∫ p, g p.1 * (f (r p) - f p.1) ∂J :=
        symmetric_edge_bilinear_identity r Prod.fst hr.aemeasurable
          measurable_fst.aemeasurable hdomr hdoms S hS hSr hSs f g hf hg
      _ = ∫ X, (∫ z, w (X, z) * (g X * (f (r (X, z)) - f X)) ∂m) ∂P :=
        hweighted.2.1
      _ = ∫ X, g X * H X ∂P := by rw [hrow]

  have jump_L2_form_construction  (d N : ℕ) (hN : 2 ≤ N) (l u β : ℝ)
      (q : BoundedBackground d l u) (hβ : 0 ≤ β)
      (G : UnitAddTorus (Fin d) → ℝ) (hG : Measurable G)
      (hGi : Integrable G volume) (hGn : ∀ x, 0 ≤ G x)
      (hGe : ∀ x, G (-x) = G x) :
      let P := CanonicalLaw (N := N) G q.density β
      let J := fun i : Fin N => (P.prod volume).withDensity
        (fun v : Configuration d N × UnitAddTorus (Fin d) => ENNReal.ofReal
          (Real.exp (-ConditionalPotential G β v.1 i v.2) * q.density v.2))
      ∃ L : Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P,
        ‖L‖ ≤ 2 * (N : ℝ) ∧
        (∀ v w, inner ℝ v (L w) = inner ℝ (L v) w) ∧
        (∀ f (hf : MemLp f 2 P),
          -inner ℝ (hf.toLp f) (L (hf.toLp f)) = (1 / 2 : ℝ) *
            ∑ i : Fin N, ∫ v, (f (Replacement v.1 i v.2) - f v.1) ^ 2 ∂J i) ∧
        (∀ v, 0 ≤ -inner ℝ v (L v)) ∧
        (∀ v, L v = 0 ↔ ∀ i : Fin N, ∀ᵐ p ∂J i,
          v (Replacement p.1 i p.2) = v p.1) ∧
        (∀ f g (hf : MemLp f 2 P) (hg : MemLp g 2 P),
          inner ℝ (hf.toLp f) (L (hg.toLp g)) = (-1 / 2 : ℝ) *
            ∑ i : Fin N, ∫ p, (f (Replacement p.1 i p.2) - f p.1) *
              (g (Replacement p.1 i p.2) - g p.1) ∂J i) := by
    classical
    intro P J
    let r := fun (i : Fin N) (p : Configuration d N × UnitAddTorus (Fin d)) =>
      Replacement p.1 i p.2
    have hr (i : Fin N) : Measurable (r i) := by
      apply measurable_pi_lambda
      intro j
      by_cases hji : j = i
      · subst j
        simpa [r, Replacement] using
          (measurable_snd : Measurable (Prod.snd : Configuration d N ×
            UnitAddTorus (Fin d) → UnitAddTorus (Fin d)))
      · have hh : Measurable (fun p : Configuration d N × UnitAddTorus (Fin d) => p.1 j) :=
          (measurable_pi_apply j).comp measurable_fst
        simpa only [r, Replacement, Function.update_of_ne hji] using hh
    have hd (i : Fin N) : ∃! D : Lp ℝ 2 P →L[ℝ] Lp ℝ 2 (J i),
        ‖D‖ ≤ 2 ∧ ∀ f (hf : MemLp f 2 P),
          D (hf.toLp f) =ᵐ[J i] (fun p => f (r i p) - f p.1) := by
      have hb := ReplacementJointBalance d N hN l u β q hβ G hG hGi hGn hGe i
      exact dominated_marginal_difference_operator (r i) Prod.fst
        (hr i).aemeasurable measurable_fst.aemeasurable hb.2.2 hb.2.1
    let D := fun i => Classical.choose (hd i).exists
    have hD := fun i => Classical.choose_spec (hd i).exists
    obtain ⟨L, hLn, hLs, hLe, hLp, hLz, hLb⟩ :=
      difference_form_operator D (fun i => (hD i).1)
    refine ⟨L, by simpa using hLn, hLs, ?_, hLp, ?_, ?_⟩
    · intro f hf
      rw [hLe]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      have hn := real_L2_norm_sq_toLp (⇑(D i (hf.toLp f)))
        (Lp.memLp (D i (hf.toLp f)))
      simp only [Lp.toLp_coeFn] at hn
      rw [hn]
      apply integral_congr_ae
      filter_upwards [(hD i).2 f hf] with p hp
      exact congrArg (fun t : ℝ => t ^ 2) hp
    · intro v
      rw [hLz]
      constructor
      · intro hz i
        have he := (hD i).2 v (Lp.memLp v)
        change D i ((Lp.memLp v).toLp v) =ᵐ[J i]
          (fun p => v (r i p) - v p.1) at he
        simp only [Lp.toLp_coeFn, hz i] at he
        filter_upwards [he, Lp.coeFn_zero ℝ 2 (J i)] with p hp hzero
        dsimp only [r] at hp
        rw [hzero] at hp
        exact sub_eq_zero.mp hp.symm
      · intro hz i
        apply Lp.ext
        have he := (hD i).2 v (Lp.memLp v)
        change D i ((Lp.memLp v).toLp v) =ᵐ[J i]
          (fun p => v (r i p) - v p.1) at he
        simp only [Lp.toLp_coeFn] at he
        filter_upwards [he, hz i, Lp.coeFn_zero ℝ 2 (J i)] with p hp hv hzero
        change D i v p = v (Replacement p.1 i p.2) - v p.1 at hp
        simpa only [hv, sub_self, hzero, Pi.zero_apply] using hp

    · intro f g hf hg
      rw [hLb]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      have hn := real_L2_inner_toLp (⇑(D i (hf.toLp f))) (⇑(D i (hg.toLp g)))
        (Lp.memLp (D i (hf.toLp f))) (Lp.memLp (D i (hg.toLp g)))
      simp only [Lp.toLp_coeFn] at hn
      rw [hn]
      apply integral_congr_ae
      filter_upwards [(hD i).2 f hf, (hD i).2 g hg] with p hpf hpg
      exact congrArg₂ (fun a b : ℝ => a * b) hpf hpg

  have jump_L2_raw_representation  (d N : ℕ) (hN : 2 ≤ N) (l u β : ℝ)
      (q : BoundedBackground d l u) (hβ : 0 ≤ β)
      (G : UnitAddTorus (Fin d) → ℝ) (hG : Measurable G)
      (hGi : Integrable G volume) (hGn : ∀ x, 0 ≤ G x)
      (hGe : ∀ x, G (-x) = G x) :
      let P := CanonicalLaw (N := N) G q.density β
      let J := fun i : Fin N => (P.prod volume).withDensity
        (fun v : Configuration d N × UnitAddTorus (Fin d) => ENNReal.ofReal
          (Real.exp (-ConditionalPotential G β v.1 i v.2) * q.density v.2))
      ∀ L : Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P,
        (∀ f g (hf : MemLp f 2 P) (hg : MemLp g 2 P),
          inner ℝ (hf.toLp f) (L (hg.toLp g)) = (-1 / 2 : ℝ) *
            ∑ i : Fin N, ∫ p, (f (Replacement p.1 i p.2) - f p.1) *
              (g (Replacement p.1 i p.2) - g p.1) ∂J i) →
        ∀ f (hf : MemLp f 2 P),
          MemLp (JumpOperator G q.density β f) 2 P ∧
          L (hf.toLp f) =ᵐ[P] JumpOperator G q.density β f := by
    classical
    intro P J L hbilin f hf
    haveI : IsProbabilityMeasure P := (GibbsNormalizerBounds d N hN l u q G hG hGi 0 β
      (le_refl 0) hβ (Filter.Eventually.of_forall fun x => by simpa using hGn x)).2.2.2
    let w := fun (i : Fin N) (p : Configuration d N × UnitAddTorus (Fin d)) =>
      Real.exp (-ConditionalPotential G β p.1 i p.2) * q.density p.2
    let r := fun (i : Fin N) (p : Configuration d N × UnitAddTorus (Fin d)) =>
      Replacement p.1 i p.2
    let S := fun (i : Fin N) (p : Configuration d N × UnitAddTorus (Fin d)) =>
      (r i p, p.1 i)
    let H := fun (i : Fin N) X => ∫ z, w i (X, z) * (f (r i (X, z)) - f X)
    have hrow (i : Fin N) : Integrable (H i) P ∧
        ∀ g (hg : MemLp g 2 P), Integrable (fun X => g X * H i X) P ∧
          (-1 / 2 : ℝ) * (∫ p, (g (r i p) - g p.1) * (f (r i p) - f p.1) ∂J i) =
            ∫ X, g X * H i X ∂P := by
      have hb := ReplacementJointBalance d N hN l u β q hβ G hG hGi hGn hGe i
      have hr : Measurable (r i) := measurable_fst.comp hb.1.measurable
      have hUm : Measurable (fun p : Configuration d N × UnitAddTorus (Fin d) =>
          ConditionalPotential G β p.1 i p.2) := by
        unfold ConditionalPotential
        refine measurable_const.mul (Finset.measurable_fun_sum _ fun j _ => ?_)
        split_ifs
        · exact measurable_const
        · exact hG.comp (measurable_snd.sub ((measurable_pi_apply j).comp measurable_fst))
      have hwm : Measurable (w i) := (hUm.neg.exp).mul (q.measurable.comp measurable_snd)
      have hwn : ∀ᵐ p ∂P.prod (volume : Measure (UnitAddTorus (Fin d))), 0 ≤ w i p := by
        have hq := (measurePreserving_snd (μ := P) (ν := (volume :
          Measure (UnitAddTorus (Fin d))))).quasiMeasurePreserving.ae q.bounds
        filter_upwards [hq] with p hp
        exact mul_nonneg (Real.exp_pos _).le (q.lower_pos.le.trans hp.1)
      have hSr (p : Configuration d N × UnitAddTorus (Fin d)) : r i (S i p) = p.1 := by
        funext j
        by_cases hji : j = i
        · subst j
          simp [r, S, Replacement]
        · simp [r, S, Replacement, hji]
      have hSs (p : Configuration d N × UnitAddTorus (Fin d)) : (S i p).1 = r i p := rfl
      exact weighted_edge_row_pairing (w i) hwm hwn (r i) hr (S i) hSr hSs f hf
        hb.1 hb.2.2 hb.2.1
    have hraw : JumpOperator G q.density β f = fun X => ∑ i : Fin N, H i X := by
      funext X
      unfold JumpOperator
      apply Finset.sum_congr rfl
      intro i hi
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun _ => by dsimp [H, w, r]; ring
    have hint : Integrable (JumpOperator G q.density β f) P := by
      rw [hraw]
      exact integrable_finsetSum Finset.univ (fun i _ => (hrow i).1)
    apply identify_integrable_formula _ _ hint
    intro g hg
    rw [hbilin]
    calc
      _ = ∑ i : Fin N, ((-1 / 2 : ℝ) *
          ∫ p, (g (r i p) - g p.1) * (f (r i p) - f p.1) ∂J i) := by
        rw [Finset.mul_sum]
      _ = ∑ i : Fin N, ∫ X, g X * H i X ∂P := by
        apply Finset.sum_congr rfl
        intro i hi
        exact ((hrow i).2 g hg).2
      _ = ∫ X, ∑ i : Fin N, g X * H i X ∂P :=
        (integral_finsetSum Finset.univ (fun i _ => ((hrow i).2 g hg).1)).symm
      _ = ∫ X, g X * JumpOperator G q.density β f X ∂P := by
        rw [hraw]
        simp only [Finset.mul_sum]
  classical
  intro P
  let J := fun i : Fin N => (P.prod volume).withDensity
    (fun v : Configuration d N × UnitAddTorus (Fin d) => ENNReal.ofReal
      (Real.exp (-ConditionalPotential G β v.1 i v.2) * q.density v.2))
  obtain ⟨L, hn, hs, he, hp, hz, hb⟩ :=
    jump_L2_form_construction d N hN l u β q hβ G hG hGi hGn hGe
  have hac := canonical_jump_haar_equivalence d N hN l u β q hβ G hG hGi hGn
  have hraw := jump_L2_raw_representation d N hN l u β q hβ G hG hGi hGn hGe L hb
  haveI : IsProbabilityMeasure P := (GibbsNormalizerBounds d N hN l u q G hG hGi 0 β
    (le_refl 0) hβ (Filter.Eventually.of_forall fun x => by simpa using hGn x)).2.2.2
  have hjoint (i : Fin N) := ReplacementJointBalance d N hN l u β q hβ G hG hGi hGn hGe i
  have hdiff (f : Configuration d N → ℝ) (hf : MemLp f 2 P) (i : Fin N) :
      MemLp (fun p => f (Replacement p.1 i p.2) - f p.1) 2 (J i) :=
    (dominated_marginal_difference _ Prod.fst
      (measurable_fst.comp (hjoint i).1.measurable).aemeasurable
      measurable_fst.aemeasurable (hjoint i).2.2 (hjoint i).2.1 f hf).1
  have hconst (v : Lp ℝ 2 P) : L v = 0 ↔ ∃ c : ℝ, ∀ᵐ X ∂P, v X = c := by
    rw [hz]
    constructor
    · intro hi
      obtain ⟨c, hc⟩ := ReplacementHaarInvariant d N v (fun i => (hac.2.2 i).ae_le (hi i))
      exact ⟨c, hac.1.ae_eq hc⟩
    · rintro ⟨c, hc⟩ i
      have hr : AEMeasurable (fun p : Configuration d N × UnitAddTorus (Fin d) =>
          Replacement p.1 i p.2) (J i) :=
        (measurable_fst.comp (hjoint i).1.measurable).aemeasurable
      have h1 := dominated_marginal_ae _ hr (hjoint i).2.2 hc
      have h0 := dominated_marginal_ae Prod.fst measurable_fst.aemeasurable (hjoint i).2.1 hc
      filter_upwards [h1, h0] with p h1p h0p
      exact h1p.trans h0p.symm
  have hclaims (f : Configuration d N → ℝ) (hf : MemLp f 2 P) :
      MemLp (JumpOperator G q.density β f) 2 P ∧
      L (hf.toLp f) =ᵐ[P] JumpOperator G q.density β f ∧
      let E := -inner ℝ (hf.toLp f) (L (hf.toLp f))
      E = (1 / 2 : ℝ) * ∑ i : Fin N,
        ∫ X, (∫ z, Real.exp (-ConditionalPotential G β X i z) *
          (f (Replacement X i z) - f X)^2 * q.density z) ∂P ∧
      0 ≤ E ∧ E ≤ 2 * (N : ℝ) * ‖hf.toLp f‖^2 ∧
      (E = 0 ↔ ∃ c : ℝ, ∀ᵐ X ∂P, f X = c) := by
    refine ⟨(hraw f hf).1, (hraw f hf).2, ?_, hp _,
      negative_energy_norm_bound L _ hn _, ?_⟩
    · rw [he]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      let w := fun p : Configuration d N × UnitAddTorus (Fin d) =>
        Real.exp (-ConditionalPotential G β p.1 i p.2) * q.density p.2
      have hUm : Measurable (fun p : Configuration d N × UnitAddTorus (Fin d) =>
          ConditionalPotential G β p.1 i p.2) := by
        unfold ConditionalPotential
        refine measurable_const.mul (Finset.measurable_fun_sum _ fun j _ => ?_)
        split_ifs
        · exact measurable_const
        · exact hG.comp (measurable_snd.sub ((measurable_pi_apply j).comp measurable_fst))
      have hwm : Measurable w := (hUm.neg.exp).mul (q.measurable.comp measurable_snd)
      have hwn : ∀ᵐ p ∂P.prod (volume : Measure (UnitAddTorus (Fin d))), 0 ≤ w p := by
        have hq := (measurePreserving_snd (μ := P) (ν := (volume :
          Measure (UnitAddTorus (Fin d))))).quasiMeasurePreserving.ae q.bounds
        filter_upwards [hq] with p hq
        exact mul_nonneg (Real.exp_pos _).le (q.lower_pos.le.trans hq.1)
      rw [(weighted_square_fubini w hwm hwn _ (hdiff f hf i)).2.1]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro X
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun _ => by dsimp [w]; ring
    · constructor
      · intro hE
        have hsum : ∑ i : Fin N, ∫ p, (f (Replacement p.1 i p.2) - f p.1)^2 ∂J i = 0 := by
          have h := he f hf
          rw [hE] at h
          linarith
        have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) =>
          integral_nonneg (fun _ => sq_nonneg _))).mp hsum
        have hInv : ∀ i : Fin N, ∀ᵐ p ∂J i, f (Replacement p.1 i p.2) = f p.1 := by
          intro i
          have hsq := (integral_eq_zero_iff_of_nonneg
            (fun _ => sq_nonneg _) (hdiff f hf i).integrable_sq).mp (hi i (Finset.mem_univ i))
          filter_upwards [hsq] with p hzero
          exact sub_eq_zero.mp (sq_eq_zero_iff.mp hzero)
        obtain ⟨c, hc⟩ := ReplacementHaarInvariant d N f (fun i => (hac.2.2 i).ae_le (hInv i))
        exact ⟨c, hac.1.ae_eq hc⟩
      · rintro ⟨c, hc⟩
        have hzv := (hconst (hf.toLp f)).mpr ⟨c, hf.coeFn_toLp.trans hc⟩
        simp only [hzv, inner_zero_right, neg_zero]
  refine ⟨L, ⟨hn, hs, hconst, hclaims⟩, ?_⟩
  intro M hM
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  have h1 := (hM.2.2.2 v (Lp.memLp v)).2.1
  have h2 := (hraw v (Lp.memLp v)).2
  simpa only [Lp.toLp_coeFn] using h1.trans h2.symm
