import Tablet.ReferenceOffsetDensity
import Tablet.MayerUniformRemainder
import Tablet.SoftRieszReferencePositive
import Tablet.ReferenceKernelSchur
import Mathlib.Tactic
open MeasureTheory Filter Set
open scoped InnerProduct
set_option autoImplicit false
set_option maxHeartbeats 1500000

-- [TABLET NODE: NativeReferenceMayerOperator]
theorem NativeReferenceMayerOperator (d : ℕ) (hd : 1 ≤ d) (s κ L M1 : ℝ)
    (hs : 0 < s) (hsd : s < (d : ℝ)) (hκ : 0 < κ) (hL : 1 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → ∃ a₀ : ℝ, 0 < a₀ ∧
      ∀ (V b : OneParticle d → ℝ), Continuous V →
        BoundedMultiplier d L b →
        (∀ x, κ / 2 * ‖x‖ ^ 2 ≤ V x - V 0) →
        (∀ x, ‖x‖ ≤ 1 → V x - V 0 ≤ M1) →
      ∀ ε : ℝ, 0 < ε → ∀ a : ℝ, 0 ≤ a → a ≤ a₀ →
      ∃! T : Lp ℝ 2 (ReferenceLaw V b) →L[ℝ] Lp ℝ 2 (ReferenceLaw V b),
        ‖T‖ ≤ a * C ∧
        (∀ v w, inner ℝ v (T w) = inner ℝ (T v) w) ∧
        (∀ v, -(a * δ) * ‖v‖ ^ 2 ≤ inner ℝ v (T v)) ∧
        (∀ (f : OneParticle d → ℝ) (hf : MemLp f 2 (ReferenceLaw V b)),
          T (hf.toLp f) =ᵐ[ReferenceLaw V b]
            fun x => ∫ y, (1 - Real.exp (-a * RieszKernel s ε (x - y))) * f y
              ∂ReferenceLaw V b) := by
-- BODY
  have actual_mayer (d : ℕ) (V b : OneParticle d → ℝ)
      [IsProbabilityMeasure (ReferenceLaw V b)] (s ε a M R : ℝ)
      (hs : 0 < s) (hε : 0 < ε) (ha : 0 ≤ a) (hM : 0 ≤ M) (hR : 0 ≤ R)
      (hrow : ∀ x : OneParticle d,
        (∫ y, RieszKernel s ε (x-y) ∂ReferenceLaw V b) ≤ M)
      (hRrow : ∀ x : OneParticle d,
        (∫ y, a*RieszKernel s ε (x-y)-1+
          Real.exp (-a*RieszKernel s ε (x-y)) ∂ReferenceLaw V b) ≤ R) :
      ∃! T : Lp ℝ 2 (ReferenceLaw V b) →L[ℝ] Lp ℝ 2 (ReferenceLaw V b),
        ‖T‖ ≤ a*M ∧
        (∀ v w, inner ℝ v (T w) = inner ℝ (T v) w) ∧
        (∀ v, -R*‖v‖^2 ≤ inner ℝ v (T v)) ∧
        (∀ (f : OneParticle d → ℝ) (hf : MemLp f 2 (ReferenceLaw V b)),
          T (hf.toLp f) =ᵐ[ReferenceLaw V b]
            fun x => ∫ y, (1-Real.exp (-a*RieszKernel s ε (x-y)))*f y ∂ReferenceLaw V b) := by
    let remainder (a z : ℝ) : ℝ := a*z-1+Real.exp (-a*z)
    have remainder_bounds (a z : ℝ) (ha : 0 ≤ a) (hz : 0 ≤ z) :
        0 ≤ remainder a z ∧ remainder a z ≤ a*z := by
      have hl := Real.add_one_le_exp (-a*z)
      have hu : Real.exp (-a*z) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      dsimp [remainder]
      constructor <;> linarith
    have kernel_operator_quadratic {Ω : Type} [MeasurableSpace Ω]
         (μ : Measure Ω) [IsProbabilityMeasure μ] (K : Ω → Ω → ℝ)
         (hKm : Measurable (fun p : Ω × Ω => K p.1 p.2)) (C : ℝ)
         (hKb : ∀ x y, ‖K x y‖ ≤ C) (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
         (hrep : ∀ f (hf : MemLp f 2 μ), T (hf.toLp f) =ᵐ[μ] fun x => ∫ y, K x y*f y ∂μ)
         (v : Lp ℝ 2 μ) : inner ℝ v (T v)=∫ p : Ω × Ω, v p.1*v p.2*K p.1 p.2 ∂μ.prod μ := by
       have hi := (Lp.memLp v).integrable (by norm_num)
       have hprod : Integrable (fun p : Ω × Ω => K p.1 p.2*(v p.1*v p.2)) (μ.prod μ) :=
         (hi.mul_prod hi).bdd_mul hKm.aestronglyMeasurable (Eventually.of_forall fun p => hKb p.1 p.2)
       have hr : T v =ᵐ[μ] fun x => ∫ y, K x y*v y ∂μ := by simpa only [Lp.toLp_coeFn] using hrep v (Lp.memLp v)
       calc
         _ = ∫ x, ∫ y, K x y*(v x*v y) ∂μ ∂μ := by
           rw [L2.inner_def]
           apply integral_congr_ae
           filter_upwards [hr] with x hx
           rw [hx]
           simp only [RCLike.inner_apply,conj_trivial]
           rw [← integral_mul_const]
           apply integral_congr_ae
           exact Eventually.of_forall fun y => by ring
         _ = ∫ p : Ω × Ω, K p.1 p.2*(v p.1*v p.2) ∂μ.prod μ := (integral_prod _ hprod).symm
         _ = _ := integral_congr_ae (Eventually.of_forall fun p => by ring)
    have positive_type_mayer_operator {Ω : Type} [MeasurableSpace Ω]
         (μ : Measure Ω) [IsProbabilityMeasure μ] (G : Ω → Ω → ℝ)
         (hGm : Measurable (fun p : Ω × Ω => G p.1 p.2)) (hGs : ∀ x y, G x y=G y x)
         (C M a r : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M) (ha : 0 ≤ a) (hr : 0 ≤ r)
         (hGb : ∀ x y, 0 ≤ G x y ∧ G x y ≤ C)
         (hrow : ∀ x, (∫ y, G x y ∂μ) ≤ M)
         (hRrow : ∀ x, (∫ y, remainder a (G x y) ∂μ) ≤ r)
         (hPSD : ∀ f, MemLp f 2 μ → 0 ≤ ∫ p : Ω × Ω, f p.1*f p.2*G p.1 p.2 ∂μ.prod μ) :
         ∃! T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ,
           ‖T‖ ≤ a*M ∧ (∀ v w, inner ℝ v (T w)=inner ℝ (T v) w) ∧
           (∀ v, -r*‖v‖^2 ≤ inner ℝ v (T v)) ∧
           (∀ f (hf : MemLp f 2 μ), T (hf.toLp f) =ᵐ[μ]
             fun x => ∫ y, (1-Real.exp (-a*G x y))*f y ∂μ) := by
       let K := fun x y => 1-Real.exp (-a*G x y)
       let R := fun x y => remainder a (G x y)
       have hKm : Measurable (fun p : Ω × Ω => K p.1 p.2) := measurable_const.sub ((hGm.const_mul (-a)).exp)
       have hRm : Measurable (fun p : Ω × Ω => R p.1 p.2) := by
         exact ((hGm.const_mul a).sub measurable_const).add (hGm.const_mul (-a)).exp
       have hKb (x y : Ω) : 0 ≤ K x y ∧ K x y ≤ 1 := by
         have he : Real.exp (-a*G x y) ≤ 1 := Real.exp_le_one_iff.mpr (by simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg ha (hGb x y).1))
         have hp := Real.exp_nonneg (-a*G x y)
         dsimp only [K]
         constructor <;> linarith
       have hRb (x y : Ω) : 0 ≤ R x y ∧ R x y ≤ a*C :=
         ⟨(remainder_bounds a _ ha (hGb x y).1).1,(remainder_bounds a _ ha (hGb x y).1).2.trans
           (mul_le_mul_of_nonneg_left (hGb x y).2 ha)⟩
       have hGnorm (x y : Ω) : ‖G x y‖ ≤ C := by simpa only [Real.norm_eq_abs,abs_of_nonneg (hGb x y).1] using (hGb x y).2
       have hRnorm (x y : Ω) : ‖R x y‖ ≤ a*C := by simpa only [Real.norm_eq_abs,abs_of_nonneg (hRb x y).1] using (hRb x y).2
       have hKs (x y : Ω) : K x y=K y x := by dsimp only [K]; rw [hGs]
       have hRs (x y : Ω) : R x y=R y x := by dsimp only [R]; rw [hGs]
       have hKrow (x : Ω) : (∫ y, K x y ∂μ) ≤ a*M := by
         have hm : Measurable (G x) := hGm.comp (measurable_const.prodMk measurable_id)
         have hGi : Integrable (G x) μ := (integrable_const C).mono' hm.aestronglyMeasurable (Eventually.of_forall (hGnorm x))
         have hKi : Integrable (K x) μ := (integrable_const (1:ℝ)).mono'
           (hKm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
           (Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hKb x y).1] using (hKb x y).2)
         calc
           _ ≤ ∫ y, a*G x y ∂μ := integral_mono hKi (hGi.const_mul a) (fun y => by
             have h := (remainder_bounds a (G x y) ha (hGb x y).1).1
             dsimp [K,remainder] at ⊢ h
             linarith)
           _ = a*(∫ y, G x y ∂μ) := integral_const_mul _ _
           _ ≤ a*M := mul_le_mul_of_nonneg_left (hrow x) ha
       obtain ⟨T,hT,hu⟩ := ReferenceKernelSchur μ K hKm 1 (a*M)
         zero_le_one (mul_nonneg ha hM) hKb hKs hKrow
       obtain ⟨S,hS,_⟩ := ReferenceKernelSchur μ R hRm (a*C) r
         (mul_nonneg ha hC) hr hRb hRs hRrow
       have hlo (v : Lp ℝ 2 μ) : -r*‖v‖^2 ≤ inner ℝ v (T v) := by
         have heT := kernel_operator_quadratic μ K hKm 1
           (fun x y => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hKb x y).1] using (hKb x y).2) T hT.2.2 v
         have heS := kernel_operator_quadratic μ R hRm (a*C) hRnorm S hS.2.2 v
         have hi := (Lp.memLp v).integrable (by norm_num)
         have hGprod : Integrable (fun p : Ω × Ω => v p.1*v p.2*G p.1 p.2) (μ.prod μ) := by
           simpa only [mul_comm] using (hi.mul_prod hi).bdd_mul hGm.aestronglyMeasurable (Eventually.of_forall fun p => hGnorm p.1 p.2)
         have hRprod : Integrable (fun p : Ω × Ω => v p.1*v p.2*R p.1 p.2) (μ.prod μ) := by
           simpa only [mul_comm] using (hi.mul_prod hi).bdd_mul hRm.aestronglyMeasurable (Eventually.of_forall fun p => hRnorm p.1 p.2)
         have hsplit : inner ℝ v (T v)=a*(∫ p : Ω × Ω, v p.1*v p.2*G p.1 p.2 ∂μ.prod μ)-inner ℝ v (S v) := by
           rw [heT,heS,← integral_const_mul,← integral_sub (hGprod.const_mul a) hRprod]
           apply integral_congr_ae
           exact Eventually.of_forall fun p => by dsimp [K,R,remainder]; ring
         have hSupper : inner ℝ v (S v) ≤ r*‖v‖^2 := by
           calc
             _ ≤ ‖v‖*‖S v‖ := real_inner_le_norm _ _
             _ ≤ ‖v‖*(r*‖v‖) := mul_le_mul_of_nonneg_left ((S.le_opNorm v).trans
               (mul_le_mul_of_nonneg_right hS.1 (norm_nonneg _))) (norm_nonneg _)
             _ = _ := by ring
         have hp := mul_nonneg ha (hPSD v (Lp.memLp v))
         rw [hsplit]
         linarith
       refine ⟨T,⟨hT.1,hT.2.1,hlo,hT.2.2⟩,?_⟩
       intro U hU
       exact hu U ⟨hU.1,hU.2.1,hU.2.2.2⟩
    let G := fun x y : OneParticle d => RieszKernel s ε (x-y)
    let C := (ε^2)^(-s/2)/s
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hGm : Measurable (fun q : OneParticle d × OneParticle d => G q.1 q.2) := by
      dsimp [G]
      simp only [RieszKernel, ne_of_gt hε, if_false]
      fun_prop
    have hGs (x y : OneParticle d) : G x y = G y x := by
      dsimp [G]
      simp only [RieszKernel, ne_of_gt hε, if_false, norm_sub_rev]
    have hGb (x y : OneParticle d) : 0 ≤ G x y ∧ G x y ≤ C := by
      dsimp [G, C]
      simp only [RieszKernel, ne_of_gt hε, if_false]
      refine ⟨by positivity, ?_⟩
      exact div_le_div_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos (by positivity)
          (by nlinarith [sq_nonneg ‖x-y‖]) (by linarith)) hs.le
    exact positive_type_mayer_operator (ReferenceLaw V b) G hGm hGs C M a R
      hC hM ha hR hGb hrow hRrow
      (fun f hf => SoftRieszReferencePositive d s ε hs hε (ReferenceLaw V b) f hf)
  let Q := L * Real.exp M1 /
    (volume : Measure (OneParticle d)).real (Metric.ball 0 1)
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    exact div_nonneg (mul_nonneg (by linarith) (Real.exp_pos _).le)
      ENNReal.toReal_nonneg
  obtain ⟨C, hC, hdata⟩ := ReferenceOffsetDensity d hd s κ L M1 hs hsd hκ hL
  refine ⟨C, hC, ?_⟩
  intro δ hδ
  obtain ⟨a₀, ha₀, hrem⟩ := MayerUniformRemainder d hd s Q hs hsd hQ δ hδ
  refine ⟨a₀, ha₀, ?_⟩
  intro V b hV hb hquad hlocal ε hε a ha haa
  have hmodel := hdata V b hV hb hquad hlocal
  have hprob := hmodel.2.2.1
  letI : IsProbabilityMeasure (ReferenceLaw V b) := hprob
  have hcap := hmodel.2.2.2.1
  have hrows := hmodel.2.2.2.2 ε hε.le
  apply actual_mayer d V b s ε a C (a * δ) hs hε ha hC (mul_nonneg ha hδ.le)
  · intro x
    simpa only [RieszKernel, norm_sub_rev] using (hrows x).2
  · intro x
    have hr := hrem (ReferenceLaw V b) hprob hcap ε hε.le a ha haa x
    simpa only [RieszKernel, norm_sub_rev] using hr.2.2
