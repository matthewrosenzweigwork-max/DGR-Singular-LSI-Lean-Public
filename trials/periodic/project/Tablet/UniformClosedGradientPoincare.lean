import Tablet.UniformSmoothPoincare
import Tablet.ClosedGradientEnergy
import Mathlib.MeasureTheory.Function.L2Space
open MeasureTheory ProbabilityTheory Set
-- [TABLET NODE: UniformClosedGradientPoincare]
theorem UniformClosedGradientPoincare (d : ℕ) (hd : 2 ≤ d)
    (s a B l u : ℝ) (hs : 0 ≤ s) (hsd : s ≤ (d : ℝ) - 2)
    (ha : 0 < a) (hB : 0 ≤ B) (hl : 0 < l) (hl1 : l ≤ 1) (hu : 1 ≤ u) :
    ∃ rate : ℝ, 0 < rate ∧ ∀ (N : ℕ), 2 ≤ N →
      ∀ (β : ℝ), 0 ≤ β → β ≤ B → ∀ (q : BoundedBackground d l u),
      ∀ (ε : ℝ), 0 ≤ ε →
      let P := CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β
      ∀ (f : Lp ℝ 2 P) (v : Lp (EuclideanSpace ℝ (Fin N×Fin d)) 2 P),
      (f,v)∈GradientGraphClosure P false →
      variance (f:Configuration d N→ℝ) P≤rate⁻¹*ClosedGradientEnergy v := by
-- BODY
  have l2_energy {Ω E : Type} [MeasurableSpace Ω] [NormedAddCommGroup E]
      [InnerProductSpace ℝ E] (P : Measure Ω) (v : Lp E 2 P) :
      (∫x,‖v x‖^2∂P)=‖v‖^2 := by
    rw [←real_inner_self_eq_norm_sq, L2.inner_def]
    simp_rw [real_inner_self_eq_norm_sq]
  have l2_square {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (f : Lp ℝ 2 P) :
      (∫x,(f x)^2∂P)=‖f‖^2 := by
    simpa only [Real.norm_eq_abs,sq_abs] using l2_energy P f
  have l2_variance_continuous {Ω : Type} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] :
      Continuous (fun f : Lp ℝ 2 P => variance (f : Ω→ℝ) P) := by
    let one : Lp ℝ 2 P := (memLp_const (1:ℝ)).toLp (fun _=>1)
    have hmean (f : Lp ℝ 2 P) : inner ℝ f one = ∫x,f x∂P := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(memLp_const (1:ℝ)).coeFn_toLp] with x hx
      rw [hx]
      simp
    have hm : Continuous (fun f : Lp ℝ 2 P => ∫x,f x∂P) := by
      have hc : Continuous (fun f : Lp ℝ 2 P => inner ℝ f one) := continuous_id.inner continuous_const
      simpa only [hmean] using hc
    have he (f : Lp ℝ 2 P) : variance (f : Ω→ℝ) P = ‖f‖^2-(∫x,f x∂P)^2 := by
      rw [variance_eq_sub (Lp.memLp f)]
      change (∫x,(f x)^2∂P)-(∫x,f x∂P)^2 = _
      rw [l2_square]
    have hc : Continuous (fun f : Lp ℝ 2 P => ‖f‖^2-(∫x,f x∂P)^2) :=
      (continuous_norm.pow 2).sub (hm.pow 2)
    simpa only [he] using hc
  have closed_graph_poincare (d N : ℕ) (P : Measure (Configuration d N))
      [IsProbabilityMeasure P] (C : ℝ)
      (hPI : ∀ f : Configuration d N→ℝ, f∈SmoothCore d N →
        MemLp f 2 P → MemLp (CoordinateGradient f) 2 P →
        variance f P ≤ C*(∫X,‖CoordinateGradient f X‖^2∂P))
      (f : Lp ℝ 2 P) (v : Lp (EuclideanSpace ℝ (Fin N×Fin d)) 2 P)
      (hfv : (f,v)∈GradientGraphClosure P false) :
      variance (f : Configuration d N→ℝ) P ≤ C*ClosedGradientEnergy v := by
    have hclosed : IsClosed {p : Lp ℝ 2 P × Lp (EuclideanSpace ℝ (Fin N×Fin d)) 2 P |
        variance (p.1 : Configuration d N→ℝ) P ≤ C*‖p.2‖^2} :=
      isClosed_le ((l2_variance_continuous P).comp continuous_fst)
        (continuous_const.mul (continuous_snd.norm.pow 2))
    apply (closure_minimal (t := {p : Lp ℝ 2 P × Lp (EuclideanSpace ℝ (Fin N×Fin d)) 2 P |
        variance (p.1 : Configuration d N→ℝ) P ≤ C*‖p.2‖^2}) ?_ hclosed) hfv
    rintro p ⟨g,hg,hD,hs,rfl⟩
    change g∈SmoothCore d N at hs
    change variance ((hg.toLp g) : Configuration d N→ℝ) P ≤ C*‖hD.toLp (CoordinateGradient g)‖^2
    have hv := variance_congr hg.coeFn_toLp
    rw [hv]
    apply (hPI g hs hg hD).trans_eq
    congr 1
    rw [←l2_energy P (hD.toLp (CoordinateGradient g))]
    apply integral_congr_ae
    filter_upwards [hD.coeFn_toLp] with X hX
    rw [hX]
  obtain ⟨rate,hrate,hPI⟩ := UniformSmoothPoincare d hd s a B l u hs hsd ha hB hl hl1 hu
  refine ⟨rate,hrate,?_⟩
  intro N hN β hβ hβB q ε hε
  let P := CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β
  have hsd' : s<(d:ℝ) := by linarith
  letI : IsProbabilityMeasure P :=
    (CanonicalCutoffConvergence d N hd hN s a l u β hs hsd' ha q hβ).1 ε hε
  change ∀ (f:Lp ℝ 2 P) (v:Lp (EuclideanSpace ℝ (Fin N×Fin d)) 2 P),
    (f,v)∈GradientGraphClosure P false → variance (f:Configuration d N→ℝ) P≤rate⁻¹*ClosedGradientEnergy v
  intro f v hfv
  apply closed_graph_poincare d N P rate⁻¹ _ f v hfv
  intro g hg _ _
  exact hPI N hN β hβ hβB q ε hε g hg
