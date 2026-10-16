module

public import Tablet.GradientGraphClosure
public import Tablet.ClosedGradientEnergy
public import Tablet.ExtendedEntropy
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
-- [TABLET NODE: GradientClosureInequalityExtension]
theorem GradientClosureInequalityExtension (d N : ℕ) (P : Measure (Configuration d N))
    [IsProbabilityMeasure P] (Cpi Clsi : ℝ)
    (hPI : ∀g:Configuration d N→ℝ,g∈SmoothCore d N →
      MemLp g 2 P → MemLp (CoordinateGradient g) 2 P →
      variance g P≤Cpi*(∫x,‖CoordinateGradient g x‖^2∂P))
    (hLSI : ∀g:Configuration d N→ℝ,g∈SmoothCore d N →
      MemLp g 2 P → MemLp (CoordinateGradient g) 2 P →
      ExtendedEntropy P (fun x=>g x^2)≤ENNReal.ofReal (Clsi*(∫x,‖CoordinateGradient g x‖^2∂P)))
    (f : Lp ℝ 2 P) (v : Lp (EuclideanSpace ℝ (Fin N×Fin d)) 2 P)
    (hfv : (f,v)∈GradientGraphClosure P false) :
    variance (f:Configuration d N→ℝ) P≤Cpi*ClosedGradientEnergy v ∧
    ExtendedEntropy P (fun x=>f x^2)≤ENNReal.ofReal (Clsi*ClosedGradientEnergy v) := by
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
  have extended_entropy_l2_repr {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      (f : Lp ℝ 2 P) :
      ExtendedEntropy P (fun x=>f x ^ 2) =
      ∫⁻ x, ENNReal.ofReal (f x^2*Real.log (f x^2) - f x^2*Real.log (‖f‖^2) - f x^2 + ‖f‖^2) ∂P := by
    have hb := l2_square P f
    unfold ExtendedEntropy
    rw [hb]
    dsimp only
    split_ifs with hz
    · have hf : f=0 := by simpa using (sq_eq_zero_iff.mp hz)
      subst f
      symm
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := P)] with x hx
      change ENNReal.ofReal (((0:Lp ℝ 2 P):Ω→ℝ) x^2*Real.log (((0:Lp ℝ 2 P):Ω→ℝ) x^2) - ((0:Lp ℝ 2 P):Ω→ℝ) x^2*Real.log (‖(0:Lp ℝ 2 P)‖^2) - ((0:Lp ℝ 2 P):Ω→ℝ) x^2 + ‖(0:Lp ℝ 2 P)‖^2)=0
      change ((0:Lp ℝ 2 P):Ω→ℝ) x=0 at hx
      rw [hx]
      simp
    · apply lintegral_congr
      intro x
      by_cases hx : f x^2=0
      · simp [hx]
      · rw [Real.log_div hx hz]
        congr 1
        ring
  have extended_entropy_l2_limit_bound {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      (f : ℕ→Lp ℝ 2 P) (g : Lp ℝ 2 P) (hf : Tendsto f atTop (𝓝 g))
      (B : ℕ→ENNReal) (b : ENNReal) (hB : Tendsto B atTop (𝓝 b))
      (hbound : ∀n,ExtendedEntropy P (fun x=>f n x^2)≤B n) :
      ExtendedEntropy P (fun x=>g x^2)≤b := by
    by_cases hg : ‖g‖^2=0
    · unfold ExtendedEntropy
      rw [l2_square P g,if_pos hg]
      exact bot_le
    obtain ⟨ns,hns,hae⟩ := (tendstoInMeasure_of_tendsto_Lp hf).exists_seq_tendsto_ae
    let H := fun n x=> ENNReal.ofReal
      (f (ns n) x^2*Real.log (f (ns n) x^2) - f (ns n) x^2*Real.log (‖f (ns n)‖^2) - f (ns n) x^2 + ‖f (ns n)‖^2)
    have hmass : Tendsto (fun n=>‖f (ns n)‖^2) atTop (𝓝 (‖g‖^2)) :=
      (hf.comp hns.tendsto_atTop).norm.pow 2
    have hpoint : ∀ᵐx∂P,Tendsto (fun n=>H n x) atTop
        (𝓝 (ENNReal.ofReal (g x^2*Real.log (g x^2)-g x^2*Real.log (‖g‖^2)-g x^2+‖g‖^2))) := by
      filter_upwards [hae] with x hx
      have hsq := hx.pow 2
      have hmul := Real.continuous_mul_log.continuousAt.tendsto.comp hsq
      exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (((hmul.sub (hsq.mul (hmass.log hg))).sub hsq).add hmass)
    have hmeas (n:ℕ) : AEMeasurable (H n) P := by
      have hu := (Lp.aestronglyMeasurable (f (ns n))).aemeasurable.pow_const 2
      exact (((hu.mul (Real.measurable_log.comp_aemeasurable hu)).sub
        (hu.mul_const _)).sub hu |>.add_const _).ennreal_ofReal
    have hfatou : ExtendedEntropy P (fun x=>g x^2)≤liminf (fun n=>∫⁻x,H n x∂P) atTop := by
      rw [extended_entropy_l2_repr]
      calc
        _ = ∫⁻x,liminf (fun n=>H n x) atTop∂P :=
          lintegral_congr_ae (hpoint.mono fun _ h=>h.liminf_eq.symm)
        _ ≤ _ := lintegral_liminf_le' hmeas
    apply hfatou.trans
    have hb' : ∀n,(∫⁻x,H n x∂P)≤B (ns n) := by
      intro n
      simpa only [extended_entropy_l2_repr,H] using hbound (ns n)
    exact (liminf_le_liminf (Eventually.of_forall hb')).trans_eq
      (hB.comp hns.tendsto_atTop).liminf_eq
  have extended_entropy_congr {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      (u v : Ω→ℝ) (h : u=ᵐ[P]v) : ExtendedEntropy P u=ExtendedEntropy P v := by
    unfold ExtendedEntropy
    rw [integral_congr_ae h]
    dsimp only
    split_ifs
    · rfl
    · exact lintegral_congr_ae (h.mono fun _ hx=>by dsimp only; rw [hx])
  have closed_graph_log_sobolev (d N : ℕ) (P : Measure (Configuration d N)) (C : ℝ)
      (hLSI : ∀g:Configuration d N→ℝ,g∈SmoothCore d N →
        ∀(hg:MemLp g 2 P) (hD:MemLp (CoordinateGradient g) 2 P),
        ExtendedEntropy P (fun x=>g x^2)≤ENNReal.ofReal (C*(∫x,‖CoordinateGradient g x‖^2∂P)))
      (f : Lp ℝ 2 P) (v : Lp (EuclideanSpace ℝ (Fin N×Fin d)) 2 P)
      (hfv : (f,v)∈GradientGraphClosure P false) :
      ExtendedEntropy P (fun x=>f x^2)≤ENNReal.ofReal (C*ClosedGradientEnergy v) := by
    obtain ⟨p,hp,hpconv⟩ := mem_closure_iff_seq_limit.mp hfv
    have hpi (n:ℕ) : ExtendedEntropy P (fun x=>(p n).1 x^2)≤ENNReal.ofReal (C*‖(p n).2‖^2) := by
      obtain ⟨g,hg,hD,hs,heq⟩ := hp n
      change g∈SmoothCore d N at hs
      rw [heq]
      dsimp only [Prod.fst,Prod.snd]
      have he : ExtendedEntropy P (fun x=>hg.toLp g x^2)=ExtendedEntropy P (fun x=>g x^2) :=
        extended_entropy_congr P _ _ (hg.coeFn_toLp.mono fun _ hx=>by dsimp only; rw [hx])
      rw [he]
      have henergy : ‖hD.toLp (CoordinateGradient g)‖^2 = ∫x,‖CoordinateGradient g x‖^2∂P := by
        rw [← l2_energy P]
        exact integral_congr_ae (hD.coeFn_toLp.mono fun _ hx=>by dsimp only; rw [hx])
      rw [henergy]
      exact hLSI g hs hg hD
    apply extended_entropy_l2_limit_bound P (fun n=>(p n).1) f (continuous_fst.tendsto (f,v) |>.comp hpconv)
      (fun n=>ENNReal.ofReal (C*‖(p n).2‖^2)) (ENNReal.ofReal (C*‖v‖^2)) _ hpi
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (((continuous_snd.tendsto (f,v) |>.comp hpconv).norm.pow 2).const_mul C)
  exact ⟨closed_graph_poincare d N P Cpi hPI f v hfv,
    closed_graph_log_sobolev d N P Clsi hLSI f v hfv⟩
