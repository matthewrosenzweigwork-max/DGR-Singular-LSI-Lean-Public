import Tablet.RieszPositiveConvolution
import Tablet.ProbabilityConvolutionJensenInputs
import Tablet.BoundedEntropyQuadraticFixedPoint
open MeasureTheory UnitAddTorus
open scoped Topology

-- [TABLET NODE: RieszThermalEulerLagrange]
theorem RieszThermalEulerLagrange (d : ℕ) (hd : 2 ≤ d) (s a ε β : ℝ)
    (hs : 0 ≤ s) (hsd : s < (d : ℝ)) (ha : 0 < a) (hε : 0 < ε) (hβ : 0 ≤ β)
    (q : UnitAddTorus (Fin d) → ℝ) (qlo qhi : ℝ)
    (hqlo : 0 < qlo) (hqm : Measurable q)
    (hq : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), qlo ≤ q x ∧ q x ≤ qhi) :
    ∃ C L : ℝ, 0 < C ∧ 0 ≤ L ∧ (∀ x, ‖RieszKernel d s a ε x‖ ≤ C) ∧
    ∃ ρ : UnitAddTorus (Fin d) → ℝ,
      Measurable ρ ∧ Integrable ρ volume ∧ (∫ x, ρ x) = 1 ∧
      (∀ᵐ x ∂volume, 0 < ρ x ∧ ρ x ≤ Real.exp (2*(L+β*C))) ∧
      (∀ x, ‖∫ y, RieszKernel d s a ε (x-y)*ρ y‖ ≤ C) ∧
      (∀ᵐ x ∂volume, ρ x = q x*Real.exp (-β*(∫ y, RieszKernel d s a ε (x-y)*ρ y)) /
        (∫ z, q z*Real.exp (-β*(∫ y, RieszKernel d s a ε (z-y)*ρ y)))) := by
-- BODY
  classical
  letI : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
    ⟨by rw [AddCircle.volume_eq_smul_haarAddCircle]; simp⟩
  have hlogc : ContinuousOn Real.log (Set.Icc qlo qhi) :=
    Real.continuousOn_log.mono fun x hx => (hqlo.trans_le hx.1).ne'
  obtain ⟨L₀, hL₀⟩ := (isCompact_Icc : IsCompact (Set.Icc qlo qhi)).exists_bound_of_continuousOn hlogc
  let L := max 0 L₀
  have hL : 0 ≤ L := le_max_left _ _
  have hlog : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), |Real.log (q x)| ≤ L :=
    hq.mono fun x hx => by simpa only [Real.norm_eq_abs] using (hL₀ (q x) hx).trans (le_max_right _ _)
  have halp : MemLp (fun x => Real.log (q x)) 2 (volume : Measure (UnitAddTorus (Fin d))) :=
    MemLp.of_bound hqm.log.aestronglyMeasurable L (by simpa only [Real.norm_eq_abs] using hlog)
  let A : Lp ℝ 2 (volume : Measure (UnitAddTorus (Fin d))) := halp.toLp (fun x => Real.log (q x))
  have hAeq : ∀ᵐ x ∂volume, A x = Real.log (q x) := MemLp.coeFn_toLp halp
  have hAb : ∀ᵐ x ∂volume, |A x| ≤ L := by filter_upwards [hAeq, hlog] with x hx hy; simpa only [hx] using hy
  obtain ⟨C, hC, hgb, T, hT⟩ := RieszPositiveConvolution d hd s a ε hs hsd ha hε
  obtain ⟨c, _, hfund⟩ := RieszL1Foundation d hd s a hs hsd ha
  have hgm := (hfund ε hε.le).1
  have potential_bound (r : Lp ℝ 2 (volume : Measure (UnitAddTorus (Fin d))))
      (hr : ∀ᵐ x ∂volume, 0 ≤ r x) (hm : (∫ x, r x) = 1) :
      ∀ x, ‖∫ y, RieszKernel d s a ε (x-y)*r y‖ ≤ C := by
    let ρ := (Lp.aestronglyMeasurable r).mk r
    have hρm : Measurable ρ := (Lp.aestronglyMeasurable r).stronglyMeasurable_mk.measurable
    have heq : r =ᵐ[volume] ρ := (Lp.aestronglyMeasurable r).ae_eq_mk
    have hri := (Lp.memLp r).integrable (by norm_num : (1 : ENNReal) ≤ 2)
    have hgi : Integrable (RieszKernel d s a ε) volume := (hfund ε hε.le).2.1
    have hgl : ∀ x, -C ≤ RieszKernel d s a ε x := fun x =>
      (abs_le.mp (by simpa only [Real.norm_eq_abs] using hgb x)).1
    have hb := ProbabilityConvolutionJensenInputs d (RieszKernel d s a ε) (fun _ => 0) ρ
      hgm hgi measurable_const hρm 0 C C
      (Filter.Eventually.of_forall fun _ => ⟨le_rfl, le_rfl⟩) le_rfl hgb hgl
      (hri.congr heq) (hr.congr (heq.mono fun _ hx => by rw [hx]))
      ((integral_congr_ae heq).symm.trans hm)
    intro x
    have hc : (∫ y, RieszKernel d s a ε (x-y)*r y) =
        ∫ y, RieszKernel d s a ε (x-y)*ρ y :=
      integral_congr_ae (heq.mono fun _ hy => by dsimp; rw [hy])
    simpa only [hc, Real.norm_eq_abs] using (hb.2.1 x).2.2
  have hpot (r : Lp ℝ 2 (volume : Measure (UnitAddTorus (Fin d))))
      (hr : ∀ᵐ x ∂volume, r x ∈ Set.Icc 0 (Real.exp (2*(L+β*C)))) (hm : (∫ x, r x) = 1) :
      ∀ᵐ x ∂volume, |(T r) x| ≤ C := by
    have hb := potential_bound r (hr.mono fun _ hx => hx.1) hm
    have hrep := (hT.2.2.2 r (Lp.memLp r)).2
    rw [Lp.toLp_coeFn r (Lp.memLp r)] at hrep
    exact hrep.mono fun x hx => by simpa only [hx, Real.norm_eq_abs] using hb x
  obtain ⟨r, hr, hrm, hreq⟩ := BoundedEntropyQuadraticFixedPoint volume β L C hβ hL hC.le A hAb T
    hT.2.2.1 hT.2.1 hpot
  let ρ := (Lp.aestronglyMeasurable r).mk r
  have hρm : Measurable ρ := (Lp.aestronglyMeasurable r).stronglyMeasurable_mk.measurable
  have hρeq : r =ᵐ[volume] ρ := (Lp.aestronglyMeasurable r).ae_eq_mk
  have hρi : Integrable ρ volume := ((Lp.memLp r).integrable (by norm_num : (1 : ENNReal) ≤ 2)).congr hρeq
  have hconv (x : UnitAddTorus (Fin d)) :
      (∫ y, RieszKernel d s a ε (x-y)*r y) = ∫ y, RieszKernel d s a ε (x-y)*ρ y :=
    integral_congr_ae (hρeq.mono fun _ hy => by dsimp; rw [hy])
  have hrep := (hT.2.2.2 r (Lp.memLp r)).2
  rw [Lp.toLp_coeFn r (Lp.memLp r)] at hrep
  have hexp : (fun x => Real.exp (A x-β*(T r) x)) =ᵐ[volume]
      fun x => q x*Real.exp (-β*(∫ y, RieszKernel d s a ε (x-y)*ρ y)) := by
    filter_upwards [hAeq, hrep, hq] with x hx hy hz
    rw [hx, hy, hconv]
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (hqlo.trans_le hz.1), neg_mul]
  have hZ := integral_congr_ae hexp
  have hb := potential_bound r (hr.mono fun _ hx => hx.1.le) hrm
  refine ⟨C, L, hC, hL, hgb, ρ, hρm, hρi, ?_, ?_, ?_, ?_⟩
  · exact (integral_congr_ae hρeq).symm.trans hrm
  · exact hr.congr (hρeq.mono fun _ hx => by simp only [hx])
  · intro x; rw [← hconv]; exact hb x
  · filter_upwards [hreq, hρeq, hexp] with x hx hy hz
    rw [← hy, ← hz, ← hZ]
    exact hx
