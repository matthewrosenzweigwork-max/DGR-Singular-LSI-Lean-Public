import Tablet.GroundStateClipping
import Tablet.ClipCutoffApproximation
import Tablet.TorusHaarPoincare
import Tablet.VarianceVariational
import Tablet.TiltNormalization
import Tablet.TorusFourierLaplacian
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Constructions
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic
open MeasureTheory ProbabilityTheory Set Function Filter
open scoped ContDiff ENNReal NNReal
-- [TABLET NODE: CompactWeightedPoincare]
theorem CompactWeightedPoincare (d : ℕ) (hd : 0 < d) (K L : ℝ)
    (hK : 0 ≤ K) (hL : 0 ≤ L) :
    ∃ rate : ℝ, 0 < rate ∧
      ∀ (V : UnitAddTorus (Fin d) → ℝ), TorusSmooth V →
      (∀ x, 0 ≤ V x) → (∫ x, V x) ≤ K →
      (∀ x, TorusLaplacian V x ≤ L) →
      ∀ (f : UnitAddTorus (Fin d) → ℝ), TorusSmooth f →
      ProbabilityTheory.variance f
        (NormalizedTilt MeasureTheory.volume (fun x => Real.exp (-V x))) ≤
      rate⁻¹ * (∫ x, ‖TorusGradient f x‖^2
        ∂NormalizedTilt MeasureTheory.volume (fun x => Real.exp (-V x))) := by
-- BODY
  have quotient (d : ℕ) : IsOpenQuotientMap (TorusLift d) := by
    have hc : IsOpenQuotientMap ((↑) : ℝ → AddCircle (1 : ℝ)) :=
      QuotientAddGroup.isOpenQuotientMap_mk
    have hp : IsOpenQuotientMap
        (Pi.map (fun _ : Fin d => ((↑) : ℝ → AddCircle (1 : ℝ)))) :=
      IsOpenQuotientMap.piMap (fun _ => hc)
    exact hp.comp (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isOpenQuotientMap

  have lift_translation_eq {d : ℕ} (y z : EuclideanSpace ℝ (Fin d))
      (h : TorusLift d y = TorusLift d z) (x : EuclideanSpace ℝ (Fin d)) :
      TorusLift d (x + (z-y)) = TorusLift d x := by
    funext j
    have hj := congrFun h j
    change (y j : AddCircle (1 : ℝ)) = (z j : AddCircle (1 : ℝ)) at hj
    simp only [TorusLift, PiLp.add_apply, PiLp.sub_apply]
    rw [AddCircle.coe_add, AddCircle.coe_sub, ← hj, sub_self, add_zero]

  have lift_fderiv_eq {d : ℕ} (f : UnitAddTorus (Fin d) → ℝ)
      (y z : EuclideanSpace ℝ (Fin d)) (h : TorusLift d y = TorusLift d z) :
      fderiv ℝ (fun x => f (TorusLift d x)) y =
        fderiv ℝ (fun x => f (TorusLift d x)) z := by
    let q := fun x => f (TorusLift d x)
    have hfun : (fun x => q (x+(z-y))) = q := by
      funext x
      exact congrArg f (lift_translation_eq y z h x)
    have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := q) (x := y) (z-y)
    rw [hfun] at hd
    simpa using hd

  have gradient_on_lift {d : ℕ} (f : UnitAddTorus (Fin d) → ℝ)
      (y : EuclideanSpace ℝ (Fin d)) (j : Fin d) :
      TorusGradient f (TorusLift d y) j =
        fderiv ℝ (fun x => f (TorusLift d x)) y (EuclideanSpace.single j 1) := by
    let z : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2
      (fun j => (AddCircle.equivIco (1 : ℝ) 0 (TorusLift d y j) : ℝ))
    have hz : TorusLift d z = TorusLift d y := by
      funext j
      simp [TorusLift, z]
    change fderiv ℝ (fun x => f (TorusLift d x)) z (EuclideanSpace.single j 1) = _
    rw [lift_fderiv_eq f z y hz]

  have tail_parameters (p C K : ℝ) (hp : 2 < p) (hC : 0 < C) (hK : 0 ≤ K) :
      ∃ t R : ℝ, 0 < t ∧ 0 < R ∧
        C^2 * Real.rpow (K / t) (1 - 2 / p) +
          Real.rpow C p * Real.rpow R (2 - p) * Real.exp ((p - 2) * t / 2) ≤ 1 / 12 := by
    have hp0 : 0 < p := by linarith
    have hα : 0 < 1 - 2 / p := by
      rw [sub_pos, div_lt_one hp0]
      exact hp
    have htlim : Tendsto (fun t : ℝ => C^2 * Real.rpow (K / t) (1 - 2 / p))
        atTop (nhds 0) := by
      have h := ((tendsto_id.const_div_atTop K).rpow_const (Or.inr hα.le)).const_mul (C^2)
      convert! h using 1 <;> simp only [id_eq, Real.zero_rpow hα.ne', mul_zero]
    obtain ⟨t, ht, hsmall⟩ :=
      ((eventually_gt_atTop (0 : ℝ)).and
        (htlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 24)))).exists
    have hRlim : Tendsto (fun R : ℝ =>
        Real.rpow C p * Real.rpow R (2 - p) * Real.exp ((p - 2) * t / 2))
        atTop (nhds 0) := by
      have hh := ((tendsto_rpow_neg_atTop (by linarith : 0 < p - 2)).const_mul
        (Real.rpow C p)).mul_const (Real.exp ((p - 2) * t / 2))
      convert! hh using 1 <;> simp only [neg_sub, mul_zero, zero_mul] <;> rfl
    obtain ⟨R, hR, hRsmall⟩ :=
      ((eventually_gt_atTop (0 : ℝ)).and
        (hRlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 24)))).exists
    exact ⟨t, R, ht, hR, by linarith⟩

  have continuous_memLp {α E : Type} [MeasurableSpace α] [TopologicalSpace α]
      [BorelSpace α] [CompactSpace α] [Nonempty α] [NormedAddCommGroup E]
      [SecondCountableTopologyEither α E] {μ : Measure α} [IsFiniteMeasure μ]
      (f : α → E) (hf : Continuous f) (p : ℝ≥0∞) : MemLp f p μ := by
    rcases isCompact_univ.exists_isMaxOn Set.univ_nonempty hf.norm.continuousOn
      with ⟨x0, _, hmax⟩
    exact MemLp.of_bound hf.aestronglyMeasurable ‖f x0‖
      (Filter.Eventually.of_forall fun x => hmax (Set.mem_univ x))

  have tilt_transfer {d : ℕ} (V : UnitAddTorus (Fin d) → ℝ) (hV : TorusSmooth V)
      (M : ℝ) (hZ : 0 < ∫ x, Real.exp (-V x))
      (hden : ∀ x, Real.exp (-V x) / (∫ y, Real.exp (-V y)) ≤ M) :
      IsProbabilityMeasure (NormalizedTilt volume (fun x => Real.exp (-V x))) ∧
        ∀ H : UnitAddTorus (Fin d) → ℝ, Continuous H → (∀ x, 0 ≤ H x) →
          (∫ x, H x ∂NormalizedTilt volume (fun x => Real.exp (-V x))) ≤ M * ∫ x, H x := by
    let w : UnitAddTorus (Fin d) → ℝ := fun x => Real.exp (-V x)
    have hw : Continuous w := Real.continuous_exp.comp (TorusFourierLaplacian d V hV).1.neg
    have hwi : Integrable w volume :=
      hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    obtain ⟨hprob, htilt⟩ := TiltNormalization volume w hw.measurable
      (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le) hwi hZ
    refine ⟨hprob, ?_⟩
    intro H hH hH0
    have hHi : Integrable H volume :=
      hH.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hHwi : Integrable (fun x => H x * w x) volume :=
      (hH.mul hw).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [(htilt H hH.measurable hHwi).2]
    calc
      (∫ x, H x * w x) / (∫ x, w x) = ∫ x, H x * (w x / ∫ y, w y) := by
        rw [← integral_div]
        congr 1
        ext x
        ring
      _ ≤ ∫ x, M * H x := by
        apply integral_mono
        · exact (hHwi.div_const (∫ x, w x)).congr
            (Filter.Eventually.of_forall fun x => by dsimp; ring)
        · exact hHi.const_mul M
        · intro x
          simpa only [mul_comm M] using mul_le_mul_of_nonneg_left (hden x) (hH0 x)
      _ = M * ∫ x, H x := integral_const_mul M _

  have gradient_affine {d : ℕ} (f : UnitAddTorus (Fin d) → ℝ) (hf : TorusSmooth f)
      (c b : ℝ) (x : UnitAddTorus (Fin d)) :
      TorusGradient (fun z => c * (f z - b)) x = c • TorusGradient f x := by
    obtain ⟨y, rfl⟩ := (quotient d).surjective x
    ext j
    simp only [PiLp.smul_apply, smul_eq_mul, gradient_on_lift]
    have hd := ((hf.differentiable (by simp) y).hasFDerivAt.sub_const b).const_mul c
    change fderiv ℝ (fun z => c * (f (TorusLift d z) - b)) y _ = _
    rw [hd.fderiv]
    simp

  have normalized_violator {d : ℕ} (μ : Measure (UnitAddTorus (Fin d)))
      [IsProbabilityMeasure μ] (f : UnitAddTorus (Fin d) → ℝ) (hf : TorusSmooth f)
      (r : ℝ) (hr : 0 < r)
      (hstrict : (∫ x, ‖TorusGradient f x‖^2 ∂μ) < r * variance f μ) :
      ∃ g : UnitAddTorus (Fin d) → ℝ, TorusSmooth g ∧
        (∫ x, (g x)^2 ∂μ) = 1 ∧ variance g μ = 1 ∧
        (∫ x, ‖TorusGradient g x‖^2 ∂μ) < r := by
    have hvar : 0 < variance f μ := by
      have hE : 0 ≤ ∫ x, ‖TorusGradient f x‖^2 ∂μ := integral_nonneg fun x => sq_nonneg _
      have hprod : 0 < r * variance f μ := hE.trans_lt hstrict
      exact (mul_pos_iff_of_pos_left hr).mp hprod
    have hfm : MemLp f 2 μ := continuous_memLp f (TorusFourierLaplacian d f hf).1 2
    let b : ℝ := ∫ x, f x ∂μ
    let c : ℝ := (Real.sqrt (variance f μ))⁻¹
    let g : UnitAddTorus (Fin d) → ℝ := fun x => c * (f x - b)
    have hg : TorusSmooth g := contDiff_const.mul (hf.sub contDiff_const)
    have hcoef : c^2 * variance f μ = 1 := by
      dsimp [c]
      rw [inv_pow, Real.sq_sqrt hvar.le]
      exact inv_mul_cancel₀ hvar.ne'
    have hcenter : (∫ x, (f x - b)^2 ∂μ) = variance f μ := by
      have hh := (VarianceVariational μ f hfm b).1
      simpa only [b, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] using hh
    have hnorm : (∫ x, (g x)^2 ∂μ) = 1 := by
      dsimp [g]
      simp_rw [mul_pow]
      rw [integral_const_mul, hcenter, hcoef]
    have hvg : variance g μ = 1 := by
      dsimp [g]
      rw [variance_const_mul, variance_sub_const hfm.aestronglyMeasurable, hcoef]
    have henergy : (∫ x, ‖TorusGradient g x‖^2 ∂μ) =
        c^2 * (∫ x, ‖TorusGradient f x‖^2 ∂μ) := by
      simp_rw [show TorusGradient g = fun x => c • TorusGradient f x from
        funext (gradient_affine f hf c b), norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      exact integral_const_mul _ _
    refine ⟨g, hg, hnorm, hvg, ?_⟩
    rw [henergy]
    have hcpos : 0 < c^2 := sq_pos_of_ne_zero (inv_ne_zero (Real.sqrt_pos.2 hvar).ne')
    have hh := mul_lt_mul_of_pos_left hstrict hcpos
    calc
      _ < c^2 * (r * variance f μ) := hh
      _ = r := by rw [mul_left_comm, hcoef, mul_one]

  have variance_three_square {d : ℕ} (ν : Measure (UnitAddTorus (Fin d)))
      [IsProbabilityMeasure ν] (f h F : UnitAddTorus (Fin d) → ℝ)
      (hf : Continuous f) (hh : Continuous h) (hF : Continuous F) (c : ℝ) :
      variance f ν ≤ 3 * ((∫ x, (f x - h x)^2 ∂ν) +
        (∫ x, (h x - F x)^2 ∂ν) + ∫ x, (F x - c)^2 ∂ν) := by
    have hsq (a b c : ℝ) : (a+b+c)^2 ≤ 3*(a^2+b^2+c^2) := by
      nlinarith [sq_nonneg (a-b), sq_nonneg (a-c), sq_nonneg (b-c)]
    have hi1 : Integrable (fun x => (f x - h x)^2) ν :=
      ((hf.sub hh).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hi2 : Integrable (fun x => (h x - F x)^2) ν :=
      ((hh.sub hF).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hi3 : Integrable (fun x => (F x - c)^2) ν :=
      ((hF.sub continuous_const).pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hfi : Integrable (fun x => (f x - c)^2) ν :=
      ((hf.sub continuous_const).pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hfm : MemLp f 2 ν := continuous_memLp f hf 2
    apply ((VarianceVariational ν f hfm c).2).trans
    have hbound := integral_mono hfi (((hi1.add hi2).add hi3).const_mul 3)
      (fun x => by
        dsimp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        convert! hsq (f x - h x) (h x - F x) (F x - c) using 1 <;> ring)
    change (∫ x, (f x - c)^2 ∂ν) ≤
      ∫ x, 3 * (((f x - h x)^2 + (h x - F x)^2) + (F x - c)^2) ∂ν at hbound
    have hadd12 : (∫ x, (f x - h x)^2 + (h x - F x)^2 ∂ν) =
        (∫ x, (f x - h x)^2 ∂ν) + ∫ x, (h x - F x)^2 ∂ν := by
      convert! integral_add hi1 hi2
    have hadd123 : (∫ x, ((f x - h x)^2 + (h x - F x)^2) + (F x - c)^2 ∂ν) =
        (∫ x, (f x - h x)^2 + (h x - F x)^2 ∂ν) + ∫ x, (F x - c)^2 ∂ν := by
      convert! integral_add (hi1.add hi2) hi3
    rwa [integral_const_mul, hadd123, hadd12] at hbound
  obtain ⟨p, C, hp, hC, hclipping⟩ := GroundStateClipping d hd L hL
  obtain ⟨t, R, ht, hR, htail⟩ := tail_parameters p C K hp hC hK
  let A1 : ℝ := R^2 * Real.exp K * K
  let A2 : ℝ := Real.exp K * (2 * R^2 * L)
  let T : ℝ := 1 + 48 * (A1 + A2)
  have hA1 : 0 ≤ A1 := by dsimp [A1]; positivity
  have hA2 : 0 ≤ A2 := by dsimp [A2]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  have hA1small : A1 / T ≤ 1 / 48 := by
    apply (div_le_iff₀ hT).mpr
    dsimp [T]
    linarith
  have hA2small : A2 / T ≤ 1 / 48 := by
    apply (div_le_iff₀ hT).mpr
    dsimp [T]
    linarith
  let D : ℝ := 2 * Real.exp K * Real.exp T
  have hD : 0 < D := by dsimp [D]; positivity
  let rate : ℝ := min 1 ((1 / 48) / D)
  have hr : 0 < rate := lt_min zero_lt_one (div_pos (by norm_num) hD)
  have hr1 : rate ≤ 1 := min_le_left _ _
  have hrD : D * rate ≤ 1 / 48 := by
    have h := (le_div_iff₀ hD).mp (min_le_right 1 ((1 / 48) / D))
    simpa only [mul_comm] using h
  refine ⟨rate, hr, ?_⟩
  intro V hV hpos hmean hLap f hf
  let ν := NormalizedTilt volume (fun x => Real.exp (-V x))
  obtain ⟨hZlower, hZupper, hden, _, hclip⟩ := hclipping K hK V hV hpos hmean hLap
  have hZ : 0 < ∫ x, Real.exp (-V x) := (Real.exp_pos (-K)).trans_le hZlower
  obtain ⟨hprob, htransfer⟩ := tilt_transfer V hV (Real.exp K) hZ hden
  haveI : IsProbabilityMeasure ν := hprob
  by_contra hfail
  have hstrict : (∫ x, ‖TorusGradient f x‖^2 ∂ν) < rate * variance f ν := by
    have h := mul_lt_mul_of_pos_left (lt_of_not_ge hfail) hr
    simpa only [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] using h
  obtain ⟨g, hg, hgnorm, hgvar, hgenergy⟩ := normalized_violator ν f hf rate hr hstrict
  have hge1 : (∫ x, ‖TorusGradient g x‖^2 ∂ν) ≤ 1 := hgenergy.le.trans hr1
  let h : UnitAddTorus (Fin d) → ℝ := fun x => max (-R) (min (g x) R)
  let χ : UnitAddTorus (Fin d) → ℝ := fun x => max (1 - V x / T) 0
  let F : UnitAddTorus (Fin d) → ℝ := fun x => χ x * h x
  let W : UnitAddTorus (Fin d) → EuclideanSpace ℝ (Fin d) := fun x =>
    χ x • (if |g x| < R then TorusGradient g x else 0) -
      (h x / T) • (if V x < T then TorusGradient V x else 0)
  have herrclip : (∫ x, (g x - h x)^2 ∂ν) ≤ 1 / 12 :=
    ((hclip g hg hgnorm hge1 t R ht hR).2).trans htail
  have happ := ClipCutoffApproximation d V g hV hg K L R T hK hL hR hT hpos hmean hLap
  change MemLp F 2 volume ∧ MemLp W 2 volume ∧
    (∃ u : ℕ → UnitAddTorus (Fin d) → ℝ,
      (∀ n, TorusSmooth (u n)) ∧
      Filter.Tendsto (fun n => ∫ x, (u n x - F x)^2) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun n => ∫ x, ‖TorusGradient (u n) x - W x‖^2)
        Filter.atTop (nhds 0)) ∧
    (∫ x, (h x - F x)^2 ∂ν) ≤ A1 / T ∧
    (∫ x, ‖W x‖^2) ≤ 2 * Real.exp T *
      (∫ x, ‖TorusGradient g x‖^2 ∂ν) + 2 * R^2 * L / T at happ
  obtain ⟨hFm, hWm, ⟨u, hus, hconv, hconvW⟩, herrcut, hWbound⟩ := happ
  let c : ℝ := ∫ x, F x
  have hhaar : (∫ x, (F x - c)^2) ≤ ∫ x, ‖W x‖^2 :=
    (TorusHaarPoincare d hd).2 F W u hFm hWm hus hconv hconvW
  have hgc : Continuous g := (TorusFourierLaplacian d g hg).1
  have hVc : Continuous V := (TorusFourierLaplacian d V hV).1
  have hhc : Continuous h := continuous_const.max (hgc.min continuous_const)
  have hχc : Continuous χ := (continuous_const.sub (hVc.div_const T)).max continuous_const
  have hFc : Continuous F := hχc.mul hhc
  have hnuF : (∫ x, (F x - c)^2 ∂ν) ≤
      Real.exp K * (2 * Real.exp T * (∫ x, ‖TorusGradient g x‖^2 ∂ν) + 2 * R^2 * L / T) := by
    apply (htransfer (fun x => (F x - c)^2) ((hFc.sub continuous_const).pow 2)
      (fun x => sq_nonneg _)).trans
    exact (mul_le_mul_of_nonneg_left hhaar (Real.exp_pos K).le).trans
      (mul_le_mul_of_nonneg_left hWbound (Real.exp_pos K).le)
  have hsmallF : (∫ x, (F x - c)^2 ∂ν) ≤ 1 / 12 := by
    apply hnuF.trans
    calc
      _ = D * (∫ x, ‖TorusGradient g x‖^2 ∂ν) + A2 / T := by dsimp [D, A2]; ring
      _ ≤ 1 / 48 + 1 / 48 := add_le_add
        ((mul_le_mul_of_nonneg_left hgenergy.le hD.le).trans hrD) hA2small
      _ ≤ 1 / 12 := by norm_num
  have hthree := variance_three_square ν g h F hgc hhc hFc c
  rw [hgvar] at hthree
  have hcut12 : (∫ x, (h x - F x)^2 ∂ν) ≤ 1 / 12 :=
    herrcut.trans (hA1small.trans (by norm_num))
  linarith
