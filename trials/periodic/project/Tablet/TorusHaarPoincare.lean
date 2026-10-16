import Tablet.TorusGradient
import Tablet.TorusSmooth
import Tablet.TorusFourierLaplacian
import Mathlib.Topology.Constructions
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Tablet.TorusIntegrationByParts
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.Real.Pi.Bounds
open MeasureTheory
open scoped ComplexConjugate ContDiff
-- [TABLET NODE: TorusHaarPoincare]
theorem TorusHaarPoincare (d : ℕ) (hd : 0 < d) :
    (∀ f : UnitAddTorus (Fin d) → ℝ, TorusSmooth f →
      (∫ x, (f x - ∫ y, f y)^2) ≤ ∫ x, ‖TorusGradient f x‖^2) ∧
    (∀ (F : UnitAddTorus (Fin d) → ℝ)
      (W : UnitAddTorus (Fin d) → EuclideanSpace ℝ (Fin d))
      (u : ℕ → UnitAddTorus (Fin d) → ℝ),
      MeasureTheory.MemLp F 2 MeasureTheory.volume →
      MeasureTheory.MemLp W 2 MeasureTheory.volume →
      (∀ n, TorusSmooth (u n)) →
      Filter.Tendsto (fun n => ∫ x, (u n x - F x)^2) Filter.atTop (nhds 0) →
      Filter.Tendsto (fun n => ∫ x, ‖TorusGradient (u n) x - W x‖^2)
        Filter.atTop (nhds 0) →
      (∫ x, (F x - ∫ y, F y)^2) ≤ ∫ x, ‖W x‖^2) := by
-- BODY
  classical
  
  have norm_sq {α E : Type} [MeasurableSpace α] [NormedAddCommGroup E]
      [InnerProductSpace ℝ E] {μ : Measure α} (f : α → E) (hf : MemLp f 2 μ) :
      ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    simp [hx, real_inner_self_eq_norm_sq]
  
  have toLp_tendsto {α E : Type} [MeasurableSpace α] [NormedAddCommGroup E]
      [InnerProductSpace ℝ E] {μ : Measure α}
      (u : ℕ → α → E) (F : α → E) (hu : ∀ n, MemLp (u n) 2 μ) (hF : MemLp F 2 μ)
      (he : Filter.Tendsto (fun n => ∫ x, ‖u n x - F x‖ ^ 2 ∂μ)
        Filter.atTop (nhds 0)) :
      Filter.Tendsto (fun n => (hu n).toLp (u n)) Filter.atTop (nhds (hF.toLp F)) := by
    have heq (n : ℕ) : ‖(hu n).toLp (u n) - hF.toLp F‖^2 =
        ∫ x, ‖u n x - F x‖^2 ∂μ := by
      rw [← MemLp.toLp_sub]
      exact norm_sq _ _
    have hsq : Filter.Tendsto (fun n => ‖(hu n).toLp (u n) - hF.toLp F‖^2)
        Filter.atTop (nhds 0) := he.congr' (Filter.Eventually.of_forall fun n => (heq n).symm)
    have hn := (Real.continuous_sqrt.tendsto 0).comp hsq
    simp only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] at hn
    exact tendsto_iff_norm_sub_tendsto_zero.mpr hn
  
  have inner_const {α : Type} [MeasurableSpace α] {μ : Measure α}
      [IsProbabilityMeasure μ] (f : α → ℝ) (hf : MemLp f 2 μ) :
      inner ℝ ((memLp_const (1 : ℝ) (μ := μ) (p := 2)).toLp (fun _ : α => (1 : ℝ))) (hf.toLp f) = ∫ x, f x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(memLp_const (1 : ℝ) (μ := μ) (p := 2)).coeFn_toLp,
      hf.coeFn_toLp] with x h1 hf
    simp [h1, hf]
  
  have centered_norm_sq {α : Type} [MeasurableSpace α] {μ : Measure α}
      [IsProbabilityMeasure μ] (f : α → ℝ) (hf : MemLp f 2 μ) :
      ‖hf.toLp f - (inner ℝ ((memLp_const (1 : ℝ) (μ := μ) (p := 2)).toLp (fun _ : α => (1 : ℝ)))
        (hf.toLp f)) • ((memLp_const (1 : ℝ) (μ := μ) (p := 2)).toLp (fun _ : α => (1 : ℝ)))‖^2 =
        ∫ x, (f x - ∫ y, f y ∂μ)^2 ∂μ := by
    rw [inner_const]
    have he : (memLp_const (∫ y, f y ∂μ) (μ := μ) (p := 2)).toLp (fun _ : α => ∫ y, f y ∂μ) =
        (∫ y, f y ∂μ) • ((memLp_const (1 : ℝ) (μ := μ) (p := 2)).toLp (fun _ : α => (1 : ℝ))) := by
      apply Lp.ext
      filter_upwards [(memLp_const (∫ y, f y ∂μ) (μ := μ) (p := 2)).coeFn_toLp,
        Lp.coeFn_smul (∫ y, f y ∂μ) ((memLp_const (1 : ℝ) (μ := μ) (p := 2)).toLp (fun _ : α => (1 : ℝ))),
        (memLp_const (1 : ℝ) (μ := μ) (p := 2)).coeFn_toLp] with x hm hs h1
      rw [hm, hs]
      simp only [Pi.smul_apply, smul_eq_mul, h1, mul_one]
    rw [← he, ← MemLp.toLp_sub, norm_sq]
    simp [Real.norm_eq_abs, sq_abs]
  
  
  have quotient (d : ℕ) : IsOpenQuotientMap (TorusLift d) := by
    have hc : IsOpenQuotientMap ((↑) : ℝ → AddCircle (1 : ℝ)) :=
      QuotientAddGroup.isOpenQuotientMap_mk
    have hp : IsOpenQuotientMap
        (Pi.map (fun _ : Fin d => ((↑) : ℝ → AddCircle (1 : ℝ)))) :=
      IsOpenQuotientMap.piMap (fun _ => hc)
    exact hp.comp (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isOpenQuotientMap
  
  have continuous {d : ℕ} {f : UnitAddTorus (Fin d) → ℝ}
      (hf : TorusSmooth f) : Continuous f := by
    apply (quotient d).continuous_comp_iff.mp
    exact hf.continuous
  
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
  
  have gradient_smooth {d : ℕ} {f : UnitAddTorus (Fin d) → ℝ}
      (hf : TorusSmooth f) (j : Fin d) : TorusSmooth (fun x => TorusGradient f x j) := by
    change ContDiff ℝ ∞ (fun y => TorusGradient f (TorusLift d y) j)
    simp_rw [gradient_on_lift]
    exact (hf.fderiv_right (by simp)).clm_apply contDiff_const
  
  
  have volume_eq_haar (d : ℕ) :
      (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d))) =
        MeasureTheory.Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle (T := (1 : ℝ))) := by
    change MeasureTheory.Measure.pi (fun _ : Fin d =>
      (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ)))) = _
    congr 1
    funext j
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
  
  have square_sum {d : ℕ} (f : UnitAddTorus (Fin d) → ℝ) (hf : TorusSmooth f) :
      HasSum (fun k : Fin d → ℤ => ‖UnitAddTorus.mFourierCoeff (fun x => (f x : ℂ)) k‖ ^ 2)
        (∫ x, (f x) ^ 2) := by
    let cf : C(UnitAddTorus (Fin d), ℂ) :=
      ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp (TorusFourierLaplacian d f hf).1⟩
    let μ := MeasureTheory.Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle (T := (1 : ℝ)))
    have hs := UnitAddTorus.hasSum_sq_mFourierCoeff (d := Fin d) (cf.toLp 2 μ ℂ)
    have hcoeff (k : Fin d → ℤ) : UnitAddTorus.mFourierCoeff (cf.toLp 2 μ ℂ) k =
        UnitAddTorus.mFourierCoeff (fun x => (f x : ℂ)) k :=
      UnitAddTorus.mFourierCoeff_toLp cf k
    simp_rw [hcoeff] at hs
    change HasSum (fun k => ‖UnitAddTorus.mFourierCoeff (fun x => (f x : ℂ)) k‖ ^ 2)
      (∫ x, ‖cf.toLp 2 μ ℂ x‖ ^ 2 ∂μ) at hs
    have hi : (∫ x, ‖cf.toLp 2 μ ℂ x‖ ^ 2 ∂μ) = ∫ x, f x ^ 2 ∂μ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [cf.coeFn_toLp (p := 2) (μ := μ) (𝕜 := ℂ)] with x hx
      rw [hx]
      simp [cf, Real.norm_eq_abs, sq_abs]
    rw [hi] at hs
    rw [volume_eq_haar]
    exact hs
  
  have energy_sum {d : ℕ} (f : UnitAddTorus (Fin d) → ℝ) (hf : TorusSmooth f) :
      HasSum (fun k : Fin d → ℤ =>
        (4 * Real.pi ^ 2 * ∑ j, (k j : ℝ) ^ 2) *
          ‖UnitAddTorus.mFourierCoeff (fun x => (f x : ℂ)) k‖ ^ 2)
        (∫ x, ‖TorusGradient f x‖ ^ 2) := by
    have hlf := (TorusFourierLaplacian d f hf).2.1
    let cf : C(UnitAddTorus (Fin d), ℂ) :=
      ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp (TorusFourierLaplacian d f hf).1⟩
    let cg : C(UnitAddTorus (Fin d), ℂ) :=
      ⟨fun x => (-(TorusLaplacian f x) : ℝ),
        Complex.continuous_ofReal.comp ((TorusFourierLaplacian d _ hlf).1.neg)⟩
    let μ := MeasureTheory.Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle (T := (1 : ℝ)))
    have hcf (k : Fin d → ℤ) : UnitAddTorus.mFourierCoeff (cf.toLp 2 μ ℂ) k =
        UnitAddTorus.mFourierCoeff (fun x => (f x : ℂ)) k :=
      UnitAddTorus.mFourierCoeff_toLp cf k
    have hcg (k : Fin d → ℤ) : UnitAddTorus.mFourierCoeff (cg.toLp 2 μ ℂ) k =
        ((4 * Real.pi ^ 2 * ∑ j, (k j : ℝ) ^ 2 : ℝ) : ℂ) *
          UnitAddTorus.mFourierCoeff (fun x => (f x : ℂ)) k := by
      rw [show UnitAddTorus.mFourierCoeff (cg.toLp 2 μ ℂ) k =
        UnitAddTorus.mFourierCoeff cg k from UnitAddTorus.mFourierCoeff_toLp cg k]
      have he := (TorusFourierLaplacian d f hf).2.2.2 (-k)
      simp only [Pi.neg_apply, Int.cast_neg, neg_sq] at he
      rw [volume_eq_haar] at he
      change (∫ x, (TorusLaplacian f x : ℂ) * UnitAddTorus.mFourier (-k) x ∂μ) =
        ((-(4 * Real.pi ^ 2 * ∑ j, (k j : ℝ) ^ 2) : ℝ) : ℂ) *
          (∫ x, (f x : ℂ) * UnitAddTorus.mFourier (-k) x ∂μ) at he
      unfold UnitAddTorus.mFourierCoeff
      change (∫ x, UnitAddTorus.mFourier (-k) x • ((-(TorusLaplacian f x) : ℝ) : ℂ) ∂μ) = _
      simp only [smul_eq_mul, Complex.ofReal_neg, mul_neg, MeasureTheory.integral_neg]
      simp_rw [mul_comm (UnitAddTorus.mFourier (-k) _)]
      rw [he]
      simp only [Complex.ofReal_neg, neg_mul, neg_neg]
      rfl
    have hs := UnitAddTorus.hasSum_prod_mFourierCoeff (d := Fin d)
      (cf.toLp 2 μ ℂ) (cg.toLp 2 μ ℂ)
    simp_rw [hcf, hcg] at hs
    change HasSum _ (∫ x, conj (cf.toLp 2 μ ℂ x) * cg.toLp 2 μ ℂ x ∂μ) at hs
    have hi : (∫ x, conj (cf.toLp 2 μ ℂ x) * cg.toLp 2 μ ℂ x ∂μ) =
        ((∫ x, (f x * (-TorusLaplacian f x) : ℝ) ∂μ : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [cf.coeFn_toLp (p := 2) (μ := μ) (𝕜 := ℂ),
        cg.coeFn_toLp (p := 2) (μ := μ) (𝕜 := ℂ)] with x hfx hgx
      rw [hfx, hgx]
      simp [cf, cg]
    rw [hi] at hs
    have hr := RCLike.hasSum_re ℂ hs
    simp only [RCLike.re_eq_complex_re, Complex.ofReal_re] at hr
    have hterm (k : Fin d → ℤ) :
        (conj (UnitAddTorus.mFourierCoeff (fun x => (f x : ℂ)) k) *
          (((4 * Real.pi ^ 2 * ∑ j, (k j : ℝ) ^ 2 : ℝ) : ℂ) *
            UnitAddTorus.mFourierCoeff (fun x => (f x : ℂ)) k)).re =
        (4 * Real.pi ^ 2 * ∑ j, (k j : ℝ) ^ 2) *
          ‖UnitAddTorus.mFourierCoeff (fun x => (f x : ℂ)) k‖ ^ 2 := by
      rw [mul_left_comm, Complex.conj_mul']
      simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
    simp_rw [hterm] at hr
    have henergy : (∫ x, f x * (-TorusLaplacian f x) ∂μ) = ∫ x, ‖TorusGradient f x‖ ^ 2 := by
      change (∫ x, f x * (-TorusLaplacian f x)
        ∂MeasureTheory.Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle (T := (1 : ℝ)))) = _
      rw [← volume_eq_haar]
      simp_rw [mul_neg]
      rw [MeasureTheory.integral_neg, TorusIntegrationByParts d f f hf hf, neg_neg]
      congr 1
      funext x
      rw [EuclideanSpace.norm_sq_eq]
      apply Finset.sum_congr rfl
      intro j _
      simp [Real.norm_eq_abs, sq_abs, pow_two]
    rw [henergy] at hr
    exact hr
  
  have smooth_poincare {d : ℕ} (f : UnitAddTorus (Fin d) → ℝ) (hf : TorusSmooth f) :
      (∫ x, (f x - ∫ y, f y)^2) ≤ ∫ x, ‖TorusGradient f x‖^2 := by
    have : MeasureTheory.IsProbabilityMeasure
        (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d))) := by
      rw [volume_eq_haar]
      infer_instance
    let b : ℝ := ∫ x, f x
    let g : UnitAddTorus (Fin d) → ℝ := fun x => f x - b
    have hg : TorusSmooth g := hf.sub contDiff_const
    have hmean : (∫ x, g x) = 0 := by
      rw [MeasureTheory.integral_sub
        ((TorusFourierLaplacian d f hf).1.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)) (MeasureTheory.integrable_const b)]
      simp [b]
    have hzero : UnitAddTorus.mFourierCoeff (fun x => (g x : ℂ)) (0 : Fin d → ℤ) = 0 := by
      unfold UnitAddTorus.mFourierCoeff
      simp only [neg_zero, UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, one_smul]
      change (∫ t, (g t : ℂ) ∂MeasureTheory.Measure.pi
        (fun _ : Fin d => AddCircle.haarAddCircle (T := (1 : ℝ)))) = 0
      rw [← volume_eq_haar, integral_complex_ofReal, hmean]
      simp
    have hweight (k : Fin d → ℤ) :
        ‖UnitAddTorus.mFourierCoeff (fun x => (g x : ℂ)) k‖^2 ≤
        (4 * Real.pi ^ 2 * ∑ j, (k j : ℝ)^2) *
          ‖UnitAddTorus.mFourierCoeff (fun x => (g x : ℂ)) k‖^2 := by
      by_cases hk : k = 0
      · simp [hk, hzero]
      · obtain ⟨j, hj⟩ := Function.ne_iff.mp hk
        have hj' : k j ≠ 0 := by simpa using hj
        have hsq : (1 : ℝ) ≤ (k j : ℝ)^2 := by
          exact_mod_cast (one_le_sq_iff_one_le_abs _).mpr (Int.one_le_abs hj')
        have hsum : (1 : ℝ) ≤ ∑ j, (k j : ℝ)^2 := hsq.trans
          (Finset.single_le_sum (fun i _ => sq_nonneg (k i : ℝ)) (Finset.mem_univ j))
        have hfactor : (1 : ℝ) ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
        have hLambda : (1 : ℝ) ≤ 4 * Real.pi ^ 2 * ∑ j, (k j : ℝ)^2 :=
          hfactor.trans (le_mul_of_one_le_right (by positivity) hsum)
        exact le_mul_of_one_le_left (sq_nonneg _) hLambda
    have hineq := hasSum_le hweight (square_sum g hg) (energy_sum g hg)
    have hgrad : TorusGradient g = TorusGradient f := by
      funext x
      unfold TorusGradient
      simp [g, fderiv_sub_const]
    simpa only [g, b, hgrad] using hineq
  
  
  have continuous_memLp {α E : Type} [MeasurableSpace α] [TopologicalSpace α]
      [BorelSpace α] [CompactSpace α] [Nonempty α] [NormedAddCommGroup E]
      [SecondCountableTopologyEither α E] {μ : Measure α} [IsFiniteMeasure μ]
      (f : α → E) (hf : Continuous f) : MemLp f 2 μ := by
    rcases isCompact_univ.exists_isMaxOn Set.univ_nonempty hf.norm.continuousOn
      with ⟨x0, _, hmax⟩
    exact MemLp.of_bound hf.aestronglyMeasurable ‖f x0‖
      (Filter.Eventually.of_forall fun x => hmax (Set.mem_univ x))
  
  have gradient_continuous {d : ℕ} {f : UnitAddTorus (Fin d) → ℝ}
      (hf : TorusSmooth f) : Continuous (TorusGradient f) := by
    change Continuous (fun x => WithLp.toLp 2 (fun j => TorusGradient f x j))
    apply (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp
    apply continuous_pi
    intro j
    exact continuous (gradient_smooth hf j)
  
  have full (d : ℕ) (hd : 0 < d) :
      (∀ f : UnitAddTorus (Fin d) → ℝ, TorusSmooth f →
        (∫ x, (f x - ∫ y, f y)^2) ≤ ∫ x, ‖TorusGradient f x‖^2) ∧
      (∀ (F : UnitAddTorus (Fin d) → ℝ)
        (W : UnitAddTorus (Fin d) → EuclideanSpace ℝ (Fin d))
        (u : ℕ → UnitAddTorus (Fin d) → ℝ),
        MeasureTheory.MemLp F 2 MeasureTheory.volume →
        MeasureTheory.MemLp W 2 MeasureTheory.volume →
        (∀ n, TorusSmooth (u n)) →
        Filter.Tendsto (fun n => ∫ x, (u n x - F x)^2) Filter.atTop (nhds 0) →
        Filter.Tendsto (fun n => ∫ x, ‖TorusGradient (u n) x - W x‖^2)
          Filter.atTop (nhds 0) →
        (∫ x, (F x - ∫ y, F y)^2) ≤ ∫ x, ‖W x‖^2) := by
    have : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := by
      rw [volume_eq_haar]
      infer_instance
    refine ⟨fun f hf => smooth_poincare f hf, ?_⟩
    intro F W u hF hW hu hconv hconvW
    have hum (n : ℕ) : MemLp (u n) 2 volume := continuous_memLp _
      (TorusFourierLaplacian d _ (hu n)).1
    have hug (n : ℕ) : MemLp (TorusGradient (u n)) 2 volume :=
      continuous_memLp _ (gradient_continuous (hu n))
    have hut : Filter.Tendsto (fun n => (hum n).toLp (u n)) Filter.atTop (nhds (hF.toLp F)) :=
      toLp_tendsto u F hum hF (by simpa [Real.norm_eq_abs, sq_abs] using hconv)
    have hwt : Filter.Tendsto (fun n => (hug n).toLp (TorusGradient (u n)))
        Filter.atTop (nhds (hW.toLp W)) :=
      toLp_tendsto _ _ hug hW hconvW
    let one : Lp ℝ 2 (volume : Measure (UnitAddTorus (Fin d))) :=
      (memLp_const (1 : ℝ)).toLp (fun _ => (1 : ℝ))
    let center : Lp ℝ 2 (volume : Measure (UnitAddTorus (Fin d))) →
        Lp ℝ 2 (volume : Measure (UnitAddTorus (Fin d))) :=
      fun v => v - (inner ℝ one v) • one
    have hc : Continuous center := by
      unfold center
      fun_prop
    have hvar := (continuous_norm.pow 2).tendsto (center (hF.toLp F)) |>.comp
      ((hc.tendsto (hF.toLp F)).comp hut)
    have hen := (continuous_norm.pow 2).tendsto (hW.toLp W) |>.comp hwt
    have hvar' : Filter.Tendsto (fun n => ∫ x, (u n x - ∫ y, u n y)^2)
        Filter.atTop (nhds (∫ x, (F x - ∫ y, F y)^2)) := by
      simpa only [Function.comp_def, Pi.pow_apply, center, one,
        centered_norm_sq] using hvar
    have hen' : Filter.Tendsto (fun n => ∫ x, ‖TorusGradient (u n) x‖^2)
        Filter.atTop (nhds (∫ x, ‖W x‖^2)) := by
      simpa only [Function.comp_def, Pi.pow_apply, norm_sq] using hen
    exact le_of_tendsto_of_tendsto hvar' hen'
      (Filter.Eventually.of_forall fun n => smooth_poincare _ (hu n))
  exact full d hd
