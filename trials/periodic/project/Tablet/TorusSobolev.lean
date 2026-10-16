module

public import Tablet.TorusGradient
public import Tablet.TorusSmooth
public import Tablet.TorusFourierLaplacian
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
public import Mathlib.Tactic

@[expose] public section
open MeasureTheory Set Function Finset
open scoped ContDiff ENNReal NNReal
-- [TABLET NODE: TorusSobolev]
theorem TorusSobolev (d : ℕ) (hd : 0 < d) :
    let p : ℝ := if d ≤ 2 then 4 else 2 * (d : ℝ) / ((d : ℝ) - 2)
    2 < p ∧ ∃ C : ℝ, 0 < C ∧
      ∀ f : UnitAddTorus (Fin d) → ℝ, TorusSmooth f →
        Real.rpow (∫ x, Real.rpow |f x| p) (2 / p) ≤
          C * ((∫ x, f x^2) + ∫ x, ‖TorusGradient f x‖^2) := by
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

  have lift_add {d : ℕ} (y z : EuclideanSpace ℝ (Fin d)) :
      TorusLift d (y + z) = TorusLift d y + TorusLift d z := by
    ext j
    simp [TorusLift]

  have averaged_ftc {F G : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
      (hG : Continuous G) (hG0 : ∀ t, 0 ≤ G t)
      (hFG : ∀ t, ‖deriv F t‖ ≤ G t) :
      ‖F 0‖ ≤ (∫ t in (0 : ℝ)..1, ‖F t‖) + ∫ t in (0 : ℝ)..1, G t := by
    have hpoint : ∀ t ∈ Icc (0 : ℝ) 1,
        ‖F 0‖ ≤ ‖F t‖ + ∫ s in (0 : ℝ)..1, G s := by
      intro t ht
      have hsub := norm_sub_le_integral_of_norm_deriv_le_of_le ht.1
        hF.continuous.continuousOn (hF.differentiable one_ne_zero).differentiableOn
        (Filter.Eventually.of_forall fun s _ => hFG s) (hG.intervalIntegrable 0 t)
      have hmono := intervalIntegral.integral_mono_interval (μ := volume) (le_refl (0 : ℝ))
        ht.1 ht.2 (Filter.Eventually.of_forall fun s => hG0 s)
        (hG.intervalIntegrable 0 1)
      have htri : ‖F 0‖ ≤ ‖F t‖ + ‖F t - F 0‖ := by
        simpa only [norm_sub_rev] using norm_le_insert (F t) (F 0)
      exact htri.trans (add_le_add_right (hsub.trans hmono) _)
    have hi := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => ‖F 0‖) volume 0 1)
      ((hF.continuous.norm.add continuous_const).intervalIntegrable 0 1) hpoint
    change (∫ t in (0 : ℝ)..1, ‖F 0‖) ≤
      ∫ t in (0 : ℝ)..1, ‖F t‖ + (∫ s in (0 : ℝ)..1, G s) at hi
    simpa only [intervalIntegral.integral_add (hF.continuous.norm.intervalIntegrable 0 1)
        intervalIntegrable_const, intervalIntegral.integral_const, sub_zero, one_smul] using hi

  have grid_bound {ι : Type} [Fintype ι] [DecidableEq ι]
      {A : ι → Type} [∀ i, MeasurableSpace (A i)]
      (μ : ∀ i, Measure (A i)) [∀ i, SigmaFinite (μ i)]
      {p : ℝ} (hp : Real.HolderConjugate (Fintype.card ι) p)
      {u g : (∀ i, A i) → ℝ≥0∞} (hg : Measurable g)
      (hline : ∀ x i, u x ≤ ∫⁻ t, g (update x i t) ∂μ i) :
      ∫⁻ x, u x ^ p ∂Measure.pi μ ≤ (∫⁻ x, g x ∂Measure.pi μ) ^ p := by
    have hpos : 0 < (Fintype.card ι : ℝ) - 1 := by linarith [hp.lt]
    calc
      ∫⁻ x, u x ^ p ∂Measure.pi μ =
          ∫⁻ x, (u x ^ (1 / (Fintype.card ι - 1 : ℝ))) ^
            (Fintype.card ι : ℝ) ∂Measure.pi μ := by
        congr! 2 with x
        rw [← ENNReal.rpow_mul, hp.conjugate_eq]
        congr 1
        field_simp
      _ = ∫⁻ x, ∏ _i : ι, u x ^ (1 / (Fintype.card ι - 1 : ℝ)) ∂Measure.pi μ := by
        congr! 2 with x
        simp_rw [prod_const]
        norm_cast
      _ ≤ ∫⁻ x, ∏ i, (∫⁻ t, g (update x i t) ∂μ i) ^
            (1 / (Fintype.card ι - 1 : ℝ)) ∂Measure.pi μ := by
        gcongr with x i
        exact hline x i
      _ ≤ (∫⁻ x, g x ∂Measure.pi μ) ^ p :=
        lintegral_prod_lintegral_pow_le μ hp hg

  have continuous_c1 {d : ℕ} {w : UnitAddTorus (Fin d) → ℝ}
      (hw : ContDiff ℝ 1 (fun y => w (TorusLift d y))) : Continuous w :=
    (quotient d).continuous_comp_iff.mp hw.continuous

  have component_continuous_c1 {d : ℕ} {w : UnitAddTorus (Fin d) → ℝ}
      (hw : ContDiff ℝ 1 (fun y => w (TorusLift d y))) (j : Fin d) :
      Continuous (fun x => TorusGradient w x j) := by
    apply (quotient d).continuous_comp_iff.mp
    simp_rw [Function.comp_def, gradient_on_lift]
    exact (hw.continuous_fderiv (by norm_num)).clm_apply continuous_const

  have slice_hasDeriv_c1 {d : ℕ} {w : UnitAddTorus (Fin d) → ℝ}
      (hw : ContDiff ℝ 1 (fun y => w (TorusLift d y)))
      (y : EuclideanSpace ℝ (Fin d)) (j : Fin d) (t : ℝ) :
      HasDerivAt (fun t => w (TorusLift d (y + t • EuclideanSpace.single j 1)))
        (TorusGradient w (TorusLift d (y + t • EuclideanSpace.single j 1)) j) t := by
    rw [gradient_on_lift]
    have hs : HasDerivAt (fun t : ℝ => y + t • EuclideanSpace.single j 1)
        (EuclideanSpace.single j 1) t := by
      convert! (show HasDerivAt _ _ t from
        (hasDerivAt_const t y).add ((hasDerivAt_id t).smul_const
        (EuclideanSpace.single j (1 : ℝ)))) using 1 <;> simp
    exact (hw.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t hs

  have add_single_update {d : ℕ} (x : UnitAddTorus (Fin d)) (j : Fin d) (t : ℝ) :
      x + TorusLift d (t • EuclideanSpace.single j 1) =
        update x j (x j + (t : AddCircle (1 : ℝ))) := by
    ext k
    by_cases h : j = k
    · subst k
      simp [TorusLift]
    · simp [TorusLift, h, Ne.symm h]

  have fiber_bound {d : ℕ} {w : UnitAddTorus (Fin d) → ℝ}
      (hw : ContDiff ℝ 1 (fun y => w (TorusLift d y)))
      (x : UnitAddTorus (Fin d)) (j : Fin d) :
      ‖w x‖ ≤ (∫ t : AddCircle (1 : ℝ), ‖w (update x j t)‖) +
        ∫ t : AddCircle (1 : ℝ), ‖TorusGradient w (update x j t) j‖ := by
    obtain ⟨y, rfl⟩ := (quotient d).surjective x
    let F : ℝ → ℝ := fun t => w (TorusLift d (y + t • EuclideanSpace.single j 1))
    let D : ℝ → ℝ := fun t =>
      TorusGradient w (TorusLift d (y + t • EuclideanSpace.single j 1)) j
    have hF : ContDiff ℝ 1 F := hw.comp (contDiff_const.add
      (contDiff_id.smul contDiff_const))
    have hD : Continuous D := (component_continuous_c1 hw j).comp
      ((quotient d).continuous.comp
        (continuous_const.add (continuous_id.smul continuous_const)))
    have hderiv : ∀ t, deriv F t = D t := fun t => (slice_hasDeriv_c1 hw y j t).deriv
    have h := averaged_ftc hF hD.norm (fun t => norm_nonneg (D t))
      (fun t => by rw [hderiv])
    have hcircle (H : UnitAddTorus (Fin d) → ℝ) :
        (∫ t in (0 : ℝ)..1, H (TorusLift d (y + t • EuclideanSpace.single j 1))) =
          ∫ t : AddCircle (1 : ℝ), H (update (TorusLift d y) j t) := by
      simp_rw [lift_add, add_single_update]
      have hm := UnitAddCircle.intervalIntegral_preimage (E := ℝ) 0
        (fun t => H (update (TorusLift d y) j (TorusLift d y j + t)))
      simp only [zero_add] at hm
      rw [hm]
      exact integral_add_left_eq_self (fun t => H (update (TorusLift d y) j t))
        (TorusLift d y j)
    change ‖w (TorusLift d (y + (0 : ℝ) • EuclideanSpace.single j 1))‖ ≤
      (∫ t in (0 : ℝ)..1, ‖w (TorusLift d (y + t • EuclideanSpace.single j 1))‖) +
      ∫ t in (0 : ℝ)..1, ‖TorusGradient w (TorusLift d
        (y + t • EuclideanSpace.single j 1)) j‖ at h
    rw [hcircle (fun z => ‖w z‖), hcircle (fun z => ‖TorusGradient w z j‖)] at h
    simpa only [zero_smul, add_zero] using h

  have w11_bound {d : ℕ} {w : UnitAddTorus (Fin d) → ℝ}
      (hw : ContDiff ℝ 1 (fun y => w (TorusLift d y)))
      {p : ℝ} (hp : Real.HolderConjugate (d : ℝ) p) :
      ∫⁻ x, ‖w x‖ₑ ^ p ≤ ENNReal.ofReal
        ((∫ x, ‖w x‖) + ∑ j : Fin d, ∫ x, ‖TorusGradient w x j‖) ^ p := by
    classical
    let g : UnitAddTorus (Fin d) → ℝ := fun x =>
      ‖w x‖ + ∑ j : Fin d, ‖TorusGradient w x j‖
    have hg : Continuous g := (continuous_c1 hw).norm.add
      (continuous_finset_sum _ fun j _ => (component_continuous_c1 hw j).norm)
    have hg0 : ∀ x, 0 ≤ g x := fun x => add_nonneg (norm_nonneg _)
      (Finset.sum_nonneg fun j _ => norm_nonneg _)
    have hgi : Integrable g volume :=
      hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
    have hline : ∀ x j, ‖w x‖ₑ ≤ ∫⁻ t : AddCircle (1 : ℝ),
        ENNReal.ofReal (g (update x j t)) := by
      intro x j
      have huc : Continuous (fun t : AddCircle (1 : ℝ) => update x j t) := by fun_prop
      have hwi : Integrable (fun t => ‖w (update x j t)‖) volume :=
        ((continuous_c1 hw).comp huc).norm.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      have hDi : Integrable (fun t => ‖TorusGradient w (update x j t) j‖) volume :=
        ((component_continuous_c1 hw j).comp huc).norm.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      have hgf : Integrable (fun t => g (update x j t)) volume :=
        (hg.comp huc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      rw [← ofReal_integral_eq_lintegral_ofReal hgf
        (Filter.Eventually.of_forall fun t => hg0 (update x j t))]
      rw [← ofReal_norm]
      apply ENNReal.ofReal_le_ofReal
      apply (fiber_bound hw x j).trans
      rw [← integral_add hwi hDi]
      apply integral_mono (hwi.add hDi) hgf
      intro t
      exact add_le_add_right (Finset.single_le_sum (fun k _ => norm_nonneg _)
        (Finset.mem_univ j)) _
    have h := grid_bound (fun _ : Fin d => (volume : Measure (AddCircle (1 : ℝ))))
      (by simpa using hp) (hg.measurable.ennreal_ofReal) hline
    have hint : (∫ x, g x) = (∫ x, ‖w x‖) +
        ∑ j : Fin d, ∫ x, ‖TorusGradient w x j‖ := by
      unfold g
      rw [integral_add, integral_finset_sum]
      · intro j _
        exact (component_continuous_c1 hw j).norm.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · exact (continuous_c1 hw).norm.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · apply integrable_finset_sum
        intro j _
        exact (component_continuous_c1 hw j).norm.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
    change (∫⁻ x, ‖w x‖ₑ ^ p) ≤ (∫⁻ x, ENNReal.ofReal (g x)) ^ p at h
    rwa [← ofReal_integral_eq_lintegral_ofReal hgi
      (Filter.Eventually.of_forall hg0), hint] at h

  have continuous_memLp {α E : Type} [MeasurableSpace α] [TopologicalSpace α]
      [BorelSpace α] [CompactSpace α] [Nonempty α] [NormedAddCommGroup E]
      [SecondCountableTopologyEither α E] {μ : Measure α} [IsFiniteMeasure μ]
      (f : α → E) (hf : Continuous f) (p : ℝ≥0∞) : MemLp f p μ := by
    rcases isCompact_univ.exists_isMaxOn Set.univ_nonempty hf.norm.continuousOn
      with ⟨x0, _, hmax⟩
    exact MemLp.of_bound hf.aestronglyMeasurable ‖f x0‖
      (Filter.Eventually.of_forall fun x => hmax (Set.mem_univ x))

  have real_w11 {d : ℕ} {w : UnitAddTorus (Fin d) → ℝ}
      (hw : ContDiff ℝ 1 (fun y => w (TorusLift d y)))
      {p : ℝ} (hp : Real.HolderConjugate (d : ℝ) p) :
      (∫ x, ‖w x‖ ^ p) ^ (1 / p) ≤
        (∫ x, ‖w x‖) + ∑ j : Fin d, ∫ x, ‖TorusGradient w x j‖ := by
    have hc : Continuous (fun x => ‖w x‖ ^ p) :=
      (continuous_c1 hw).norm.rpow_const (fun _ => Or.inr hp.symm.nonneg)
    have hi : Integrable (fun x => ‖w x‖ ^ p) volume := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hn : ∀ x, 0 ≤ ‖w x‖ ^ p := fun x => Real.rpow_nonneg (norm_nonneg _) _
    have h := w11_bound hw hp
    have hre : (∫⁻ x, ‖w x‖ₑ ^ p) = ENNReal.ofReal (∫ x, ‖w x‖ ^ p) := by
      rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hn)]
      apply lintegral_congr
      intro x
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.symm.nonneg]
    have hb0 : 0 ≤ (∫ x, ‖w x‖) + ∑ j : Fin d, ∫ x, ‖TorusGradient w x j‖ := by
      apply add_nonneg (integral_nonneg fun x => norm_nonneg _)
      exact Finset.sum_nonneg fun j _ => integral_nonneg fun x => norm_nonneg _
    rw [hre, ENNReal.ofReal_rpow_of_nonneg hb0 hp.symm.nonneg] at h
    have hr := (ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hb0 p)).mp h
    have hpow := Real.rpow_le_rpow (integral_nonneg hn) hr
      (one_div_nonneg.mpr hp.symm.nonneg)
    rw [← Real.rpow_mul hb0, mul_one_div_cancel hp.symm.pos.ne', Real.rpow_one] at hpow
    exact hpow

  have gradient_continuous_c1 {d : ℕ} {f : UnitAddTorus (Fin d) → ℝ}
      (hf : ContDiff ℝ 1 (fun y => f (TorusLift d y))) : Continuous (TorusGradient f) := by
    change Continuous (fun x => WithLp.toLp 2 (fun j => TorusGradient f x j))
    apply (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp
    apply continuous_pi
    exact component_continuous_c1 hf

  have gradient_normpow_bound {d : ℕ} {f : UnitAddTorus (Fin d) → ℝ}
      (hf : ContDiff ℝ 1 (fun y => f (TorusLift d y)))
      {γ : ℝ} (hγ : 1 < γ) (x : UnitAddTorus (Fin d)) (j : Fin d) :
      ‖TorusGradient (fun x => ‖f x‖ ^ γ) x j‖ ≤
        γ * ‖f x‖ ^ (γ - 1) * ‖TorusGradient f x‖ := by
    obtain ⟨y, rfl⟩ := (quotient d).surjective x
    rw [gradient_on_lift]
    have hd := (hasFDerivAt_norm_rpow (f (TorusLift d y)) hγ).comp y
      (hf.differentiable one_ne_zero y).hasFDerivAt
    have heq := hd.fderiv
    change fderiv ℝ (fun z => ‖f (TorusLift d z)‖ ^ γ) y = _ at heq
    rw [heq, ContinuousLinearMap.comp_apply]
    have hbound := ContinuousLinearMap.le_opNorm
      (fderiv ℝ (fun t : ℝ => ‖t‖ ^ γ) (f (TorusLift d y)))
      (fderiv ℝ (fun z => f (TorusLift d z)) y (EuclideanSpace.single j 1))
    have hnorm : ‖(γ * ‖f (TorusLift d y)‖ ^ (γ - 2)) • innerSL ℝ (f (TorusLift d y))‖ =
        γ * ‖f (TorusLift d y)‖ ^ (γ - 1) := by
      rw [← fderiv_norm_rpow _ hγ, norm_fderiv_norm_id_rpow _ hγ]
    rw [fderiv_norm_rpow _ hγ, hnorm] at hbound
    apply hbound.trans
    rw [← gradient_on_lift]
    exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le (TorusGradient f (TorusLift d y)) j)
      (by positivity)

  have powered_w11 {d : ℕ} {f : UnitAddTorus (Fin d) → ℝ}
      (hf : ContDiff ℝ 1 (fun y => f (TorusLift d y)))
      {q γ : ℝ} (hq : Real.HolderConjugate (d : ℝ) q) (hγ : 1 < γ) :
      (∫ x, ‖f x‖ ^ (γ * q)) ^ (1 / q) ≤
        (∫ x, ‖f x‖ ^ γ) + (d : ℝ) * γ *
          ∫ x, ‖f x‖ ^ (γ - 1) * ‖TorusGradient f x‖ := by
    have hw : ContDiff ℝ 1 (fun y => ‖f (TorusLift d y)‖ ^ γ) := hf.norm_rpow hγ
    have h := real_w11 (w := fun x => ‖f x‖ ^ γ) hw hq
    have hg : Continuous (fun x => ‖f x‖ ^ (γ - 1) * ‖TorusGradient f x‖) :=
      ((continuous_c1 hf).norm.rpow_const (fun _ => Or.inr (by linarith))).mul
        (gradient_continuous_c1 hf).norm
    have hgi : Integrable (fun x => ‖f x‖ ^ (γ - 1) * ‖TorusGradient f x‖) volume := hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hcomp (j : Fin d) :
        (∫ x, ‖TorusGradient (fun x => ‖f x‖ ^ γ) x j‖) ≤
          γ * ∫ x, ‖f x‖ ^ (γ - 1) * ‖TorusGradient f x‖ := by
      rw [← integral_const_mul]
      apply integral_mono
      · exact (component_continuous_c1 (w := fun x => ‖f x‖ ^ γ) hw j).norm.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · exact hgi.const_mul γ
      · intro x
        simpa only [mul_assoc] using gradient_normpow_bound hf hγ x j
    have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hcomp j)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    have hh := h.trans (add_le_add_right hs _)
    have hnormpow (x : UnitAddTorus (Fin d)) : ‖‖f x‖ ^ γ‖ = ‖f x‖ ^ γ :=
      Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) γ)
    simp_rw [hnormpow, ← Real.rpow_mul (norm_nonneg _)] at hh
    simpa only [mul_assoc] using hh

  have bootstrap_algebra {A Z E δ p q : ℝ} (hA : 0 ≤ A) (hZ : 0 ≤ Z)
      (hE : 0 ≤ E) (hδ : 0 ≤ δ) (hp : 0 < p)
      (he : 1 / q - 1 / 2 = 1 / p)
      (h : A ^ (1 / q) ≤ A ^ (1 / 2 : ℝ) * (Z ^ (1 / 2 : ℝ) + δ * E ^ (1 / 2 : ℝ))) :
      A ^ (2 / p) ≤ 2 * (1 + δ^2) * (Z + E) := by
    by_cases ha : A = 0
    · subst A
      rw [Real.zero_rpow (by positivity : 2 / p ≠ 0)]
      positivity
    have hapos : 0 < A := lt_of_le_of_ne hA (Ne.symm ha)
    have hcancel : A ^ (1 / p) ≤ Z ^ (1 / 2 : ℝ) + δ * E ^ (1 / 2 : ℝ) := by
      rw [← he, Real.rpow_sub hapos]
      apply (div_le_iff₀ (Real.rpow_pos_of_pos hapos _)).mpr
      rw [mul_comm (Z ^ (1 / 2 : ℝ) + δ * E ^ (1 / 2 : ℝ)) (A ^ (1 / 2 : ℝ))]
      exact h
    have hrootZ : (Z ^ (1 / 2 : ℝ))^2 = Z := by
      rw [← Real.rpow_two, ← Real.rpow_mul hZ]
      norm_num
    have hrootE : (E ^ (1 / 2 : ℝ))^2 = E := by
      rw [← Real.rpow_two, ← Real.rpow_mul hE]
      norm_num
    have hs : (A ^ (1 / p))^2 ≤ (Z ^ (1 / 2 : ℝ) + δ * E ^ (1 / 2 : ℝ))^2 := by
      exact pow_le_pow_left₀ (Real.rpow_nonneg hA _) hcancel 2
    have hpower : (A ^ (1 / p))^2 = A ^ (2 / p) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hA]
      congr 1
      ring
    rw [hpower] at hs
    have hweighted : δ^2 * (E ^ (1 / 2 : ℝ))^2 = δ^2 * E := by rw [hrootE]
    have hbound : (Z ^ (1 / 2 : ℝ) + δ * E ^ (1 / 2 : ℝ))^2 ≤ 2*Z + 2*δ^2*E := by
      have hid : (Z ^ (1 / 2 : ℝ) + δ * E ^ (1 / 2 : ℝ))^2 +
          (Z ^ (1 / 2 : ℝ) - δ * E ^ (1 / 2 : ℝ))^2 = 2*Z + 2*δ^2*E := by
        calc
          _ = 2*(Z ^ (1 / 2 : ℝ))^2 + 2*δ^2*(E ^ (1 / 2 : ℝ))^2 := by ring
          _ = _ := by rw [hrootZ, hrootE]
      linarith [sq_nonneg (Z ^ (1 / 2 : ℝ) - δ * E ^ (1 / 2 : ℝ))]
    apply hs.trans (hbound.trans _)
    nlinarith [mul_nonneg (sq_nonneg δ) hZ]

  have cauchy {d : ℕ} {u v : UnitAddTorus (Fin d) → ℝ}
      (hu : Continuous u) (hv : Continuous v) (hu0 : ∀ x, 0 ≤ u x)
      (hv0 : ∀ x, 0 ≤ v x) :
      (∫ x, u x * v x) ≤ (∫ x, (u x)^2) ^ (1 / 2 : ℝ) *
        (∫ x, (v x)^2) ^ (1 / 2 : ℝ) := by
    have hp : Real.HolderConjugate 2 2 := by
      exact Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) hp
      (Filter.Eventually.of_forall hu0) (Filter.Eventually.of_forall hv0)
      (continuous_memLp u hu (ENNReal.ofReal 2))
      (continuous_memLp v hv (ENNReal.ofReal 2))
    simpa only [Real.rpow_two] using h

  have critical {d : ℕ} {f : UnitAddTorus (Fin d) → ℝ}
      (hf : ContDiff ℝ 1 (fun y => f (TorusLift d y)))
      {p q γ : ℝ} (hp : 0 < p) (hq : Real.HolderConjugate (d : ℝ) q)
      (hγ : 1 < γ) (hγq : γ * q = p) (hγ2 : (γ - 1) * 2 = p)
      (hexp : 1 / q - 1 / 2 = 1 / p) :
      (∫ x, ‖f x‖ ^ p) ^ (2 / p) ≤
        2 * (1 + ((d : ℝ) * γ)^2) *
          ((∫ x, (f x)^2) + ∫ x, ‖TorusGradient f x‖^2) := by
    have hfc := continuous_c1 hf
    have hpowc : Continuous (fun x => ‖f x‖ ^ (γ - 1)) :=
      hfc.norm.rpow_const (fun _ => Or.inr (by linarith))
    have hE := cauchy hpowc (gradient_continuous_c1 hf).norm
      (fun x => Real.rpow_nonneg (norm_nonneg _) _) (fun x => norm_nonneg _)
    have hZ := cauchy hpowc hfc.norm
      (fun x => Real.rpow_nonneg (norm_nonneg _) _) (fun x => norm_nonneg _)
    have hpow (x : UnitAddTorus (Fin d)) : (‖f x‖ ^ (γ - 1))^2 = ‖f x‖ ^ p := by
      rw [← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _), hγ2]
    have hnormsq (x : UnitAddTorus (Fin d)) : ‖f x‖^2 = (f x)^2 := by
      simp [Real.norm_eq_abs, sq_abs]
    simp_rw [hpow] at hE hZ
    simp_rw [hnormsq] at hZ
    have hprod (x : UnitAddTorus (Fin d)) : ‖f x‖ ^ (γ - 1) * ‖f x‖ = ‖f x‖ ^ γ := by
      rw [← Real.rpow_add_one' (norm_nonneg _) (by linarith : γ - 1 + 1 ≠ 0)]
      congr 1
      ring
    simp_rw [hprod] at hZ
    have hw := powered_w11 hf hq hγ
    rw [hγq] at hw
    have hbound : (∫ x, ‖f x‖ ^ p) ^ (1 / q) ≤
        (∫ x, ‖f x‖ ^ p) ^ (1 / 2 : ℝ) *
          ((∫ x, (f x)^2) ^ (1 / 2 : ℝ) + (d : ℝ) * γ *
            (∫ x, ‖TorusGradient f x‖^2) ^ (1 / 2 : ℝ)) := by
      calc
        _ ≤ (∫ x, ‖f x‖ ^ p) ^ (1 / 2 : ℝ) * (∫ x, (f x)^2) ^ (1 / 2 : ℝ) +
            (d : ℝ) * γ * ((∫ x, ‖f x‖ ^ p) ^ (1 / 2 : ℝ) *
              (∫ x, ‖TorusGradient f x‖^2) ^ (1 / 2 : ℝ)) :=
          hw.trans (add_le_add hZ (mul_le_mul_of_nonneg_left hE (by positivity)))
        _ = _ := by ring
    exact bootstrap_algebra
      (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _)
      (integral_nonneg fun x => sq_nonneg _) (integral_nonneg fun x => sq_nonneg _)
      (by positivity) hp hexp hbound

  have volume_probability (d : ℕ) :
      IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := by
    have hm : (volume : Measure (UnitAddTorus (Fin d))) =
        Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle (T := (1 : ℝ))) := by
      change Measure.pi (fun _ : Fin d => (volume : Measure (AddCircle (1 : ℝ)))) = _
      congr 1
      funext j
      rw [AddCircle.volume_eq_smul_haarAddCircle]
      simp
    rw [hm]
    infer_instance

  have two_dim {f : UnitAddTorus (Fin 2) → ℝ}
      (hf : ContDiff ℝ 1 (fun y => f (TorusLift 2 y))) :
      (∫ x, ‖f x‖ ^ (4 : ℝ)) ^ (1 / 2 : ℝ) ≤
        3 * ((∫ x, (f x)^2) + ∫ x, ‖TorusGradient f x‖^2) := by
    have hq : Real.HolderConjugate (2 : ℝ) 2 :=
      Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
    have hw := powered_w11 hf hq (by norm_num : (1 : ℝ) < 2)
    norm_num only [Nat.cast_ofNat] at hw
    have hcs := cauchy (continuous_c1 hf).norm (gradient_continuous_c1 hf).norm
      (fun x => norm_nonneg _) (fun x => norm_nonneg _)
    have hnormsq (x : UnitAddTorus (Fin 2)) : ‖f x‖^2 = (f x)^2 := by
      simp [Real.norm_eq_abs, sq_abs]
    simp_rw [Real.rpow_two, hnormsq] at hw
    simp_rw [hnormsq] at hcs
    have hz : 0 ≤ ∫ x, (f x)^2 := integral_nonneg fun x => sq_nonneg _
    have he : 0 ≤ ∫ x, ‖TorusGradient f x‖^2 := integral_nonneg fun x => sq_nonneg _
    have hrootZ : ((∫ x, (f x)^2) ^ (1 / 2 : ℝ))^2 = ∫ x, (f x)^2 := by
      rw [← Real.rpow_two, ← Real.rpow_mul hz]
      norm_num
    have hrootE : ((∫ x, ‖TorusGradient f x‖^2) ^ (1 / 2 : ℝ))^2 =
        ∫ x, ‖TorusGradient f x‖^2 := by
      rw [← Real.rpow_two, ← Real.rpow_mul he]
      norm_num
    norm_num only [sub_self, add_zero, Real.rpow_one] at hw
    nlinarith [sq_nonneg ((∫ x, (f x)^2) ^ (1 / 2 : ℝ) -
      (∫ x, ‖TorusGradient f x‖^2) ^ (1 / 2 : ℝ))]

  have fiber_one (H : UnitAddTorus (Fin 1) → ℝ) (x : UnitAddTorus (Fin 1)) :
      (∫ t : AddCircle (1 : ℝ), H (update x 0 t)) = ∫ z, H z := by
    have heq (t : AddCircle (1 : ℝ)) : update x 0 t =
        (MeasurableEquiv.funUnique (Fin 1) (AddCircle (1 : ℝ))).symm t := by
      ext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp [MeasurableEquiv.funUnique]
    simp_rw [heq]
    exact (volume_preserving_funUnique (Fin 1) (AddCircle (1 : ℝ))).symm.integral_comp' H

  have one_dim {f : UnitAddTorus (Fin 1) → ℝ}
      (hf : ContDiff ℝ 1 (fun y => f (TorusLift 1 y))) :
      (∫ x, ‖f x‖ ^ (4 : ℝ)) ^ (1 / 2 : ℝ) ≤
        2 * ((∫ x, (f x)^2) + ∫ x, ‖TorusGradient f x‖^2) := by
    letI := volume_probability 1
    have hq : Real.HolderConjugate (2 : ℝ) 2 :=
      Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
    have hfc := continuous_c1 hf
    have hgc := gradient_continuous_c1 hf
    have hcsF := cauchy hfc.norm (continuous_const : Continuous
        (fun _ : UnitAddTorus (Fin 1) => (1 : ℝ)))
      (fun x => norm_nonneg _) (fun _ => zero_le_one)
    have hcsG := cauchy hgc.norm (continuous_const : Continuous
        (fun _ : UnitAddTorus (Fin 1) => (1 : ℝ)))
      (fun x => norm_nonneg _) (fun _ => zero_le_one)
    have hnormsq (x : UnitAddTorus (Fin 1)) : ‖f x‖^2 = (f x)^2 := by
      simp [Real.norm_eq_abs, sq_abs]
    simp only [mul_one, one_pow, integral_const, probReal_univ,
      one_smul, Real.one_rpow, hnormsq] at hcsF hcsG
    let Z : ℝ := ∫ x, (f x)^2
    let E : ℝ := ∫ x, ‖TorusGradient f x‖^2
    let S : ℝ := Z ^ (1 / 2 : ℝ) + E ^ (1 / 2 : ℝ)
    have hz : 0 ≤ Z := integral_nonneg fun x => sq_nonneg _
    have he : 0 ≤ E := integral_nonneg fun x => sq_nonneg _
    have hs : 0 ≤ S := add_nonneg (Real.rpow_nonneg hz _) (Real.rpow_nonneg he _)
    have hpoint (x : UnitAddTorus (Fin 1)) : ‖f x‖ ≤ S := by
      have h := fiber_bound hf x 0
      rw [fiber_one (fun z => ‖f z‖) x, fiber_one (fun z => ‖TorusGradient f z 0‖) x] at h
      have hci : Integrable (fun z => ‖TorusGradient f z 0‖) volume :=
        (component_continuous_c1 hf 0).norm.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      have hgi : Integrable (fun z => ‖TorusGradient f z‖) volume :=
        hgc.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      have hcomp : (∫ z, ‖TorusGradient f z 0‖) ≤ ∫ z, ‖TorusGradient f z‖ :=
        integral_mono hci hgi (fun z => PiLp.norm_apply_le (TorusGradient f z) 0)
      exact h.trans ((add_le_add hcsF (hcomp.trans hcsG)))
    have hfi : Integrable (fun x => ‖f x‖^4) volume :=
      (hfc.norm.pow 4).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hfour : (∫ x, ‖f x‖^4) ≤ S^4 := by
      have hmono := integral_mono hfi (integrable_const (S^4))
        (fun x => pow_le_pow_left₀ (norm_nonneg _) (hpoint x) 4)
      simpa only [integral_const, probReal_univ, one_smul] using hmono
    have hroot := Real.rpow_le_rpow (integral_nonneg fun x => pow_nonneg (norm_nonneg _) 4)
      hfour (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hSroot : (S^4) ^ (1 / 2 : ℝ) = S^2 := by
      rw [← Real.rpow_natCast_mul hs]
      norm_num
    rw [hSroot] at hroot
    have hrootZ : (Z ^ (1 / 2 : ℝ))^2 = Z := by
      rw [← Real.rpow_two, ← Real.rpow_mul hz]
      norm_num
    have hrootE : (E ^ (1 / 2 : ℝ))^2 = E := by
      rw [← Real.rpow_two, ← Real.rpow_mul he]
      norm_num
    have hb : S^2 ≤ 2*(Z+E) := by
      dsimp [S]
      nlinarith [sq_nonneg (Z ^ (1 / 2 : ℝ) - E ^ (1 / 2 : ℝ))]
    simpa only [Real.rpow_ofNat, Z, E] using hroot.trans hb
  dsimp only
  by_cases hsmall : d ≤ 2
  · rw [if_pos hsmall]
    refine ⟨by norm_num, ?_⟩
    have hd12 : d = 1 ∨ d = 2 := by omega
    rcases hd12 with rfl | rfl
    · refine ⟨2, by norm_num, fun f hf => ?_⟩
      have hc : ContDiff ℝ 1 (fun y => f (TorusLift 1 y)) := hf.of_le (by simp)
      convert! one_dim hc using 1 <;> simp [Real.norm_eq_abs, Real.rpow_ofNat] <;> norm_num

    · refine ⟨3, by norm_num, fun f hf => ?_⟩
      have hc : ContDiff ℝ 1 (fun y => f (TorusLift 2 y)) := hf.of_le (by simp)
      convert! two_dim hc using 1 <;> simp [Real.norm_eq_abs, Real.rpow_ofNat] <;> norm_num

  · rw [if_neg hsmall]
    have hd2 : (2 : ℝ) < d := by exact_mod_cast (lt_of_not_ge hsmall)
    have hd1 : (1 : ℝ) < d := by linarith
    have hn : (d : ℝ) ≠ 0 := by linarith
    have hn1 : (d : ℝ) - 1 ≠ 0 := by linarith
    have hn2 : (d : ℝ) - 2 ≠ 0 := by linarith
    let p : ℝ := 2 * (d : ℝ) / ((d : ℝ) - 2)
    let q : ℝ := (d : ℝ) / ((d : ℝ) - 1)
    let γ : ℝ := 2 * ((d : ℝ) - 1) / ((d : ℝ) - 2)
    have hp2 : 2 < p := by
      dsimp [p]
      apply (lt_div_iff₀ (by linarith : (0 : ℝ) < d - 2)).mpr
      linarith
    have hq : Real.HolderConjugate (d : ℝ) q :=
      Real.HolderConjugate.conjExponent hd1
    have hγ : 1 < γ := by
      dsimp [γ]
      apply (lt_div_iff₀ (by linarith : (0 : ℝ) < d - 2)).mpr
      linarith
    have hγq : γ * q = p := by
      dsimp [γ, q, p]
      field_simp
    have hγ2 : (γ - 1) * 2 = p := by
      dsimp [γ, p]
      field_simp
      ring
    have hexp : 1 / q - 1 / 2 = 1 / p := by
      dsimp [q, p]
      field_simp
      ring
    refine ⟨hp2, 2 * (1 + ((d : ℝ) * γ)^2), by positivity, fun f hf => ?_⟩
    have hc : ContDiff ℝ 1 (fun y => f (TorusLift d y)) := hf.of_le (by simp)
    convert! critical hc (lt_trans (by norm_num) hp2) hq hγ hγq hγ2 hexp using 1 <;>
      simp [Real.norm_eq_abs, p]
