import Tablet.AtomicCoulombSourceMass
import Tablet.RieszKernelBounds
import Tablet.EuclideanGradient
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Tactic
set_option maxHeartbeats 1600000
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal
namespace AtomicLocalRieszBounds
private abbrev X (d : ℕ) := EuclideanSpace ℝ (Fin d)

private noncomputable def nearKernel (d : ℕ) (p r : ℝ) (x : X d) : ℝ :=
  if ‖x‖ < r then ‖x‖ ^ (-p) else 0

private noncomputable def farKernel (d : ℕ) (p r : ℝ) (x : X d) : ℝ :=
  if ‖x‖ < r then 0 else ‖x‖ ^ (-p)

private theorem kernel_split (d : ℕ) (p r : ℝ) (x : X d) :
    ‖x‖ ^ (-p) = nearKernel d p r x + farKernel d p r x := by
  simp only [nearKernel, farKernel]
  split_ifs <;> ring

private noncomputable def softForce (d : ℕ) (s ε : ℝ) (z : X d) : X d :=
  -((‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1) • z)

private noncomputable def softKernel (d : ℕ) (s ε : ℝ) (z : X d) : ℝ :=
  (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2) / s

private theorem softKernel_hasFDerivAt (d : ℕ) (s ε : ℝ) (hs : 0 < s) (hε : 0 < ε)
    (z : X d) : HasFDerivAt (softKernel d s ε) (innerSL ℝ (softForce d s ε z)) z := by
  have hbase : 0 < ‖z‖ ^ 2 + ε ^ 2 := by positivity
  have hder := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.add_const (ε ^ 2)).rpow_const
    (p := -s / 2) (Or.inl hbase.ne')
  have hscaled := hder.const_smul s⁻¹
  have heq : s⁻¹ • ((-s / 2 * (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1)) •
      (2 • innerSL ℝ z)) = innerSL ℝ (softForce d s ε z) := by
    ext h
    simp only [smul_apply, smul_eq_mul, nsmul_eq_mul, innerSL_apply_apply,
      softForce, inner_neg_left, real_inner_smul_left]
    field_simp
    ring
  rw [heq] at hscaled
  have hf : (s⁻¹ • fun x : X d => (‖x‖ ^ 2 + ε ^ 2) ^ (-s / 2)) = softKernel d s ε := by
    funext x
    simp only [Pi.smul_apply, softKernel, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [hf] at hscaled
  exact hscaled

-- Explicit softened radial force formula. Its identification with the gradient
-- of g_{s,ε} is a separate derivative theorem, not assumed here.
private theorem softForce_norm_le (d : ℕ) (s ε : ℝ) (hs : 0 ≤ s) (z : X d) :
    ‖softForce d s ε z‖ ≤ ‖z‖ ^ (-(s + 1)) := by
  by_cases hz : z = 0
  · subst z
    simp only [softForce, norm_zero, smul_zero, neg_zero]
    exact Real.rpow_nonneg (by rfl) _
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hn2 : 0 < ‖z‖ ^ 2 := by positivity
    have he : -s / 2 - 1 ≤ 0 := by linarith
    have hp := Real.rpow_le_rpow_of_nonpos hn2
      (by nlinarith [sq_nonneg ε] : ‖z‖ ^ 2 ≤ ‖z‖ ^ 2 + ε ^ 2) he
    have hb : 0 ≤ ‖z‖ ^ 2 + ε ^ 2 := by positivity
    unfold softForce
    rw [norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hb _)]
    calc
      (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1) * ‖z‖
          ≤ (‖z‖ ^ 2) ^ (-s / 2 - 1) * ‖z‖ :=
            mul_le_mul_of_nonneg_right hp hn.le
      _ = ‖z‖ ^ (-(s + 1)) := by
          rw [← Real.rpow_two, ← Real.rpow_mul hn.le]
          have heq := Real.rpow_add hn (2 * (-s / 2 - 1)) 1
          simp only [Real.rpow_one] at heq
          rw [← heq]
          congr 1
          ring

private theorem nearKernel_nonneg (d : ℕ) (p r : ℝ) (x : X d) :
    0 ≤ nearKernel d p r x := by
  unfold nearKernel
  split_ifs
  · exact Real.rpow_nonneg (norm_nonneg _) _
  · rfl

private theorem farKernel_nonneg (d : ℕ) (p r : ℝ) (x : X d) :
    0 ≤ farKernel d p r x := by
  unfold farKernel
  split_ifs
  · rfl
  · exact Real.rpow_nonneg (norm_nonneg _) _

private theorem farKernel_le (d : ℕ) (p r : ℝ) (hp : 0 ≤ p) (hr : 0 < r)
    (x : X d) : farKernel d p r x ≤ r ^ (-p) := by
  unfold farKernel
  split_ifs with h
  · exact Real.rpow_nonneg hr.le _
  · exact Real.rpow_le_rpow_of_nonpos hr (le_of_not_gt h) (by linarith)

private theorem nearKernel_integrable (d : ℕ) (hd : 1 ≤ d) (p r : ℝ)
    (hp : p < (d : ℝ)) : Integrable (nearKernel d p r) volume := by
  have hdim : 1 ≤ Module.finrank ℝ (X d) := by simpa [X] using hd
  have hpd : p < Module.finrank ℝ (X d) := by simpa [X] using hp
  have hmeas : AEStronglyMeasurable (fun x : X d => ‖x‖ ^ (-p)) volume := by
    exact (continuous_norm.measurable.pow_const _).aestronglyMeasurable
  have hi := integrableOn_ball_of_norm_le_rpow (μ := (volume : Measure (X d)))
    hdim hpd (C := (1 : ℝ)) (r := r)
    (by filter_upwards with x; simp only [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) (-p)), one_mul]; rfl) hmeas
  have hh := (integrable_indicator_iff measurableSet_ball).2 hi
  have heq : nearKernel d p r =
      (ball (0 : X d) r).indicator (fun x => ‖x‖ ^ (-p)) := by
    funext x
    simp [nearKernel, Set.indicator]
  rw [heq]
  exact hh

private theorem translated_nearKernel_integrable (d : ℕ) (hd : 1 ≤ d) (p r : ℝ)
    (hp : p < (d : ℝ)) (y : X d) :
    Integrable (fun x => nearKernel d p r (x - y)) volume := by
  simpa only [sub_eq_add_neg] using (nearKernel_integrable d hd p r hp).comp_add_right (-y)

private theorem translated_nearKernel_integral (d : ℕ) (p r : ℝ) (y : X d) :
    (∫ x : X d, nearKernel d p r (x - y)) = ∫ x : X d, nearKernel d p r x := by
  simpa only [sub_eq_add_neg] using integral_add_right_eq_self
    (nearKernel d p r) (-y) (μ := (volume : Measure (X d)))

private theorem nearKernel_integral_nonneg (d : ℕ) (p r : ℝ) :
    0 ≤ ∫ x : X d, nearKernel d p r x :=
  integral_nonneg fun x => nearKernel_nonneg d p r x

private theorem softened_atomic_potential_hasFDerivAt {d : ℕ} {ι : Type*} (J : Finset ι)
    (a : ι → ℝ) (y : ι → X d) (s ε : ℝ) (hs : 0 < s) (hε : 0 < ε) (x : X d) :
    HasFDerivAt (fun z => ∑ j ∈ J, a j * softKernel d s ε (z - y j))
      (innerSL ℝ (∑ j ∈ J, a j • softForce d s ε (x - y j))) x := by
  have h_each : ∀ j ∈ J, HasFDerivAt
      (fun z => a j * softKernel d s ε (z - y j))
      (a j • innerSL ℝ (softForce d s ε (x - y j))) x := by
    intro j hj
    have hh := (softKernel_hasFDerivAt d s ε hs hε (x - y j)).comp x
      ((hasFDerivAt_id x).sub_const (y j))
    simp only [ContinuousLinearMap.comp_id] at hh
    convert! hh.const_smul (a j) using 1
  have hh := HasFDerivAt.fun_sum h_each
  have heq : (∑ j ∈ J, a j • innerSL ℝ (softForce d s ε (x - y j))) =
      innerSL ℝ (∑ j ∈ J, a j • softForce d s ε (x - y j)) := by
    ext h
    simp only [sum_apply, smul_apply, innerSL_apply_apply,
      smul_eq_mul, sum_inner, real_inner_smul_left]
  rw [heq] at hh
  exact hh


private theorem softKernel_contDiff (d : ℕ) (s ε : ℝ) (hε : 0 < ε) {n : ℕ∞} :
    ContDiff ℝ n (softKernel d s ε) := by
  unfold softKernel
  exact (((contDiff_norm_sq ℝ).add contDiff_const).rpow_const_of_ne
    (fun z => ne_of_gt (by positivity : 0 < ‖z‖ ^ 2 + ε ^ 2))).div_const s

private noncomputable def atomicU {d : ℕ} {ι : Type*} (J : Finset ι) (a : ι → ℝ)
    (y : ι → X d) (s ε : ℝ) (x : X d) : ℝ :=
  ∑ j ∈ J, a j * softKernel d s ε (x - y j)

private theorem atomicU_contDiff {d : ℕ} {ι : Type*} (J : Finset ι) (a : ι → ℝ)
    (y : ι → X d) (s ε : ℝ) (hε : 0 < ε) {n : ℕ∞} :
    ContDiff ℝ n (atomicU J a y s ε) := by
  apply ContDiff.sum
  intro j hj
  exact contDiff_const.mul ((softKernel_contDiff d s ε hε).comp (contDiff_id.sub contDiff_const))

private theorem atomicU_gradient {d : ℕ} {ι : Type*} (J : Finset ι) (a : ι → ℝ)
    (y : ι → X d) (s ε : ℝ) (hs : 0 < s) (hε : 0 < ε) (x : X d) :
    EuclideanGradient (atomicU J a y s ε) x =
      ∑ j ∈ J, a j • softForce d s ε (x - y j) := by
  apply (InnerProductSpace.toDual ℝ (X d)).injective
  rw [EuclideanGradient, toDual_gradient]
  change fderiv ℝ (fun z => ∑ j ∈ J, a j * softKernel d s ε (z - y j)) x = _
  rw [(softened_atomic_potential_hasFDerivAt J a y s ε hs hε x).fderiv]
  rfl

private theorem softKernel_laplacian (d : ℕ) (s ε : ℝ) (hs : 0 < s) (hsd : s ≤ (d : ℝ) - 2) (hε : 0 < ε)
    (z : X d) :
    EuclideanLaplacian (softKernel d s ε) z =
      (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 2) *
        ((s + 2 - (d : ℝ)) * ‖z‖ ^ 2 - (d : ℝ) * ε ^ 2) := by
  have h := AtomicInteractionSource d s ε hs hsd hε
    ({()} : Finset Unit) (fun _ => (1 : ℝ)) (fun _ => (0 : X d)) (by simp)
  have he : (fun x : X d => ∑ j ∈ ({()} : Finset Unit),
      (1 : ℝ) * RieszKernel s ε (x - (0 : X d))) = softKernel d s ε := by
    funext x
    simp [RieszKernel, ne_of_gt hε, softKernel]
  rw [he] at h
  have hh := (h.2 z).1
  simp only [Finset.sum_singleton, sub_zero, one_mul] at hh
  nlinarith only [hh]

private noncomputable def localPowerConstant (d : ℕ) (p : ℝ) (K : Set (X d)) : ℝ :=
  (∫ x : X d, nearKernel d p 1 x) + volume.real K

private theorem localPowerConstant_nonneg (d : ℕ) (p : ℝ) (K : Set (X d)) :
    0 ≤ localPowerConstant d p K := add_nonneg (nearKernel_integral_nonneg _ _ _) (measureReal_nonneg)

private theorem translated_power_local (d : ℕ) (hd : 1 ≤ d) (p : ℝ) (hp : 0 ≤ p)
    (hpd : p < (d : ℝ)) (K : Set (X d)) (hK : MeasurableSet K)
    (hfin : volume K ≠ (⊤ : ENNReal)) (y : X d) :
    IntegrableOn (fun x => ‖x-y‖^(-p)) K volume ∧
      (∫ x in K, ‖x-y‖^(-p)) ≤ localPowerConstant d p K := by
  have hn := translated_nearKernel_integrable d hd p 1 hpd y
  have hc : IntegrableOn (fun _ : X d => (1:ℝ)) K volume := integrableOn_const hfin
  have hf : IntegrableOn (fun x => farKernel d p 1 (x-y)) K volume := by
    apply hc.mono' (by
      apply Measurable.aestronglyMeasurable
      unfold farKernel
      exact Measurable.ite (measurableSet_lt (continuous_id.sub continuous_const).norm.measurable measurable_const)
        measurable_const ((continuous_id.sub continuous_const).norm.measurable.pow_const _))
    exact Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (farKernel_nonneg _ _ _ _)]
      simpa using farKernel_le d p 1 hp (by norm_num) (x-y))
  have hi : IntegrableOn (fun x => ‖x-y‖^(-p)) K volume := by
    have hh := hn.integrableOn.add hf
    change IntegrableOn (fun x => nearKernel d p 1 (x-y)+farKernel d p 1 (x-y)) K volume at hh
    simpa only [← kernel_split] using hh
  refine ⟨hi,?_⟩
  calc
    (∫ x in K, ‖x-y‖^(-p)) =
        (∫ x in K, nearKernel d p 1 (x-y)) + (∫ x in K, farKernel d p 1 (x-y)) := by
          simp_rw [kernel_split d p 1]; exact integral_add hn.integrableOn hf
    _ ≤ (∫ x : X d, nearKernel d p 1 (x-y)) + volume.real K := by
      apply add_le_add
      · exact setIntegral_le_integral hn (Eventually.of_forall (fun x => nearKernel_nonneg _ _ _ _))
      · calc
          _ ≤ ∫ x in K, (1:ℝ) := integral_mono_ae hf hc (Eventually.of_forall (fun x => by
            simpa using farKernel_le d p 1 hp (by norm_num) (x-y)))
          _ = _ := by simp
    _ = _ := by rw [translated_nearKernel_integral]; rfl

private theorem softKernel_le_power {d : ℕ} (s ε : ℝ) (hs : 0 < s) (hε : 0 < ε)
    (z : X d) (hz : z ≠ 0) :
    softKernel d s ε z ≤ ‖z‖^(-s)/s := by
  simpa [RieszKernel, ne_of_gt hε, softKernel] using
    (RieszKernelBounds (d := d) s ε hs hε.le).2 z hz

private theorem softKernel_nonneg {d : ℕ} (s ε : ℝ) (hs : 0 < s) (z : X d) :
    0 ≤ softKernel d s ε z := div_nonneg (Real.rpow_nonneg (by positivity) _) hs.le

private theorem softKernel_local (d : ℕ) (hd : 1 ≤ d) (s ε : ℝ) (hs : 0 < s)
    (hsd : s < (d : ℝ)) (hε : 0 < ε) (K : Set (X d)) (hK : MeasurableSet K)
    (hfin : volume K ≠ (⊤ : ENNReal)) (y : X d) :
    IntegrableOn (fun x => softKernel d s ε (x-y)) K volume ∧
      (∫ x in K, softKernel d s ε (x-y)) ≤ localPowerConstant d s K/s := by
  letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hp := translated_power_local d hd s hs.le hsd K hK hfin y
  have hdom : ∀ᵐ x ∂volume, ‖softKernel d s ε (x-y)‖ ≤ ‖x-y‖^(-s)/s := by
    filter_upwards [volume.ae_ne y] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (softKernel_nonneg s ε hs _)]
    exact softKernel_le_power s ε hs hε _ (sub_ne_zero.mpr hx)
  have hm : AEStronglyMeasurable (fun x => softKernel d s ε (x-y)) (volume.restrict K) := by
    apply Continuous.aestronglyMeasurable
    exact (softKernel_contDiff d s ε hε : ContDiff ℝ 1 _).continuous.comp (continuous_id.sub continuous_const)
  have hi := (hp.1.div_const s).mono' hm (ae_restrict_of_ae hdom)
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ x in K, ‖x-y‖^(-s)/s := integral_mono_ae hi (hp.1.div_const s)
      ((ae_restrict_of_ae hdom).mono (fun x hx => (le_abs_self _).trans hx))
    _ = (∫ x in K, ‖x-y‖^(-s))/s := integral_div s _
    _ ≤ _ := div_le_div_of_nonneg_right hp.2 hs.le

private theorem atomic_local_potential {d : ℕ} {ι : Type*} (J : Finset ι) (a : ι → ℝ)
    (y : ι → X d) (hd : 3 ≤ d) (s ε A : ℝ) (hs : 0 < s)
    (hsd : s ≤ (d : ℝ)-2) (hε : 0 < ε) (ha : ∀ j ∈ J, 0 ≤ a j)
    (hA : ∑ j ∈ J, a j ≤ A) (K : Set (X d)) (hK : MeasurableSet K)
    (hfin : volume K ≠ (⊤ : ENNReal)) :
    IntegrableOn (atomicU J a y s ε) K volume ∧
      (∫ x in K, atomicU J a y s ε x) ≤ A*localPowerConstant d s K/s := by
  have hi := fun j => softKernel_local d (by omega) s ε hs (by linarith) hε K hK hfin (y j)
  refine ⟨integrable_finsetSum J (fun j hj => (hi j).1.const_mul (a j)),?_⟩
  change (∫ x in K, ∑ j ∈ J, a j*softKernel d s ε (x-y j)) ≤ _
  rw [integral_finsetSum J (fun j hj => (hi j).1.const_mul (a j))]
  simp_rw [integral_const_mul]
  calc
    _ ≤ ∑ j ∈ J, a j*(localPowerConstant d s K/s) := Finset.sum_le_sum (fun j hj =>
      mul_le_mul_of_nonneg_left (hi j).2 (ha j hj))
    _ = (∑ j ∈ J, a j)*(localPowerConstant d s K/s) := by rw [Finset.sum_mul]
    _ ≤ A*(localPowerConstant d s K/s) := mul_le_mul_of_nonneg_right hA
      (div_nonneg (localPowerConstant_nonneg _ _ _) hs.le)
    _ = _ := by ring

private theorem atomic_local_force {d : ℕ} {ι : Type*} (J : Finset ι) (a : ι → ℝ)
    (y : ι → X d) (hd : 3 ≤ d) (s ε A : ℝ) (hs : 0 < s)
    (hsd : s ≤ (d : ℝ)-2) (hε : 0 < ε) (ha : ∀ j ∈ J, 0 ≤ a j)
    (hA : ∑ j ∈ J, a j ≤ A) (K : Set (X d)) (hK : MeasurableSet K)
    (hfin : volume K ≠ (⊤ : ENNReal)) :
    IntegrableOn (fun x => ‖EuclideanGradient (atomicU J a y s ε) x‖) K volume ∧
      (∫ x in K, ‖EuclideanGradient (atomicU J a y s ε) x‖) ≤ A*localPowerConstant d (s+1) K := by
  let g := fun x => ∑ j ∈ J, a j*‖x-y j‖^(-(s+1))
  have hp := fun j => translated_power_local d (by omega) (s+1) (by linarith)
    (by linarith) K hK hfin (y j)
  have hg : IntegrableOn g K volume := integrable_finsetSum J (fun j hj => (hp j).1.const_mul (a j))
  have hdg : ∀ x, ‖EuclideanGradient (atomicU J a y s ε) x‖ ≤ g x := by
    intro x
    rw [atomicU_gradient J a y s ε hs hε]
    calc
      _ ≤ ∑ j ∈ J, ‖a j • softForce d s ε (x-y j)‖ := norm_sum_le _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (ha j hj)]
        exact mul_le_mul_of_nonneg_left (softForce_norm_le d s ε hs.le _) (ha j hj)
  have hm : AEStronglyMeasurable (fun x => ‖EuclideanGradient (atomicU J a y s ε) x‖) (volume.restrict K) := by
    apply Continuous.aestronglyMeasurable
    exact ((InnerProductSpace.toDual ℝ (X d)).symm.continuous.comp
      ((atomicU_contDiff J a y s ε hε : ContDiff ℝ 1 _).continuous_fderiv (by norm_num))).norm
  have hi := hg.mono' hm (Eventually.of_forall (fun x => by simpa using hdg x))
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ x in K, g x := integral_mono_ae hi hg (Eventually.of_forall hdg)
    _ = ∑ j ∈ J, a j*(∫ x in K, ‖x-y j‖^(-(s+1))) := by
      dsimp [g]; rw [integral_finsetSum J (fun j hj => (hp j).1.const_mul (a j))]; simp_rw [integral_const_mul]
    _ ≤ ∑ j ∈ J, a j*localPowerConstant d (s+1) K := Finset.sum_le_sum (fun j hj =>
      mul_le_mul_of_nonneg_left (hp j).2 (ha j hj))
    _ = (∑ j ∈ J, a j)*localPowerConstant d (s+1) K := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hA (localPowerConstant_nonneg _ _ _)
private theorem soft_source_le_power (d : ℕ) (s ε : ℝ) (hs : 0 < s)
    (hsd : s ≤ (d : ℝ) - 2) (hε : 0 < ε)
    (z : X d) (hz : z ≠ 0) :
    -EuclideanLaplacian (softKernel d s ε) z ≤
      (d:ℝ)*‖z‖^(-(s+2)) := by
  rw [softKernel_laplacian d s ε hs hsd hε]
  have hb : 0 < ‖z‖^2+ε^2 := by positivity
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hpow : (‖z‖^2+ε^2)^(-s/2-2)*(‖z‖^2+ε^2) =
      (‖z‖^2+ε^2)^(-s/2-1) := by
    calc
      _ = (‖z‖^2+ε^2)^(-s/2-2)*(‖z‖^2+ε^2)^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hb]; congr 1; ring
  calc
    _ = (‖z‖^2+ε^2)^(-s/2-2)*(((d:ℝ)-s-2)*‖z‖^2+(d:ℝ)*ε^2) := by ring
    _ ≤ (‖z‖^2+ε^2)^(-s/2-2)*((d:ℝ)*(‖z‖^2+ε^2)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hb.le _)
      nlinarith [sq_nonneg ‖z‖]
    _ = (d:ℝ)*(‖z‖^2+ε^2)^(-s/2-1) := by rw [← mul_assoc,mul_comm _ (d:ℝ),mul_assoc,hpow]
    _ ≤ (d:ℝ)*(‖z‖^2)^(-s/2-1) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg ε]) (by linarith))
      (Nat.cast_nonneg _)
    _ = _ := by rw [← Real.rpow_two,← Real.rpow_mul hn.le]; congr 2; ring


end AtomicLocalRieszBounds

open AtomicLocalRieszBounds

-- [TABLET NODE: AtomicLocalRieszBounds]
theorem AtomicLocalRieszBounds (d : ℕ) (hd : 3 ≤ d) (s : ℝ)
    (hs : 0 < s) (hsd : s ≤ (d : ℝ) - 2)
    (K : Set (OneParticle d)) (hK : MeasurableSet K)
    (hfin : volume K ≠ (⊤ : ENNReal)) :
    ∃ P F S : ℝ, 0 ≤ P ∧ 0 ≤ F ∧ 0 ≤ S ∧
    ∀ {ι : Type*} (J : Finset ι) (a : ι → ℝ) (y : ι → OneParticle d)
      (ε A : ℝ), 0 < ε → 0 ≤ A → (∀ j ∈ J, 0 ≤ a j) →
      (∑ j ∈ J, a j ≤ A) →
      let U := fun x => ∑ j ∈ J, a j * RieszKernel s ε (x - y j)
      IntegrableOn U K ∧
      IntegrableOn (fun x => ‖EuclideanGradient U x‖) K ∧
      IntegrableOn (fun x => -EuclideanLaplacian U x) K ∧
      (∫ x in K, U x) ≤ A * P ∧
      (∫ x in K, ‖EuclideanGradient U x‖) ≤ A * F ∧
      (∫ x in K, -EuclideanLaplacian U x) ≤ A * S := by
-- BODY
  let P := localPowerConstant d s K / s
  let F := localPowerConstant d (s + 1) K
  let C := ∫ z : OneParticle d,
    (d : ℝ) * (‖z‖ ^ 2 + 1) ^ (-((d : ℝ) + 2) / 2)
  let S := if s = (d : ℝ) - 2 then C else (d : ℝ) * localPowerConstant d (s + 2) K
  have hC : 0 ≤ C := (AtomicCoulombSourceMass.{0} d hd).1
  have hS : 0 ≤ S := by
    dsimp [S]
    split_ifs
    · exact hC
    · exact mul_nonneg (Nat.cast_nonneg _) (localPowerConstant_nonneg _ _ _)
  refine ⟨P, F, S, div_nonneg (localPowerConstant_nonneg _ _ _) hs.le,
    localPowerConstant_nonneg _ _ _, hS, ?_⟩
  intro ι J a y ε A hε hA0 ha hA
  dsimp only
  let U := fun x => ∑ j ∈ J, a j * RieszKernel s ε (x - y j)
  have he : U = atomicU J a y s ε := by
    funext x
    simp only [U, RieszKernel, if_neg (ne_of_gt hε), atomicU, softKernel]
  have hp := atomic_local_potential J a y hd s ε A hs hsd hε ha hA K hK hfin
  have hf := atomic_local_force J a y hd s ε A hs hsd hε ha hA K hK hfin
  have hsi : IntegrableOn (fun x => -EuclideanLaplacian U x) K ∧
      (∫ x in K, -EuclideanLaplacian U x) ≤ A * S := by
    by_cases hc : s = (d : ℝ) - 2
    · subst s
      have hh := (AtomicCoulombSourceMass d hd).2 J a y ε hε ha
      refine ⟨(hh.2.2 K).1, ?_⟩
      calc
        _ ≤ (∑ j ∈ J, a j) * C := (hh.2.2 K).2
        _ ≤ A * C := mul_le_mul_of_nonneg_right hA hC
        _ = A * S := by simp [S]
    · have hlt : s + 2 < (d : ℝ) := by
        have hh : s < (d : ℝ) - 2 := lt_of_le_of_ne hsd hc
        linarith
      letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
      let σ := fun z : OneParticle d =>
        (((d : ℝ) - s - 2) * ‖z‖ ^ 2 + (d : ℝ) * ε ^ 2) *
          (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 2)
      have hσeq (z : OneParticle d) : σ z = -EuclideanLaplacian (softKernel d s ε) z := by
        rw [softKernel_laplacian d s ε hs hsd hε]
        dsimp [σ]
        ring
      have hσn (z : OneParticle d) : 0 ≤ σ z := by
        dsimp [σ]
        have hh : 0 ≤ (d : ℝ) - s - 2 := by linarith
        positivity
      have hσm : Measurable σ := by
        dsimp [σ]
        fun_prop
      have hlocal (j : ι) : IntegrableOn (fun x => σ (x - y j)) K ∧
          (∫ x in K, σ (x - y j)) ≤ (d : ℝ) * localPowerConstant d (s + 2) K := by
        have hb := translated_power_local d (by omega) (s + 2) (by linarith) hlt K hK hfin (y j)
        have hdom : ∀ᵐ x ∂volume, ‖σ (x - y j)‖ ≤ (d : ℝ) * ‖x - y j‖ ^ (-(s + 2)) := by
          filter_upwards [volume.ae_ne (y j)] with x hx
          rw [Real.norm_eq_abs, abs_of_nonneg (hσn _), hσeq]
          exact soft_source_le_power d s ε hs hsd hε _ (sub_ne_zero.mpr hx)
        have hi := (hb.1.const_mul (d : ℝ)).mono'
          ((hσm.comp (continuous_id.sub continuous_const).measurable).aestronglyMeasurable)
          (ae_restrict_of_ae hdom)
        refine ⟨hi, ?_⟩
        calc
          _ ≤ ∫ x in K, (d : ℝ) * ‖x - y j‖ ^ (-(s + 2)) :=
            integral_mono_ae hi (hb.1.const_mul (d : ℝ))
              ((ae_restrict_of_ae hdom).mono (fun x hx => (le_abs_self _).trans hx))
          _ = (d : ℝ) * (∫ x in K, ‖x - y j‖ ^ (-(s + 2))) := integral_const_mul _ _
          _ ≤ _ := mul_le_mul_of_nonneg_left hb.2 (Nat.cast_nonneg _)
      have hsource := AtomicInteractionSource d s ε hs hsd hε J a y ha
      have hsum : (fun x => -EuclideanLaplacian U x) =
          fun x => ∑ j ∈ J, a j * σ (x - y j) := by
        funext x
        rw [(hsource.2 x).1]
        dsimp [σ]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [hsum]
      refine ⟨integrable_finsetSum J (fun j hj => (hlocal j).1.const_mul (a j)), ?_⟩
      rw [integral_finsetSum J (fun j hj => (hlocal j).1.const_mul (a j))]
      simp_rw [integral_const_mul]
      calc
        _ ≤ ∑ j ∈ J, a j * ((d : ℝ) * localPowerConstant d (s + 2) K) :=
          Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hlocal j).2 (ha j hj))
        _ = (∑ j ∈ J, a j) * S := by rw [Finset.sum_mul]; simp [S, hc]
        _ ≤ A * S := mul_le_mul_of_nonneg_right hA hS
  change IntegrableOn U K ∧
    IntegrableOn (fun x => ‖EuclideanGradient U x‖) K ∧
    IntegrableOn (fun x => -EuclideanLaplacian U x) K ∧
    (∫ x in K, U x) ≤ A * P ∧
    (∫ x in K, ‖EuclideanGradient U x‖) ≤ A * F ∧
    (∫ x in K, -EuclideanLaplacian U x) ≤ A * S
  rw [← he] at hp hf
  exact ⟨hp.1, hf.1, hsi.1, by simpa [P, div_eq_mul_inv, mul_assoc] using hp.2,
    hf.2, hsi.2⟩
