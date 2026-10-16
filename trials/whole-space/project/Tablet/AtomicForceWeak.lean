module

public import Tablet.RieszKernel
public import Tablet.EuclideanGradient
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Tactic

@[expose] public section
set_option maxHeartbeats 1600000
open MeasureTheory Set Metric
open scoped ENNReal NNReal
namespace AtomicForceWeak

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

private theorem optimal_radius_identities (A t p : ℝ) (hA : 0 < A) (ht : 0 < t) (hp : 0 < p) :
    let r := (2 * A / t) ^ (1 / p)
    0 < r ∧ A * r ^ (-p) = t / 2 := by
  dsimp
  have hu : 0 < 2 * A / t := by positivity
  refine ⟨Real.rpow_pos_of_pos hu _, ?_⟩
  rw [← Real.rpow_mul hu.le]
  have hexp : 1 / p * -p = (-1 : ℝ) := by field_simp
  rw [hexp, Real.rpow_neg_one]
  field_simp

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

private theorem nearKernel_measurable (d : ℕ) (p r : ℝ) : Measurable (nearKernel d p r) := by
  unfold nearKernel
  exact Measurable.ite (measurableSet_lt continuous_norm.measurable measurable_const)
    (continuous_norm.measurable.pow_const _) measurable_const

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

private theorem nearKernel_smul (d : ℕ) (p r : ℝ) (hr : 0 < r) (x : X d) :
    nearKernel d p r (r • x) = r ^ (-p) * nearKernel d p 1 x := by
  have hn : ‖r • x‖ = r * ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  have hlt : r * ‖x‖ < r ↔ ‖x‖ < 1 := by
    constructor <;> intro h <;> nlinarith
  simp only [nearKernel, hn, hlt]
  split_ifs
  · exact Real.mul_rpow hr.le (norm_nonneg x)
  · ring

private theorem nearKernel_integral_scale (d : ℕ) (p r : ℝ) (hr : 0 < r) :
    (∫ x : X d, nearKernel d p r x) =
      (∫ x : X d, nearKernel d p 1 x) * r ^ ((d : ℝ) - p) := by
  have hc := Measure.integral_comp_smul_of_nonneg
    (volume : Measure (X d)) (nearKernel d p r) r (hR := hr.le)
  simp only [X, finrank_euclideanSpace_fin, smul_eq_mul] at hc
  simp_rw [nearKernel_smul d p r hr] at hc
  rw [integral_const_mul] at hc
  have hpow : r ^ d ≠ 0 := pow_ne_zero _ hr.ne'
  have hm := congrArg (fun z : ℝ => r ^ d * z) hc
  have hi : (∫ x : X d, nearKernel d p r x) =
      r ^ d * r ^ (-p) * (∫ x : X d, nearKernel d p 1 x) := by
    simp only [← mul_assoc, mul_inv_cancel₀ hpow, one_mul] at hm
    exact hm.symm
  rw [hi, ← Real.rpow_natCast r d, ← Real.rpow_add hr]
  rw [sub_eq_add_neg, mul_comm]

-- Finite positive atomic exterior charges, with no location or count restriction.
private theorem atomic_far_bound {d : ℕ} {ι : Type*} (J : Finset ι)
    (a : ι → ℝ) (y : ι → X d) (p r A : ℝ)
    (ha : ∀ j ∈ J, 0 ≤ a j) (hA : ∑ j ∈ J, a j ≤ A)
    (hp : 0 ≤ p) (hr : 0 < r) (x : X d) :
    (∑ j ∈ J, a j * farKernel d p r (x - y j)) ≤ A * r ^ (-p) := by
  calc
    (∑ j ∈ J, a j * farKernel d p r (x - y j))
        ≤ ∑ j ∈ J, a j * r ^ (-p) := by
          apply Finset.sum_le_sum
          intro j hj
          exact mul_le_mul_of_nonneg_left (farKernel_le d p r hp hr _) (ha j hj)
    _ = (∑ j ∈ J, a j) * r ^ (-p) := by rw [Finset.sum_mul]
    _ ≤ A * r ^ (-p) := mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg hr.le _)

private theorem atomic_near_integrable {d : ℕ} {ι : Type*} (J : Finset ι)
    (a : ι → ℝ) (y : ι → X d) (hd : 1 ≤ d) (p r : ℝ) (hp : p < (d : ℝ)) :
    Integrable (fun x => ∑ j ∈ J, a j * nearKernel d p r (x - y j)) volume := by
  apply integrable_finsetSum
  intro j hj
  exact (translated_nearKernel_integrable d hd p r hp (y j)).const_mul (a j)

private theorem atomic_near_integral {d : ℕ} {ι : Type*} (J : Finset ι)
    (a : ι → ℝ) (y : ι → X d) (hd : 1 ≤ d) (p r : ℝ)
    (hp : p < (d : ℝ)) (hr : 0 < r) :
    (∫ x : X d, ∑ j ∈ J, a j * nearKernel d p r (x - y j)) =
      (∑ j ∈ J, a j) * (∫ x : X d, nearKernel d p 1 x) * r ^ ((d : ℝ) - p) := by
  rw [integral_finsetSum J (fun j hj =>
    (translated_nearKernel_integrable d hd p r hp (y j)).const_mul (a j))]
  simp_rw [integral_const_mul, translated_nearKernel_integral, nearKernel_integral_scale d p r hr]
  rw [← Finset.sum_mul]
  ring

private theorem atomic_force_domination {d : ℕ} {ι : Type*} (J : Finset ι)
    (a : ι → ℝ) (y : ι → X d) (F : X d → X d) (p r : ℝ)
    (ha : ∀ j ∈ J, 0 ≤ a j) (hF : ∀ z, ‖F z‖ ≤ ‖z‖ ^ (-p)) (x : X d) :
    ‖∑ j ∈ J, a j • F (x - y j)‖ ≤
      (∑ j ∈ J, a j * nearKernel d p r (x - y j)) +
      (∑ j ∈ J, a j * farKernel d p r (x - y j)) := by
  calc
    ‖∑ j ∈ J, a j • F (x - y j)‖ ≤ ∑ j ∈ J, ‖a j • F (x - y j)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ J, a j * ‖x - y j‖ ^ (-p) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ha j hj)]
      exact mul_le_mul_of_nonneg_left (hF _) (ha j hj)
    _ = _ := by simp_rw [kernel_split d p r, mul_add]; rw [Finset.sum_add_distrib]

private theorem atomic_force_weak_radius {d : ℕ} {ι : Type*} (J : Finset ι)
    (a : ι → ℝ) (y : ι → X d) (F : X d → X d)
    (hd : 1 ≤ d) (p r A : ℝ) (ha : ∀ j ∈ J, 0 ≤ a j)
    (hA : ∑ j ∈ J, a j ≤ A) (hApos : 0 < A) (hp0 : 0 ≤ p)
    (hpd : p < (d : ℝ)) (hr : 0 < r)
    (hF : ∀ z, ‖F z‖ ≤ ‖z‖ ^ (-p)) :
    volume {x : X d | 2 * (A * r ^ (-p)) < ‖∑ j ∈ J, a j • F (x - y j)‖} ≤
      ENNReal.ofReal ((∑ j ∈ J, a j) *
        (∫ x : X d, nearKernel d p 1 x) * r ^ ((d : ℝ) - p)) /
        ENNReal.ofReal (A * r ^ (-p)) := by
  let n : X d → ℝ := fun x => ∑ j ∈ J, a j * nearKernel d p r (x - y j)
  let b : ℝ := A * r ^ (-p)
  have hb : 0 < b := by dsimp [b]; positivity
  have hn : ∀ x, 0 ≤ n x := by
    intro x
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (ha j hj) (nearKernel_nonneg d p r _)
  have hi := atomic_near_integrable J a y hd p r hpd
  have hm : AEMeasurable (fun x => ENNReal.ofReal (n x)) volume :=
    hi.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hset : {x : X d | 2 * b < ‖∑ j ∈ J, a j • F (x - y j)‖} ⊆
      {x | ENNReal.ofReal b ≤ ENNReal.ofReal (n x)} := by
    intro x hx
    have hf := atomic_far_bound J a y p r A ha hA hp0 hr x
    have hd := atomic_force_domination J a y F p r ha hF x
    have hnb : b ≤ n x := by dsimp [n, b] at *; linarith
    exact ENNReal.ofReal_le_ofReal hnb
  have hmark := (measure_mono hset).trans (meas_ge_le_lintegral_div hm
    (by exact ne_of_gt (ENNReal.ofReal_pos.mpr hb)) ENNReal.ofReal_ne_top)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hn)] at hmark
  rw [atomic_near_integral J a y hd p r hpd hr] at hmark
  exact hmark

private theorem atomic_force_weak_distribution {d : ℕ} {ι : Type*} (J : Finset ι)
    (a : ι → ℝ) (y : ι → X d) (F : X d → X d)
    (hd : 1 ≤ d) (p A : ℝ) (ha : ∀ j ∈ J, 0 ≤ a j)
    (hA : ∑ j ∈ J, a j ≤ A) (hApos : 0 < A) (hp : 0 < p)
    (hpd : p < (d : ℝ)) (hF : ∀ z, ‖F z‖ ≤ ‖z‖ ^ (-p)) (t : ℝ) (ht : 0 < t) :
    volume {x : X d | t < ‖∑ j ∈ J, a j • F (x - y j)‖} ≤
      ENNReal.ofReal ((∫ x : X d, nearKernel d p 1 x) *
        (2 * A / t) ^ ((d : ℝ) / p)) := by
  let r : ℝ := (2 * A / t) ^ (1 / p)
  have hrad := optimal_radius_identities A t p hApos ht hp
  have hr : 0 < r := hrad.1
  have hfar : A * r ^ (-p) = t / 2 := hrad.2
  have hthreshold : 2 * (A * r ^ (-p)) = t := by linarith
  have hweak := atomic_force_weak_radius J a y F hd p r A ha hA hApos hp.le hpd hr hF
  rw [hthreshold] at hweak
  let I : ℝ := ∫ x : X d, nearKernel d p 1 x
  have hI : 0 ≤ I := nearKernel_integral_nonneg d p 1
  have hn : (∑ j ∈ J, a j) * I * r ^ ((d : ℝ) - p) ≤
      A * I * r ^ ((d : ℝ) - p) := by
    gcongr
  have hdpos : 0 < A * r ^ (-p) := by positivity
  apply hweak.trans
  calc
    ENNReal.ofReal ((∑ j ∈ J, a j) * I * r ^ ((d : ℝ) - p)) /
        ENNReal.ofReal (A * r ^ (-p))
      ≤ ENNReal.ofReal (A * I * r ^ ((d : ℝ) - p)) /
        ENNReal.ofReal (A * r ^ (-p)) := by
          gcongr
    _ = ENNReal.ofReal ((A * I * r ^ ((d : ℝ) - p)) / (A * r ^ (-p))) :=
      (ENNReal.ofReal_div_of_pos hdpos).symm
    _ = ENNReal.ofReal (I * (2 * A / t) ^ ((d : ℝ) / p)) := by
      congr 1
      have hexp : (d : ℝ) - p = (d : ℝ) + (-p) := by ring
      rw [hexp, Real.rpow_add hr]
      have hrr : r ^ (-p) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
      have heq : (A * I * (r ^ (d : ℝ) * r ^ (-p))) / (A * r ^ (-p)) =
          I * r ^ (d : ℝ) := by field_simp
      rw [heq]
      dsimp [r]
      rw [← Real.rpow_mul (by positivity : 0 ≤ 2 * A / t)]
      congr 2
      ring

private theorem softened_atomic_force_weak_distribution {d : ℕ} {ι : Type*} (J : Finset ι)
    (a : ι → ℝ) (y : ι → X d) (hd : 3 ≤ d) (s ε A : ℝ)
    (ha : ∀ j ∈ J, 0 ≤ a j) (hA : ∑ j ∈ J, a j ≤ A) (hApos : 0 < A)
    (hs : 0 < s) (hsd : s ≤ (d : ℝ) - 2) (t : ℝ) (ht : 0 < t) :
    volume {x : X d | t < ‖∑ j ∈ J, a j • softForce d s ε (x - y j)‖} ≤
      ENNReal.ofReal ((∫ x : X d, nearKernel d (s + 1) 1 x) *
        (2 * A / t) ^ ((d : ℝ) / (s + 1))) := by
  apply atomic_force_weak_distribution J a y (softForce d s ε) (by omega)
    (s + 1) A ha hA hApos (by linarith) (by linarith) _ t ht
  exact softForce_norm_le d s ε hs.le

private noncomputable def forceConstant (d : ℕ) (s : ℝ) : ℝ :=
  (∫ x : X d, nearKernel d (s + 1) 1 x) * (2 : ℝ) ^ ((d : ℝ) / (s + 1)) + 1

private theorem forceConstant_pos (d : ℕ) (s : ℝ) : 0 < forceConstant d s := by
  have hI := nearKernel_integral_nonneg d (s + 1) 1
  unfold forceConstant
  positivity

-- Complete weak-distribution estimate for the explicit softened force formula,
-- including A=0. Constant is selected before the atom count, locations and ε.
private theorem softened_atomic_force_weak_uniform {d : ℕ} {ι : Type*} (J : Finset ι)
    (a : ι → ℝ) (y : ι → X d) (hd : 3 ≤ d) (s ε A : ℝ)
    (ha : ∀ j ∈ J, 0 ≤ a j) (hA : ∑ j ∈ J, a j ≤ A) (hA0 : 0 ≤ A)
    (hs : 0 < s) (hsd : s ≤ (d : ℝ) - 2) (t : ℝ) (ht : 0 < t) :
    volume {x : X d | t < ‖∑ j ∈ J, a j • softForce d s ε (x - y j)‖} ≤
      ENNReal.ofReal (forceConstant d s * (A / t) ^ ((d : ℝ) / (s + 1))) := by
  rcases eq_or_lt_of_le hA0 with hAzero | hApos
  · have hAeq : A = 0 := hAzero.symm
    have ha0 : ∀ j ∈ J, a j = 0 := by
      intro j hj
      have hjle : a j ≤ ∑ i ∈ J, a i := Finset.single_le_sum ha hj
      rw [hAeq] at hA
      exact le_antisymm (hjle.trans hA) (ha j hj)
    have hsum : ∀ x, (∑ j ∈ J, a j • softForce d s ε (x - y j)) = 0 := by
      intro x
      apply Finset.sum_eq_zero
      intro j hj
      rw [ha0 j hj, zero_smul]
    simp only [hsum, norm_zero]
    have hempty : {x : X d | t < (0 : ℝ)} = ∅ := by ext x; simp [not_lt_of_ge ht.le]
    rw [hempty]
    simp
  · have hh := softened_atomic_force_weak_distribution J a y hd s ε A ha hA hApos hs hsd t ht
    apply hh.trans
    apply ENNReal.ofReal_le_ofReal
    have hI := nearKernel_integral_nonneg d (s + 1) 1
    have hratio : 0 ≤ A / t := by positivity
    have hbase : 2 * A / t = 2 * (A / t) := by ring
    rw [hbase, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hratio]
    unfold forceConstant
    nlinarith [Real.rpow_nonneg hratio ((d : ℝ) / (s + 1))]

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

end AtomicForceWeak

-- [TABLET NODE: AtomicForceWeak]
theorem AtomicForceWeak (d : ℕ) (hd : 3 ≤ d) (s : ℝ)
    (hs : 0 < s) (hsd : s ≤ (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} (J : Finset ι) (a : ι → ℝ)
      (y : ι → OneParticle d) (ε A : ℝ),
      (∀ j ∈ J, 0 ≤ a j) → (∑ j ∈ J, a j ≤ A) → 0 ≤ A → 0 < ε →
      ∀ t : ℝ, 0 < t →
      volume {x | t < ‖EuclideanGradient (fun z => ∑ j ∈ J,
        a j * RieszKernel s ε (z - y j)) x‖} ≤
        ENNReal.ofReal (C * (A / t) ^ ((d : ℝ) / (s + 1))) := by
-- BODY
  refine ⟨AtomicForceWeak.forceConstant d s, AtomicForceWeak.forceConstant_pos d s, ?_⟩
  intro ι J a y ε A ha hA hA0 hε t ht
  have hg (x : OneParticle d) :
      EuclideanGradient (fun z => ∑ j ∈ J, a j * RieszKernel s ε (z - y j)) x =
        ∑ j ∈ J, a j • AtomicForceWeak.softForce d s ε (x - y j) := by
    have hp := AtomicForceWeak.softened_atomic_potential_hasFDerivAt J a y s ε hs hε x
    have he : (fun z => ∑ j ∈ J, a j * RieszKernel s ε (z - y j)) =
        (fun z => ∑ j ∈ J, a j * AtomicForceWeak.softKernel d s ε (z - y j)) := by
      funext z
      simp only [RieszKernel, if_neg (ne_of_gt hε), AtomicForceWeak.softKernel]
    rw [he]
    apply (InnerProductSpace.toDual ℝ (OneParticle d)).injective
    rw [EuclideanGradient, toDual_gradient, hp.fderiv]
    rfl
  simp_rw [hg]
  exact AtomicForceWeak.softened_atomic_force_weak_uniform J a y hd s ε A ha hA hA0 hs hsd t ht
