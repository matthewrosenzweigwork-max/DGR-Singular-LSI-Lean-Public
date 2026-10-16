import Tablet.AtomicLawTestControls
import Tablet.AtomicLocalCutoffEnergy
import Tablet.CriticalNormControls
import Tablet.GaussianConfinementIntegral
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic
open MeasureTheory Set Filter
open scoped ContDiff NNReal Topology
set_option maxHeartbeats 1600000
noncomputable section
namespace AtomicTestClipping
private def weightedTransform {α : Type*} (f : α → ℝ) (ρ : α → ℝ≥0) (x : α) : ℝ :=
  f x*Real.sqrt (ρ x : ℝ)

private theorem weighted_transform_square {α : Type*} (f : α → ℝ) (ρ : α → ℝ≥0) (x : α) :
    weightedTransform f ρ x^2 = (ρ x : ℝ)*f x^2 := by
  dsimp [weightedTransform]
  rw [mul_pow,Real.sq_sqrt (NNReal.coe_nonneg _)]
  ring

private theorem weighted_transform_set_mass {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → ℝ) (ρ : α → ℝ≥0) (hρ : Measurable ρ)
    (S : Set α) (hS : MeasurableSet S) :
    (∫ x in S, f x^2 ∂μ.withDensity (fun x => ρ x)) =
      ∫ x in S, weightedTransform f ρ x^2 ∂μ := by
  rw [setIntegral_withDensity_eq_setIntegral_smul hρ _ hS]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    simpa only [NNReal.smul_def,smul_eq_mul] using (weighted_transform_square f ρ x).symm)

private theorem transformed_square_holder {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (ψ : α → ℝ) (p : ℝ) (hp : 2 < p)
    (hψ : MemLp (fun x => ψ x^2) (ENNReal.ofReal (p/2)) μ)
    (S : Set α) (hS : MeasurableSet S) (hfinite : μ S ≠ ⊤) :
    (∫ x in S, ψ x^2 ∂μ) ≤
      (∫ x, |ψ x|^p ∂μ)^(2/p)*(μ.real S)^(1-2/p) := by
  have hp0 : 0 < p := by linarith
  have hpm : 0 < p-2 := by linarith
  have hpq : (p/2).HolderConjugate (p/(p-2)) := by
    apply Real.holderConjugate_iff.mpr
    refine ⟨by linarith,?_⟩
    field_simp
    ring
  have hi : MemLp (S.indicator (fun _ : α => (1 : ℝ)))
      (ENNReal.ofReal (p/(p-2))) μ :=
    memLp_indicator_const _ hS _ (Or.inr hfinite)
  have hin : 0 ≤ᵐ[μ] S.indicator (fun _ : α => (1 : ℝ)) :=
    Filter.Eventually.of_forall (fun x => by simp only [Set.indicator]; split_ifs <;> norm_num)
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall (fun x => sq_nonneg (ψ x))) hin hψ hi
  have he : (fun x => ψ x^2*S.indicator (fun _ : α => (1 : ℝ)) x) =
      S.indicator (fun x => ψ x^2) := by
    funext x
    simp only [Set.indicator]
    split_ifs <;> simp
  have hexp : 1/(p/2) = 2/p := by field_simp
  have hexp' : 1/(p/(p-2)) = 1-2/p := by field_simp
  have hipow : (fun x => (S.indicator (fun _ : α => (1 : ℝ)) x)^(p/(p-2))) =
      S.indicator (fun _ : α => (1 : ℝ)) := by
    funext x
    simp only [Set.indicator]
    split_ifs <;> simp [Real.zero_rpow (ne_of_gt (div_pos hp0 hpm))]
  rw [he,integral_indicator hS,hipow,integral_indicator hS,setIntegral_const,
    smul_eq_mul,mul_one,hexp,hexp'] at h
  have hsquare (x : ℝ) : (x^2)^(p/2) = |x|^p := by
    rw [← sq_abs,← Real.rpow_natCast,← Real.rpow_mul (abs_nonneg x)]
    congr 1
    ring
  simpa only [hsquare] using h

private theorem good_density_transform_threshold (f : ℝ) (ρ : ℝ≥0) (b M : ℝ)
    (_hb : 0 < b) (_hM : 0 < M) (hρ : b ≤ (ρ : ℝ)) (hf : M < |f|) :
    M*Real.sqrt b ≤ |f*Real.sqrt (ρ : ℝ)| := by
  rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul hf.le (Real.sqrt_le_sqrt hρ) (Real.sqrt_nonneg b) (abs_nonneg f)

private theorem high_transformed_square_bound (ψ p a : ℝ) (hp : 2 < p) (ha : 0 < a)
    (hψ : a ≤ |ψ|) : ψ^2 ≤ a^(2-p)*|ψ|^p := by
  have hψp : 0 < |ψ| := ha.trans_le hψ
  have hpow : |ψ|^(2-p) ≤ a^(2-p) :=
    (Real.rpow_le_rpow_iff_of_neg hψp ha (by linarith)).mpr hψ
  have heq : ψ^2 = |ψ|^p*|ψ|^(2-p) := by
    rw [← Real.rpow_add hψp]
    simp [sq_abs]
  rw [heq]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hpow
    (Real.rpow_nonneg (abs_nonneg ψ) p)

private theorem local_potential_markov {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (K : Set α) (hK : MeasurableSet K) (hfinite : μ K ≠ ⊤)
    (U : α → ℝ) (hU : Measurable U) (hUi : IntegrableOn U K μ)
    (hUn : ∀ x ∈ K, 0 ≤ U x) (T C : ℝ) (hT : 0 < T)
    (hC : (∫ x in K, U x ∂μ) ≤ C) :
    μ.real (K ∩ {x | T < U x}) ≤ C/T := by
  let B := K ∩ {x | T < U x}
  have hB : MeasurableSet B := hK.inter (measurableSet_lt measurable_const hU)
  have hBfinite : μ B ≠ ⊤ := ne_top_of_le_ne_top hfinite (measure_mono inter_subset_left)
  have hi : Integrable (B.indicator (fun _ : α => (1 : ℝ))) μ :=
    memLp_one_iff_integrable.mp (memLp_indicator_const 1 hB _ (Or.inr hBfinite))
  have hUK : Integrable (K.indicator U) μ := (integrable_indicator_iff hK).mpr hUi
  have h := integral_mono (hi.const_mul T) hUK (fun x => by
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
      by_cases ht : T < U x
      · rw [Set.indicator_of_mem (show x ∈ B from ⟨hx,ht⟩)]
        simpa using ht.le
      · rw [Set.indicator_of_notMem (show x ∉ B by simp [B,ht])]
        simpa using hUn x hx
    · rw [Set.indicator_of_notMem hx,
        Set.indicator_of_notMem (show x ∉ B by simp [B,hx])]
      simp)
  rw [integral_const_mul,integral_indicator hB,setIntegral_const,smul_eq_mul,
    mul_one,integral_indicator hK] at h
  exact (le_div_iff₀ hT).mpr (by simpa [mul_comm] using h.trans hC)

private theorem weighted_test_tail_split {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → ℝ) (hf : Measurable f) (ρ : α → ℝ≥0) (hρ : Measurable ρ)
    (U : α → ℝ) (hU : Measurable U)
    (K : Set α) (hK : MeasurableSet K) (hfinite : μ K ≠ ⊤)
    (hUi : IntegrableOn U K μ) (hUn : ∀ x ∈ K, 0 ≤ U x)
    (p T M b C : ℝ) (hp : 2 < p) (hT : 0 < T) (hM : 0 < M) (hb : 0 < b)
    (hC : (∫ x in K, U x ∂μ) ≤ C)
    (hLower : ∀ x ∈ K, U x ≤ T → b ≤ (ρ x : ℝ))
    (hSq : Integrable (fun x => weightedTransform f ρ x^2) μ)
    (hLp : MemLp (fun x => weightedTransform f ρ x^2) (ENNReal.ofReal (p/2)) μ)
    (hMoment : Integrable (fun x => |weightedTransform f ρ x|^p) μ) :
    (∫ x in {x | M < |f x|}, f x^2 ∂μ.withDensity (fun x => ρ x)) ≤
      (∫ x in Kᶜ, f x^2 ∂μ.withDensity (fun x => ρ x)) +
      (∫ x, |weightedTransform f ρ x|^p ∂μ)^(2/p)*(C/T)^(1-2/p) +
      (M*Real.sqrt b)^(2-p)*(∫ x, |weightedTransform f ρ x|^p ∂μ) := by
  let ψ := weightedTransform f ρ
  let B := K ∩ {x | T < U x}
  let A := {x | M < |f x|}
  let a := M*Real.sqrt b
  have ha : 0 < a := by dsimp [a]; positivity
  have hA : MeasurableSet A := measurableSet_lt measurable_const (continuous_abs.measurable.comp hf)
  have hB : MeasurableSet B := hK.inter (measurableSet_lt measurable_const hU)
  have hBfinite : μ B ≠ ⊤ := ne_top_of_le_ne_top hfinite (measure_mono inter_subset_left)
  have hpoint (x : α) : A.indicator (fun x => ψ x^2) x ≤
      Kᶜ.indicator (fun x => ψ x^2) x+B.indicator (fun x => ψ x^2) x+a^(2-p)*|ψ x|^p := by
    have hn : 0 ≤ a^(2-p)*|ψ x|^p := by positivity
    by_cases hax : x ∈ A
    · rw [Set.indicator_of_mem hax]
      by_cases hkx : x ∈ K
      · rw [Set.indicator_of_notMem (show x ∉ Kᶜ from not_not.mpr hkx),zero_add]
        by_cases hux : T < U x
        · rw [Set.indicator_of_mem (show x ∈ B from ⟨hkx,hux⟩)]
          linarith
        · rw [Set.indicator_of_notMem (show x ∉ B by simp [B,hux]),zero_add]
          exact high_transformed_square_bound (ψ x) p a hp ha
            (good_density_transform_threshold (f x) (ρ x) b M hb hM
              (hLower x hkx (le_of_not_gt hux)) hax)
      · rw [Set.indicator_of_mem (show x ∈ Kᶜ from hkx)]
        have hbn : 0 ≤ B.indicator (fun x => ψ x^2) x := by
          simp only [Set.indicator]; split_ifs <;> positivity
        linarith
    · rw [Set.indicator_of_notMem hax]
      simp only [Set.indicator]
      split_ifs <;> positivity
  have hiout := hSq.indicator hK.compl
  have hibad := hSq.indicator hB
  have himom := hMoment.const_mul (a^(2-p))
  have h := integral_mono (hSq.indicator hA) ((hiout.add hibad).add himom) hpoint
  change (∫ x, A.indicator (fun x => ψ x^2) x ∂μ) ≤
    ∫ x, (Kᶜ.indicator (fun x => ψ x^2) x+B.indicator (fun x => ψ x^2) x)+a^(2-p)*|ψ x|^p ∂μ at h
  rw [integral_add
    (f := fun x => Kᶜ.indicator (fun x => ψ x^2) x+B.indicator (fun x => ψ x^2) x)
    (g := fun x => a^(2-p)*|ψ x|^p) (hiout.add hibad) himom,
    integral_add (f := Kᶜ.indicator (fun x => ψ x^2))
      (g := B.indicator (fun x => ψ x^2)) hiout hibad,
    integral_const_mul,integral_indicator hA,integral_indicator hK.compl,integral_indicator hB] at h
  have hm := local_potential_markov μ K hK hfinite U hU hUi hUn T C hT hC
  have hh := transformed_square_holder μ ψ p hp hLp B hB hBfinite
  have hγ : 0 ≤ 1-2/p := by
    have hp0 : 0 < p := by linarith
    exact sub_nonneg.mpr ((div_le_one hp0).mpr hp.le)
  have hbad : (∫ x in B, ψ x^2 ∂μ) ≤
      (∫ x, |ψ x|^p ∂μ)^(2/p)*(C/T)^(1-2/p) :=
    hh.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (show 0 ≤ μ.real B from measureReal_nonneg) hm hγ) (by positivity))
  rw [weighted_transform_set_mass μ f ρ hρ A hA,
    weighted_transform_set_mass μ f ρ hρ Kᶜ hK.compl]
  exact h.trans (add_le_add (add_le_add le_rfl hbad) le_rfl)

private theorem ordered_potential_test_level_choice (p C₀ C₁ C₂ δ : ℝ) (hp : 2 < p)
    (hδ : 0 < δ) (b : ℝ → ℝ) (hb : ∀ T, 0 < T → 0 < b T) :
    ∃ T M : ℝ, 0 < T ∧ 0 < M ∧
      C₀*(C₁/T)^(1-2/p)+(M*Real.sqrt (b T))^(2-p)*C₂ < δ := by
  have hp0 : 0 < p := by linarith
  have hγ : 0 < 1-2/p := sub_pos.mpr ((div_lt_one hp0).mpr hp)
  have hTlim : Tendsto (fun T : ℝ => C₀*(C₁/T)^(1-2/p)) atTop (nhds 0) := by
    have h := ((tendsto_id.const_div_atTop C₁).rpow_const (Or.inr hγ.le)).const_mul C₀
    convert h using 1 <;> simp [Real.zero_rpow hγ.ne']
  obtain ⟨T,hT,htsmall⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (hTlim.eventually (eventually_lt_nhds (show (0 : ℝ) < δ/2 by linarith)))).exists
  have hbT : 0 < b T := hb T hT
  have hMlim : Tendsto (fun M : ℝ => (M*Real.sqrt (b T))^(2-p)*C₂) atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (show 0 < p-2 by linarith)).mul_const
      ((Real.sqrt (b T))^(2-p)*C₂)
    have h' : Tendsto (fun M : ℝ => M^(2-p)*((Real.sqrt (b T))^(2-p)*C₂)) atTop (nhds 0) := by
      convert h using 1 <;> simp [neg_sub]
    apply h'.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with M hM
    rw [Real.mul_rpow hM (Real.sqrt_nonneg _)]
    ring
  obtain ⟨M,hM,hmsmall⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (hMlim.eventually (eventually_lt_nhds (show (0 : ℝ) < δ/2 by linarith)))).exists
  exact ⟨T,M,hT,hM,by linarith⟩


private def scalarBump : ContDiffBump (0 : ℝ) :=
  { rIn := 1, rOut := 2, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }

private theorem scalar_bump_smooth : ContDiff ℝ ∞ (scalarBump : ℝ → ℝ) := scalarBump.contDiff

private theorem scalar_bump_one (x : ℝ) (hx : |x| ≤ 1) : scalarBump x = 1 := by
  apply scalarBump.one_of_mem_closedBall
  simpa [scalarBump,Real.dist_eq] using hx

private theorem scalar_bump_zero (x : ℝ) (hx : 2 ≤ |x|) : scalarBump x = 0 := by
  apply scalarBump.zero_of_le_dist
  simpa [scalarBump,Real.dist_eq] using hx

private theorem scalar_bump_derivative_bound : ∃ C : ℝ, 0 < C ∧ ∀ x, |deriv scalarBump x| ≤ C := by
  have hs : HasCompactSupport (scalarBump : ℝ → ℝ) := scalarBump.hasCompactSupport
  obtain ⟨C,hC⟩ := (scalar_bump_smooth.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).continuous_deriv_one
    |>.bounded_above_of_compact_support hs.deriv
  refine ⟨max 1 C,by positivity,?_⟩
  intro x
  exact (show |deriv scalarBump x| ≤ C by simpa using hC x).trans (le_max_right _ _)

private def smoothClip (M x : ℝ) : ℝ := x*scalarBump (x/M)

private theorem smooth_clip_smooth (M : ℝ) : ContDiff ℝ ∞ (smoothClip M) :=
  contDiff_id.mul (scalar_bump_smooth.comp (contDiff_id.div_const M))

private theorem smooth_clip_bound (M x : ℝ) (hM : 0 < M) : |smoothClip M x| ≤ 2*M := by
  by_cases hx : |x| ≤ 2*M
  · rw [smoothClip,abs_mul,abs_of_nonneg scalarBump.nonneg]
    exact (mul_le_of_le_one_right (abs_nonneg x) scalarBump.le_one).trans hx
  · have hbig : 2 ≤ |x/M| := by
      rw [abs_div,abs_of_pos hM]
      exact (le_div_iff₀ hM).mpr (le_of_lt (lt_of_not_ge hx))
    rw [smoothClip,scalar_bump_zero _ hbig,mul_zero,abs_zero]
    positivity

private theorem smooth_clip_error (M x : ℝ) (hM : 0 < M) :
    (x-smoothClip M x)^2 ≤ (if M < |x| then x^2 else 0) := by
  by_cases hx : M < |x|
  · rw [if_pos hx]
    have hn : 0 ≤ scalarBump (x/M) := scalarBump.nonneg
    have hu : scalarBump (x/M) ≤ 1 := scalarBump.le_one
    have hfactor : (1-scalarBump (x/M))^2 ≤ 1 := by nlinarith
    have heq : (x-smoothClip M x)^2 = x^2*(1-scalarBump (x/M))^2 := by dsimp [smoothClip]; ring
    rw [heq]
    exact mul_le_of_le_one_right (sq_nonneg x) hfactor
  · have hsmall : |x/M| ≤ 1 := by
      rw [abs_div,abs_of_pos hM]
      exact (div_le_one hM).mpr (le_of_not_gt hx)
    rw [if_neg hx,smoothClip,scalar_bump_one _ hsmall]
    simp

private theorem scalar_bump_scaled_derivative_bound (C : ℝ) (hC : 0 < C)
    (hd : ∀ x, |deriv scalarBump x| ≤ C) (x : ℝ) : |x*deriv scalarBump x| ≤ 2*C := by
  by_cases hx : |x| ≤ 2
  · rw [abs_mul]
    exact mul_le_mul hx (hd x) (abs_nonneg _) (by norm_num)
  · have hn : x ∉ tsupport (scalarBump : ℝ → ℝ) := by
      rw [scalarBump.tsupport_eq]
      simpa [scalarBump,Real.dist_eq] using hx
    rw [deriv_of_notMem_tsupport hn,mul_zero,abs_zero]
    positivity

private theorem smooth_clip_deriv (M x : ℝ) :
    deriv (smoothClip M) x = scalarBump (x/M)+(x/M)*deriv scalarBump (x/M) := by
  have hb := (scalar_bump_smooth.differentiable (by simp) (x/M)).hasDerivAt
  have h := (hasDerivAt_id x).mul (hb.comp x ((hasDerivAt_id x).div_const M))
  have heq : ((id : ℝ → ℝ) * ((scalarBump : ℝ → ℝ) ∘ fun u => id u/M)) = smoothClip M := rfl
  rw [heq] at h
  rw [h.deriv]
  simp only [Function.comp_def,id_eq,one_mul]
  ring

private theorem smooth_clip_derivative_gain (C : ℝ) (hC : 0 < C)
    (hd : ∀ x, |deriv scalarBump x| ≤ C) (M x : ℝ) :
    |deriv (smoothClip M) x| ≤ 1+2*C := by
  rw [smooth_clip_deriv]
  calc
    _ ≤ |scalarBump (x/M)|+|(x/M)*deriv scalarBump (x/M)| := abs_add_le _ _
    _ ≤ 1+2*C := add_le_add (by rw [abs_of_nonneg scalarBump.nonneg]; exact scalarBump.le_one)
      (scalar_bump_scaled_derivative_bound C hC hd _)


private theorem cube_norm_bound (d : ℕ) (R : ℝ) (hR : 0 < R)
    (x : OneParticle d) (hx : ∀ i, |x i| ≤ R) : ‖x‖ ≤ (d : ℝ)*R+1 := by
  have hs : ‖x‖^2 ≤ (d : ℝ)*R^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      ∑ i : Fin d, (x i)^2 ≤ ∑ _i : Fin d, R^2 := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hx i) 2
      _ = (d : ℝ)*R^2 := by simp
  have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hd1 : (d : ℝ) ≤ (d : ℝ)^2 := by
    have h : d = 0 ∨ 1 ≤ d := Nat.eq_zero_or_pos d
    rcases h with h | h
    · simp [h]
    · have h' : (1 : ℝ) ≤ d := by exact_mod_cast h
      nlinarith
  have hmul := mul_le_mul_of_nonneg_right hd1 (sq_nonneg R)
  have hn : ‖x‖ ≤ (d : ℝ)*R :=
    (sq_le_sq₀ (norm_nonneg x) (by positivity)).mp (by
      simpa [mul_pow] using hs.trans hmul)
  linarith
end AtomicTestClipping
open AtomicTestClipping

-- [TABLET NODE: AtomicTestClipping]
theorem AtomicTestClipping (d : ℕ) (hd : 3 ≤ d) (s A κ : ℝ)
    (hs : 0 < s) (hsd : s ≤ (d : ℝ)-2) (hA : 0 ≤ A) (hκ : 0 < κ)
    (Ca Mloc : ℝ → ℝ) :
    ∃ (clip : ℝ → ℝ → ℝ) (K : ℝ), 0 < K ∧
      (∀ m : ℝ, 0 < m → ContDiff ℝ ∞ (clip m) ∧ ∀ u : ℝ,
        |clip m u| ≤ 2*m ∧ |deriv (clip m) u| ≤ K ∧
        (|u| ≤ m → clip m u = u) ∧
        (u-clip m u)^2 ≤ if m < |u| then u^2 else 0) ∧
      ∀ δ : ℝ, 0 < δ → ∃ m : ℝ, 0 < m ∧
      ∀ V : OneParticle d → ℝ, PotentialBounds d κ V →
        (∀ x, V 0 ≤ V x) →
        (∀ R : ℝ, 0 < R → ∀ x, ‖x‖ ≤ R → V x-V 0 ≤ Mloc R) →
        (∀ a : ℝ, 0 < a → ∀ x, EuclideanLaplacian V x ≤
          a*‖EuclideanGradient V x‖^(2/(s+1))+Ca a) →
      ∀ {ι : Type*} (J : Finset ι) (charges : ι → ℝ) (y : ι → OneParticle d) (ε : ℝ),
        (∀ j ∈ J, 0 ≤ charges j) → (∑ j ∈ J, charges j ≤ A) → 0 < ε →
        let U := fun x => ∑ j ∈ J, charges j*RieszKernel s ε (x-y j)
        let P := ReferenceLaw (fun x => V x+U x) (fun _ => 1)
        ∀ f : OneParticle d → ℝ, ContDiff ℝ 1 f → ∀ c : ℝ,
          HasCompactSupport (fun x => f x-c) →
          (∫ x, f x^2 ∂P) = 1 → (∫ x, ‖EuclideanGradient f x‖^2 ∂P) ≤ 1 →
          (∫ x in {x | m < |f x|}, f x^2 ∂P) < δ ∧
          Integrable (fun x => (f x-clip m (f x))^2) P ∧
          (∫ x, (f x-clip m (f x))^2 ∂P) < δ := by
-- BODY
  obtain ⟨D, hD, hder⟩ := scalar_bump_derivative_bound
  refine ⟨smoothClip, 1+2*D, by positivity, ?_, ?_⟩
  · intro m hm
    refine ⟨smooth_clip_smooth m, fun u => ⟨smooth_clip_bound m u hm,
      smooth_clip_derivative_gain D hD hder m u, ?_, smooth_clip_error m u hm⟩⟩
    intro hu
    have hu' : |u/m| ≤ 1 := by
      rw [abs_div, abs_of_pos hm]
      exact (div_le_one hm).mpr hu
    simp [smoothClip, scalar_bump_one _ hu']
  obtain ⟨H, G, C, T, hH, hG, hC, hT, hcontrols⟩ :=
    AtomicLawTestControls d hd s A κ (Mloc 1) hs hsd hA hκ Ca
  obtain ⟨χ, D', hD', hχ, hlocal⟩ := AtomicLocalCutoffEnergy d hd s A hs hsd hA
  let p : ℝ := SobolevExponent d hd
  have hp : 2 < p := by
    have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
    change 2 < 2*(d : ℝ)/((d : ℝ)-2)
    apply (lt_div_iff₀ (show 0 < (d : ℝ)-2 by linarith)).mpr
    linarith
  let S : ℝ := T.toReal^p
  have hS : 0 ≤ S := by dsimp [S]; positivity
  intro δ hδ
  have hdecay : Tendsto (fun R : ℝ => 2*C*(R^(-2 : ℝ)+R^(-(2/(s+1)))))
      atTop (nhds 0) := by
    have ha := tendsto_rpow_neg_atTop (show (0 : ℝ) < 2 by norm_num)
    have hb := tendsto_rpow_neg_atTop (show (0 : ℝ) < 2/(s+1) by positivity)
    convert (ha.add hb).const_mul (2*C) using 1 <;> simp
  obtain ⟨R, hR, hsmall⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (hdecay.eventually (eventually_lt_nhds (show (0 : ℝ) < δ/2 by positivity)))).exists
  obtain ⟨VR, SR, hVR, hSR, hpot⟩ := hlocal R hR
  let radius : ℝ := (d : ℝ)*R+1
  have hradius : 0 < radius := by dsimp [radius]; positivity
  let Zg := ∫ x : OneParticle d, Real.exp (-(κ/2)*‖x‖^2)
  have hZg : 0 < Zg := (GaussianConfinementIntegral (ι := Fin d) κ hκ).2.2
  let b := fun t : ℝ => Real.exp (-Mloc radius-t)/Zg
  have hb : ∀ t : ℝ, 0 < t → 0 < b t := fun t _ => div_pos (Real.exp_pos _) hZg
  obtain ⟨t, m, ht, hm, hchoice⟩ := ordered_potential_test_level_choice
    p (S^(2/p)) VR S (δ/2) hp (by positivity) b hb
  refine ⟨m, hm, ?_⟩
  intro V hV hmin hM hgrowth ι J charges y ε ha hmass hε
  let U := fun x => ∑ j ∈ J, charges j*RieszKernel s ε (x-y j)
  let W := fun x => V x+U x
  let P := ReferenceLaw W (fun _ => 1)
  let r := (ReferencePartition W (fun _ => 1))⁻¹
  let density := fun x => r*Real.exp (-W x)
  let ρ := fun x => Real.toNNReal (density x)
  have hdata := hcontrols V hV hmin (hM 1 (by norm_num)) hgrowth J charges y ε ha hmass hε
  dsimp only at hdata
  rcases hdata with ⟨hZ, hr, hoffZ, hoffLaw, hpm, hpp, hprob, hP,
    hρ, hρeq, hPρ, hupper, hlower, hint, hptail, htest⟩
  dsimp only
  intro f hf c hc hunit henergy
  obtain ⟨hfsq, hfenergy, htrans⟩ := htest f hf c hc
  rcases htrans hunit henergy with ⟨hψeq, hψunit, hψ, hψsq, hψG, hψcap, hψnorm, htail⟩
  let ψ := weightedTransform f ρ
  have heq : ψ = fun x => f x*Real.sqrt (density x) := by
    funext x
    change f x*Real.sqrt (ρ x : ℝ) = f x*Real.sqrt (density x)
    rw [hρeq]
  have hnorm := CriticalNormControls volume (SobolevExponent d hd) hp T hT
    (fun x => f x*Real.sqrt (density x)) hψ.continuous.aestronglyMeasurable hψnorm
  change Integrable (fun x => |f x*Real.sqrt (density x)|^p) volume ∧
    MemLp (fun x => (f x*Real.sqrt (density x))^2) (ENNReal.ofReal (p/2)) volume ∧
    (∫ x, |f x*Real.sqrt (density x)|^p) ≤ S ∧ _ at hnorm
  have himoment : Integrable (fun x => |ψ x|^p) volume := by rw [heq]; exact hnorm.1
  have hLp : MemLp (fun x => ψ x^2) (ENNReal.ofReal (p/2)) volume := by
    rw [heq]; exact hnorm.2.1
  have hmoment : (∫ x, |ψ x|^p) ≤ S := by rw [heq]; exact hnorm.2.2.1
  have hisq : Integrable (fun x => ψ x^2) volume := by rw [heq]; exact hψsq
  let Q := {x : OneParticle d | ∀ k : Fin d, |x k| ≤ R}
  have hQcompact : IsCompact Q := by
    have h := (isCompact_univ_pi (fun _ : Fin d => isCompact_Icc (a := -R) (b := R))).image
      (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous
    convert h using 1
    ext x
    change (∀ k : Fin d, |x k| ≤ R) ↔
      ∃ q ∈ Set.pi Set.univ (fun _ : Fin d => Set.Icc (-R) R), WithLp.toLp 2 q = x
    constructor
    · intro hx
      refine ⟨x.ofLp, ?_, rfl⟩
      simpa only [Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Icc, abs_le] using hx
    · rintro ⟨q, hq, hqx⟩
      rw [← hqx]
      simpa only [WithLp.ofLp_toLp, Set.mem_pi, Set.mem_univ, forall_true_left,
        Set.mem_Icc, abs_le] using hq
  have hQ : MeasurableSet Q := hQcompact.isClosed.measurableSet
  have hU := (AtomicInteractionSource d s ε hs hsd hε J charges y ha).1
  have hUn : ∀ x, 0 ≤ U x := by
    intro x
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (ha j hj) ((RieszKernelBounds s ε hs hε.le).1 _)
  have hUi : IntegrableOn U Q volume := hU.continuous.continuousOn.integrableOn_compact hQcompact
  have hVRbound : (∫ x in Q, U x) ≤ VR := by
    have h := (hpot J charges y ε hε ha hmass).1
    simpa only [Q, abs_le] using h
  have hlow : ∀ x ∈ Q, U x ≤ t → b t ≤ (ρ x : ℝ) := by
    intro x hx hu
    rw [hρeq]
    exact hlower radius (Mloc radius) t (hM radius hradius) x
      (cube_norm_bound d R hR x hx) hu
  have hsplit := weighted_test_tail_split volume f hf.continuous.measurable ρ hρ
    U hU.continuous.measurable Q hQ hQcompact.measure_lt_top.ne hUi
    (fun x _ => hUn x) p t m (b t) VR hp ht hm (hb t ht) hVRbound hlow hisq hLp himoment
  have htail' : (∫ x in Qᶜ, f x^2 ∂P) ≤ 2*C*(R^(-2 : ℝ)+R^(-(2/(s+1)))) := by
    simpa only [Q, compl_ofPred] using htail R hR
  have hpow : (∫ x, |ψ x|^p)^(2/p) ≤ S^(2/p) :=
    Real.rpow_le_rpow (integral_nonneg (fun _ => Real.rpow_nonneg (abs_nonneg _) _))
      hmoment (by positivity)
  have hfirst := mul_le_mul_of_nonneg_right hpow
    (Real.rpow_nonneg (div_nonneg hVR ht.le) (1-2/p))
  have hsecond := mul_le_mul_of_nonneg_left hmoment
    (Real.rpow_nonneg (mul_nonneg hm.le (Real.sqrt_nonneg (b t))) (2-p))
  rw [hPρ] at hsplit
  have htailm : (∫ x in {x | m < |f x|}, f x^2 ∂P) < δ := by
    dsimp [ψ] at hfirst hsecond
    linarith
  have hErrM : Measurable (fun x => (f x-smoothClip m (f x))^2) :=
    (hf.continuous.measurable.sub ((smooth_clip_smooth m).continuous.measurable.comp
      hf.continuous.measurable)).pow_const 2
  have hErr : Integrable (fun x => (f x-smoothClip m (f x))^2) P :=
    hfsq.mono' hErrM.aestronglyMeasurable (Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h := smooth_clip_error m (f x) hm
      split_ifs at h with hx
      · exact h
      · exact h.trans (sq_nonneg _)))
  have hset : MeasurableSet {x | m < |f x|} :=
    measurableSet_lt measurable_const hf.continuous.abs.measurable
  have herrle := integral_mono hErr (hfsq.indicator hset) (fun x => by
    simpa only [Set.indicator, Set.mem_ofPred_eq] using smooth_clip_error m (f x) hm)
  rw [integral_indicator hset] at herrle
  exact ⟨htailm, hErr, herrle.trans_lt htailm⟩
