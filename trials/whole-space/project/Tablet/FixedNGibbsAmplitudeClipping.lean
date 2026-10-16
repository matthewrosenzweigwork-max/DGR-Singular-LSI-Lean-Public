module

public import Tablet.ConfigurationCoordinateTransport
public import Tablet.FiniteGibbsCommonDensity
public import Tablet.FiniteGibbsSquaredTestTail
public import Tablet.FiniteGibbsCompactNormalizedSobolev
public import Tablet.FinitePairLocalCutoffEnergy
public import Tablet.AtomicTestClipping
public import Tablet.PairInteractionSource
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter Metric
open scoped ContDiff ENNReal NNReal Topology
noncomputable section
-- [TABLET NODE: FixedNGibbsAmplitudeClipping]
theorem FixedNGibbsAmplitudeClipping (N d : ℕ) (hN : 2 ≤ N) (hd : 3 ≤ d)
    (s B κ : ℝ) (hs : 0 < s) (hsd : s ≤ (d:ℝ)-2)
    (hB : 0 ≤ B) (hκ : 0 < κ) (Ca Mloc : ℝ → ℝ) :
    ∃ (clip : ℝ → ℝ → ℝ) (K : ℝ), 0 < K ∧
      (∀ m : ℝ, 0 < m → ContDiff ℝ ∞ (clip m) ∧ ∀ u : ℝ,
        |clip m u| ≤ 2*m ∧ |deriv (clip m) u| ≤ K ∧
        (|u| ≤ m → clip m u=u) ∧
        (u-clip m u)^2 ≤ if m < |u| then u^2 else 0) ∧
      ∀ δ : ℝ, 0 < δ → ∃ m : ℝ, 0 < m ∧
      ∀ V : OneParticle d → ℝ, PotentialBounds d κ V → (∀ x, V 0 ≤ V x) →
        (∀ R, 0 < R → ∀ x, ‖x‖ ≤ R → V x-V 0 ≤ Mloc R) →
        (∀ a, 0 < a → ∀ x, EuclideanLaplacian V x ≤ a*‖EuclideanGradient V x‖^ForceExponent s+Ca a) →
      ∀ coupling ε : ℝ, 0 ≤ coupling → coupling ≤ B → 0 < ε →
      ∀ f : ParticleConfig d N → ℝ, ContDiff ℝ 1 f → ∀ c : ℝ,
        HasCompactSupport (fun X => f X-c) →
      let P := GibbsLaw (N:=N) (ReferenceLaw V (fun _ => 1)) s coupling ε
      (∫ X, f X^2 ∂P)=1 → (∫ X, ‖EuclideanGradient f X‖^2 ∂P) ≤ 1 →
      IsProbabilityMeasure P ∧ Integrable (fun X => (f X-clip m (f X))^2) P ∧
      (∫ X, (f X-clip m (f X))^2 ∂P) < δ := by
-- BODY
  obtain ⟨clip,K,hK,hclip,hUnusedAtomicTail⟩ := AtomicTestClipping.{0} d hd s B κ hs hsd hB hκ Ca Mloc
  -- Only the scalar clip construction is projected. Its atomic tail estimate is unused.
  refine ⟨clip,K,hK,hclip,?_⟩
  have hn : 0 < N := by omega
  have hn3 : 3 ≤ N*d := hd.trans (Nat.le_mul_of_pos_left d hn)
  let p : ℝ := (SobolevExponent (N*d) hn3:ℝ)
  have hp : 2 < p := by
    have hdreal : (3:ℝ) ≤ (N*d:ℕ) := by exact_mod_cast hn3
    change 2 < 2*((N*d:ℕ):ℝ)/(((N*d:ℕ):ℝ)-2)
    apply (lt_div_iff₀ (by linarith : 0 < ((N*d:ℕ):ℝ)-2)).mpr
    linarith
  obtain ⟨G,Z,hG,hZ,hSob⟩ := FiniteGibbsCompactNormalizedSobolev N d hn hd s B κ hs hsd hB hκ Ca
  let S0 : ℝ := Z.toReal^p
  obtain ⟨C,D,hC,hD,beta,hBeta,hDensity⟩ := FiniteGibbsCommonDensity d N hd (by omega) s B κ 1 hs hsd hB hκ le_rfl Mloc
  have hone : BoundedMultiplier d 1 (fun _ => 1) := by
    refine ⟨measurable_const,1,1,zero_lt_one,le_rfl,?_,fun x => ⟨le_rfl,le_rfl⟩⟩
    norm_num
  obtain ⟨χ,Dχ,hDχ,hχ,hLocal⟩ := FinitePairLocalCutoffEnergy d N hd hN s B hs hsd hB
  intro δ hδ
  let tailTolerance : ℝ := δ/2
  have hTailTolerance : 0 < tailTolerance := by dsimp [tailTolerance]; linarith
  classical
  obtain ⟨Ctail,hCtail,hradial⟩ := FiniteGibbsSquaredTestTail N d hn hd s B κ hs hsd hB hκ Ca
  have hθ : 0 < ForceExponent s := (ForceExponentRange s hs).1
  have hlim : Tendsto (fun R : ℝ => 2*Ctail*(R^(-2:ℝ)+R^(-(ForceExponent s)))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<2)).add
      (tendsto_rpow_neg_atTop hθ)).const_mul (2*Ctail)
  have hevent : ∀ᶠ R : ℝ in atTop, 2*Ctail*(R^(-2:ℝ)+R^(-(ForceExponent s))) < tailTolerance :=
    hlim.eventually (eventually_lt_nhds hTailTolerance)
  obtain ⟨R,hR,hRate⟩ := ((eventually_gt_atTop (0:ℝ)).and hevent).exists
  have hTail : ∀ V : OneParticle d → ℝ, PotentialBounds d κ V → (∀ z, V 0 ≤ V z) →
      (∀ a : ℝ, 0 < a → ∀ z, EuclideanLaplacian V z ≤
        a*‖EuclideanGradient V z‖^(ForceExponent s)+Ca a) →
      ∀ coupling ε : ℝ, 0 ≤ coupling → coupling ≤ B → 0 < ε →
      let P := GibbsLaw (N:=N) (ReferenceLaw V (fun _ => 1)) s coupling ε
      let O := {X : ParticleConfig d N | ¬ ∀ k : Fin N × Fin d, |X k| ≤ R}
      IsProbabilityMeasure P ∧ P.real O ≤ tailTolerance ∧
      ∀ f : ParticleConfig d N → ℝ, ContDiff ℝ 1 f → ∀ c : ℝ,
      HasCompactSupport (fun X => f X-c) →
        (∫ X in O, f X^2 ∂P) ≤ (tailTolerance/2)*
          ((∫ X, ‖EuclideanGradient f X‖^2 ∂P)+∫ X, f X^2 ∂P) ∧
        ((∫ X, f X^2 ∂P)=1 → (∫ X, ‖EuclideanGradient f X‖^2 ∂P) ≤ 1 →
          (∫ X in O, f X^2 ∂P) ≤ tailTolerance) := by
    intro V hV hmin hgrowth coupling ε ha haB hε
    dsimp only
    let P := GibbsLaw (N:=N) (ReferenceLaw V (fun _ => 1)) s coupling ε
    let O := {X : ParticleConfig d N | ¬ ∀ k : Fin N × Fin d, |X k| ≤ R}
    let T := {X : ParticleConfig d N | R < ‖X‖}
    have hOT : O ⊆ T := by
      intro X hX
      by_contra hn
      apply hX
      intro k
      have hk : |X k| ≤ ‖X‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le X k
      exact hk.trans (le_of_not_gt hn)
    have hc : HasCompactSupport (fun _ : ParticleConfig d N => (1:ℝ)-1) := by
      have he : (fun _ : ParticleConfig d N => (1:ℝ)-1)=(0 : ParticleConfig d N → ℝ) := by funext X; norm_num
      rw [he]; exact HasCompactSupport.zero
    have hOne := hradial V hV hmin hgrowth coupling ε ha haB hε (fun _ => 1) contDiff_const 1 hc
    letI : IsProbabilityMeasure P := hOne.1
    have hK : 0 ≤ Ctail*(R^(-2:ℝ)+R^(-(ForceExponent s))) := by positivity
    have hhalf : Ctail*(R^(-2:ℝ)+R^(-(ForceExponent s))) ≤ tailTolerance/2 := by linarith
    have cubeTail (f : ParticleConfig d N → ℝ) (hf : ContDiff ℝ 1 f) (c : ℝ)
        (hcf : HasCompactSupport (fun X => f X-c)) :
        (∫ X in O, f X^2 ∂P) ≤ Ctail*(R^(-2:ℝ)+R^(-(ForceExponent s)))*
          ((∫ X, ‖EuclideanGradient f X‖^2 ∂P)+∫ X, f X^2 ∂P) := by
      have h := hradial V hV hmin hgrowth coupling ε ha haB hε f hf c hcf
      have hm := setIntegral_mono_set h.2.1.integrableOn
        (Eventually.of_forall fun X => sq_nonneg (f X)) (Eventually.of_forall hOT)
      exact hm.trans (h.2.2.2 R hR)
    have hProbTail : P.real O ≤ tailTolerance := by
      have h := cubeTail (fun _ => 1) contDiff_const 1 hc
      simp only [one_pow,EuclideanGradient,gradient_fun_const,norm_zero,
        zero_pow (by decide : 2≠0),integral_zero,zero_add,integral_const,smul_eq_mul,
        mul_one,probReal_univ,measureReal_restrict_apply_univ] at h
      exact h.trans (by linarith)
    refine ⟨hOne.1,hProbTail,?_⟩
    intro f hf c hcf
    have h := cubeTail f hf c hcf
    have hE : 0 ≤ (∫ X, ‖EuclideanGradient f X‖^2 ∂P)+∫ X, f X^2 ∂P :=
      add_nonneg (integral_nonneg fun X => sq_nonneg _) (integral_nonneg fun X => sq_nonneg _)
    have hb := h.trans (mul_le_mul_of_nonneg_right hhalf hE)
    refine ⟨hb,?_⟩
    intro hm he
    rw [hm] at hb
    have hcoef : 0 ≤ tailTolerance/2 := by positivity
    exact hb.trans (by nlinarith)
  let Rb : ℝ := ((N*d:ℕ)+1:ℝ)*R
  have hRb : 0 < Rb := by dsimp [Rb]; positivity
  obtain ⟨VR,SR,hVR,hSR,hLocalR⟩ := hLocal Rb hRb
  let weightedTransform (f : ParticleConfig d N → ℝ) (ρ : ParticleConfig d N → ℝ≥0) (X : ParticleConfig d N) := f X*Real.sqrt (ρ X:ℝ)
  have weighted_transform_square (f : ParticleConfig d N → ℝ) (ρ : ParticleConfig d N → ℝ≥0) (x : ParticleConfig d N) :
      weightedTransform f ρ x^2 = (ρ x : ℝ)*f x^2 := by
    dsimp [weightedTransform]
    rw [mul_pow,Real.sq_sqrt (NNReal.coe_nonneg _)]
    ring
  have weighted_transform_set_mass (μ : Measure (ParticleConfig d N))
      (f : ParticleConfig d N → ℝ) (ρ : ParticleConfig d N → ℝ≥0) (hρ : Measurable ρ)
      (S : Set (ParticleConfig d N)) (hS : MeasurableSet S) :
      (∫ x in S, f x^2 ∂μ.withDensity (fun x => ρ x)) =
        ∫ x in S, weightedTransform f ρ x^2 ∂μ := by
    rw [setIntegral_withDensity_eq_setIntegral_smul hρ _ hS]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      simpa only [NNReal.smul_def,smul_eq_mul] using (weighted_transform_square f ρ x).symm)
  have good_density_transform_threshold (f : ℝ) (ρ : ℝ≥0) (b M : ℝ)
      (_hb : 0 < b) (_hM : 0 < M) (hρ : b ≤ (ρ : ℝ)) (hf : M < |f|) :
      M*Real.sqrt b ≤ |f*Real.sqrt (ρ : ℝ)| := by
    rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul hf.le (Real.sqrt_le_sqrt hρ) (Real.sqrt_nonneg b) (abs_nonneg f)
  have high_transformed_square_bound (ψ p a : ℝ) (hp : 2 < p) (ha : 0 < a)
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
  have local_potential_markov (μ : Measure (ParticleConfig d N))
      (K : Set (ParticleConfig d N)) (hK : MeasurableSet K) (hfinite : μ K ≠ (⊤ : ℝ≥0∞))
      (U : ParticleConfig d N → ℝ) (hU : Measurable U) (hUi : IntegrableOn U K μ)
      (hUn : ∀ x ∈ K, 0 ≤ U x) (T C : ℝ) (hT : 0 < T)
      (hC : (∫ x in K, U x ∂μ) ≤ C) :
      μ.real (K ∩ {x | T < U x}) ≤ C/T := by
    let B := K ∩ {x | T < U x}
    have hB : MeasurableSet B := hK.inter (measurableSet_lt measurable_const hU)
    have hBfinite : μ B ≠ (⊤ : ℝ≥0∞) := ne_top_of_le_ne_top hfinite (measure_mono inter_subset_left)
    have hi : Integrable (B.indicator (fun _ : ParticleConfig d N => (1 : ℝ))) μ :=
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
  have weighted_test_tail_split (μ : Measure (ParticleConfig d N))
      (f : ParticleConfig d N → ℝ) (hf : Measurable f) (ρ : ParticleConfig d N → ℝ≥0) (hρ : Measurable ρ)
      (U : ParticleConfig d N → ℝ) (hU : Measurable U)
      (K : Set (ParticleConfig d N)) (hK : MeasurableSet K) (hfinite : μ K ≠ (⊤ : ℝ≥0∞))
      (hUi : IntegrableOn U K μ) (hUn : ∀ x ∈ K, 0 ≤ U x)
      (p T M b C S0 : ℝ) (hS0 : 0 ≤ S0) (hp : 2 < p) (hT : 0 < T) (hM : 0 < M) (hb : 0 < b)
      (hC : (∫ x in K, U x ∂μ) ≤ C)
      (hLower : ∀ x ∈ K, U x ≤ T → b ≤ (ρ x : ℝ))
      (hSq : Integrable (fun x => weightedTransform f ρ x^2) μ)
      (hHolder : ∀ A : Set (ParticleConfig d N), MeasurableSet A → μ A ≠ (⊤ : ℝ≥0∞) →
        (∫ x in A, weightedTransform f ρ x^2 ∂μ) ≤ S0^(2/p)*(μ.real A)^(1-2/p))
      (hMoment : Integrable (fun x => |weightedTransform f ρ x|^p) μ) :
      (∫ x in {x | M < |f x|}, f x^2 ∂μ.withDensity (fun x => ρ x)) ≤
        (∫ x in Kᶜ, f x^2 ∂μ.withDensity (fun x => ρ x)) +
        S0^(2/p)*(C/T)^(1-2/p) +
        (M*Real.sqrt b)^(2-p)*(∫ x, |weightedTransform f ρ x|^p ∂μ) := by
    let ψ := weightedTransform f ρ
    let B := K ∩ {x | T < U x}
    let A := {x | M < |f x|}
    let a := M*Real.sqrt b
    have ha : 0 < a := by dsimp [a]; positivity
    have hA : MeasurableSet A := measurableSet_lt measurable_const (continuous_abs.measurable.comp hf)
    have hB : MeasurableSet B := hK.inter (measurableSet_lt measurable_const hU)
    have hBfinite : μ B ≠ (⊤ : ℝ≥0∞) := ne_top_of_le_ne_top hfinite (measure_mono inter_subset_left)
    have hpoint (x : ParticleConfig d N) : A.indicator (fun x => ψ x^2) x ≤
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
    have hh := hHolder B hB hBfinite
    have hγ : 0 ≤ 1-2/p := by
      have hp0 : 0 < p := by linarith
      exact sub_nonneg.mpr ((div_le_one hp0).mpr hp.le)
    have hbad : (∫ x in B, ψ x^2 ∂μ) ≤
        S0^(2/p)*(C/T)^(1-2/p) :=
      hh.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (show 0 ≤ μ.real B from measureReal_nonneg) hm hγ) (by positivity))
    rw [weighted_transform_set_mass μ f ρ hρ A hA,
      weighted_transform_set_mass μ f ρ hρ Kᶜ hK.compl]
    exact h.trans (add_le_add (add_le_add le_rfl hbad) le_rfl)
  have ordered_potential_test_level_choice (p C₀ C₁ C₂ δ : ℝ) (hp : 2 < p)
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
  obtain ⟨T,m,hT,hm,hSmall⟩ := ordered_potential_test_level_choice p (S0^(2/p)) VR S0 (δ/2)
    hp (by linarith) (fun T => beta Rb T) (fun T hT => hBeta Rb T hRb hT)
  refine ⟨m,hm,?_⟩
  intro V hV hmin hlocal hgrowth coupling ε ha haB hε f hf c hcf
  dsimp only
  intro hunit henergy
  let P := GibbsLaw (N:=N) (ReferenceLaw V (fun _ => 1)) s coupling ε
  let U := PairInteraction (d:=d) (N:=N) s coupling ε
  let Q : Set (ParticleConfig d N) := {X | ∀ k, |X k| ≤ R}
  let Ball := closedBall (0:ParticleConfig d N) Rb
  obtain ⟨hZlo,hZhi,hZraw,hrawI,hrawEq,hpm,hpn,hpraw,hprob,hlaw,hupper,hlower⟩ :=
    hDensity V (fun _ => 1) hV hmin hlocal hone N (by omega) le_rfl coupling ε ha haB hε
  letI : IsProbabilityMeasure P := hprob
  let ρ : ParticleConfig d N → ℝ≥0 := fun X => ⟨GibbsLebesgueDensity (N:=N) V (fun _ => 1) s coupling ε X,hpn X⟩
  have hρ : Measurable ρ := hpm.subtype_mk
  have hP : P = volume.withDensity (fun X => (ρ X:ℝ≥0∞)) := by
    change GibbsLaw (N:=N) (ReferenceLaw V (fun _ => 1)) s coupling ε = _
    rw [hlaw]
    congr 1
    funext X
    change ENNReal.ofReal (ρ X : ℝ) = (ρ X : ℝ≥0∞)
    simp only [ENNReal.ofReal_coe_nnreal]
  obtain ⟨hprobS,hpS,hψunit,hψC,hψsq,hψgradI,hψgrad,hψLp,hMoment,hψMem,hMomentCap,hHolder⟩ :=
    hSob V hV hgrowth coupling ε ha haB hε f hf c hcf hunit henergy
  have hQ : MeasurableSet Q := by
    simp only [Q, setOf_forall]
    exact MeasurableSet.iInter (fun k => measurableSet_le ((continuous_abs.comp (PiLp.continuous_apply 2 _ k)).measurable) measurable_const)
  have hsubset : Q ⊆ Ball := by
    intro X hx
    rw [mem_closedBall,dist_zero_right]
    exact (ConfigurationCoordinateTransport N d).2.2.2.1 R hR.le X hx
  have hBall : IsCompact Ball := isCompact_closedBall _ _
  have hfinite : volume Q ≠ (⊤ : ℝ≥0∞) := ne_top_of_le_ne_top hBall.measure_ne_top (measure_mono hsubset)
  have hUC : ContDiff ℝ 1 U := by
    exact (PairInteractionSource d N s coupling ε hs hsd ha hε).1.of_le (by norm_num)
  have hUn : ∀ X, 0 ≤ U X := by
    intro X
    dsimp only [U,PairInteraction]
    apply mul_nonneg (div_nonneg ha (Nat.cast_nonneg _))
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    split_ifs
    · unfold RieszKernel
      split_ifs <;> positivity
    · rfl
  have hUi : IntegrableOn U Q volume :=
    (hUC.continuous.continuousOn.integrableOn_compact hBall).mono_set hsubset
  have hVR : (∫ X in Q, U X) ≤ VR := by
    have hi : IntegrableOn U Ball volume := hUC.continuous.continuousOn.integrableOn_compact hBall
    exact (setIntegral_mono_set hi (Eventually.of_forall hUn) (Eventually.of_forall hsubset)).trans
      (hLocalR coupling ε ha haB hε).1
  have hLow : ∀ X ∈ Q, U X ≤ T → beta Rb T ≤ (ρ X:ℝ) := by
    intro X hX hUX
    exact hlower Rb T hRb hT X ((ConfigurationCoordinateTransport N d).2.2.2.1 R hR.le X hX) (hUX.trans (by linarith))
  have ht := ((hTail V hV hmin hgrowth coupling ε ha haB hε).2.2 f hf c hcf).2 hunit henergy
  have hsplit := weighted_test_tail_split volume f hf.continuous.measurable ρ hρ U hUC.continuous.measurable
    Q hQ hfinite hUi (fun X _ => hUn X) p T m (beta Rb T) VR S0 (by dsimp [S0]; positivity) hp hT hm
    (hBeta Rb T hRb hT) hVR hLow hψsq hHolder hMoment
  have hOut : (∫ X in Qᶜ, f X^2 ∂volume.withDensity (fun X => (ρ X:ℝ≥0∞))) ≤ δ/2 := by
    rw [← hP]
    exact ht
  have hSecond := mul_le_mul_of_nonneg_left hMomentCap
    (Real.rpow_nonneg (mul_nonneg hm.le (Real.sqrt_nonneg (beta Rb T))) (2-p))
  have hTailAmp : (∫ X in {X | m < |f X|}, f X^2 ∂P) < δ := by
    rw [hP]
    have hh := hsplit.trans (add_le_add (add_le_add hOut le_rfl) hSecond)
    linarith
  have hfi := ((FiniteGibbsSquaredTestTail N d hn hd s B κ hs hsd hB hκ Ca).choose_spec.2
    V hV hmin hgrowth coupling ε ha haB hε f hf c hcf)
  have hErr : Integrable (fun X => (f X-clip m (f X))^2) P := by
    have hbound : ∀ X, ‖(f X-clip m (f X))^2‖ ≤ f X^2 := by
      intro X
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact ((hclip m hm).2 (f X)).2.2.2.trans (by split_ifs <;> nlinarith [sq_nonneg (f X)])
    exact (hfi.2.1).mono' ((hf.continuous.sub ((hclip m hm).1.continuous.comp hf.continuous)).pow 2).aestronglyMeasurable (Eventually.of_forall hbound)
  have hA : MeasurableSet {X | m < |f X|} := measurableSet_lt measurable_const (continuous_abs.measurable.comp hf.continuous.measurable)
  have hErrorLe : (∫ X, (f X-clip m (f X))^2 ∂P) ≤ ∫ X in {X | m < |f X|}, f X^2 ∂P := by
    rw [← integral_indicator hA]
    apply integral_mono hErr ((hfi.2.1).indicator hA)
    intro X
    have hh := ((hclip m hm).2 (f X)).2.2.2
    simpa only [Set.indicator,Set.mem_setOf_eq] using hh
  exact ⟨hprob,hErr,hErrorLe.trans_lt hTailAmp⟩
