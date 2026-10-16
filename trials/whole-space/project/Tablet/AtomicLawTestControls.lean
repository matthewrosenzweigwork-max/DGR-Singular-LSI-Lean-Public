import Tablet.AtomicReferenceDensity
import Tablet.AtomicNormalizedSobolev
import Tablet.AtomicSquaredTestTail
import Tablet.HessianMinimizer
import Mathlib.Tactic
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
set_option maxHeartbeats 1600000

namespace AtomicLawTestControls
private theorem offset_partition {d : ℕ} (W : OneParticle d → ℝ) (c : ℝ) :
    ReferencePartition (fun x => W x - c) (fun _ => 1) =
      Real.exp c * ReferencePartition W (fun _ => 1) := by
  unfold ReferencePartition
  simp only [one_mul]
  have he : (fun x => Real.exp (-(W x-c))) = fun x => Real.exp c * Real.exp (-W x) := by
    funext x
    rw [neg_sub, sub_eq_add_neg, Real.exp_add]
  rw [he]
  rw [integral_const_mul]

private theorem offset_density {d : ℕ} (W : OneParticle d → ℝ) (c : ℝ) (x : OneParticle d) :
    (ReferencePartition (fun z => W z - c) (fun _ => 1))⁻¹ * Real.exp (-(W x - c)) =
      (ReferencePartition W (fun _ => 1))⁻¹ * Real.exp (-W x) := by
  rw [offset_partition, mul_inv_rev, neg_sub, sub_eq_add_neg, Real.exp_add]
  have h := Real.exp_ne_zero c
  field_simp

private theorem actual_integral {d : ℕ} (W : OneParticle d → ℝ) (hW : Continuous W)
    (hZ : 0 < ReferencePartition W (fun _ => 1))
    (g : OneParticle d → ℝ) (S : Set (OneParticle d)) (hS : MeasurableSet S) :
    (∫ x in S, g x ∂ReferenceLaw W (fun _ => 1)) =
      (ReferencePartition W (fun _ => 1))⁻¹ * ∫ x in S, g x * Real.exp (-W x) := by
  unfold ReferenceLaw
  rw [restrict_withDensity hS]
  have hm : Measurable (fun x => ENNReal.ofReal
      ((ReferencePartition W (fun _ => 1))⁻¹ * (1 * Real.exp (-W x)))) := by
    fun_prop
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.mpr hZ.le)
    (mul_nonneg zero_le_one (Real.exp_pos _).le)), smul_eq_mul, one_mul]
  have he : (fun x => (ReferencePartition W (fun _ => 1))⁻¹ * Real.exp (-W x) * g x) =
      fun x => (ReferencePartition W (fun _ => 1))⁻¹ * (g x * Real.exp (-W x)) := by
    funext x; ring
  rw [he, integral_const_mul]

private theorem test_integrable {d : ℕ} (P : Measure (OneParticle d)) [IsFiniteMeasure P]
    (f : OneParticle d → ℝ) (hf : ContDiff ℝ 1 f) (c : ℝ)
    (hc : HasCompactSupport (fun x => f x - c)) :
    Integrable (fun x => f x^2) P ∧ Integrable (fun x => ‖EuclideanGradient f x‖^2) P := by
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuous (hf.continuous.sub continuous_const)
  let F := max 0 B + |c|
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hfb (x) : |f x| ≤ F := by
    have hb : |f x-c| ≤ B := by simpa only [Real.norm_eq_abs] using hB x
    have hh := abs_add_le (f x-c) c
    rw [sub_add_cancel] at hh
    dsimp [F]; linarith [le_max_right (0 : ℝ) B]
  have hd : ContDiff ℝ 1 (fun x => f x-c) := hf.sub contDiff_const
  obtain ⟨G, hG⟩ := (hc.fderiv ℝ).exists_bound_of_continuous
    (hd.continuous_fderiv (by norm_num))
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
  have hgb (x) : ‖EuclideanGradient f x‖ ≤ G := by
    have h := hG x
    rw [fderiv_sub_const c] at h
    simpa only [(GradientNormIdentity f x).2] using h
  have hg : Continuous (EuclideanGradient f) :=
    (InnerProductSpace.toDual ℝ (OneParticle d)).symm.continuous.comp
      (hf.continuous_fderiv (by norm_num))
  constructor
  · apply (integrable_const (F^2)).mono' (hf.continuous.pow 2).aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      change |f x^2| ≤ F^2
      rw [abs_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hfb x) 2
  · apply (integrable_const (G^2)).mono' (hg.norm.pow 2).aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hgb x) 2
end AtomicLawTestControls
open AtomicLawTestControls

-- [TABLET NODE: AtomicLawTestControls]
theorem AtomicLawTestControls (d : ℕ) (hd : 3 ≤ d) (s A κ M1 : ℝ)
    (hs : 0 < s) (hsd : s ≤ (d : ℝ) - 2) (hA : 0 ≤ A) (hκ : 0 < κ)
    (Ca : ℝ → ℝ) :
    ∃ (H G C : ℝ) (T : ℝ≥0∞), 0 < H ∧ 0 ≤ G ∧ 0 < C ∧ T < ⊤ ∧
    ∀ V : OneParticle d → ℝ, PotentialBounds d κ V →
      (∀ x, V 0 ≤ V x) → (∀ x, ‖x‖ ≤ 1 → V x - V 0 ≤ M1) →
      (∀ a : ℝ, 0 < a → ∀ x, EuclideanLaplacian V x ≤
        a * ‖EuclideanGradient V x‖ ^ (2 / (s + 1)) + Ca a) →
    ∀ {ι : Type*} (J : Finset ι) (charges : ι → ℝ) (y : ι → OneParticle d) (ε : ℝ),
      (∀ j ∈ J, 0 ≤ charges j) → (∑ j ∈ J, charges j ≤ A) → 0 < ε →
      let U := fun x => ∑ j ∈ J, charges j * RieszKernel s ε (x - y j)
      let W := fun x => V x + U x
      let r := (ReferencePartition W (fun _ => 1))⁻¹
      let p := fun x => r * Real.exp (-W x)
      let P := ReferenceLaw W (fun _ => 1)
      0 < ReferencePartition W (fun _ => 1) ∧ 0 < r ∧
      ReferencePartition (fun x => W x - V 0) (fun _ => 1) =
        Real.exp (V 0) * ReferencePartition W (fun _ => 1) ∧
      ReferenceLaw (fun x => W x - V 0) (fun _ => 1) = P ∧
      Measurable p ∧ (∀ x, 0 < p x) ∧ IsProbabilityMeasure P ∧
      volume.withDensity (fun x => ENNReal.ofReal (p x)) = P ∧
      Measurable (fun x => Real.toNNReal (p x)) ∧
      (∀ x, (Real.toNNReal (p x) : ℝ) = p x) ∧
      volume.withDensity (fun x => (Real.toNNReal (p x) : ℝ≥0∞)) = P ∧
      (∀ x, p x ≤ H * Real.exp (-(κ / 2) * ‖x‖^2)) ∧
      (∀ R MR t : ℝ, (∀ x, ‖x‖ ≤ R → V x - V 0 ≤ MR) →
        ∀ x, ‖x‖ ≤ R → U x ≤ t →
        Real.exp (-MR-t) / (∫ z : OneParticle d, Real.exp (-(κ / 2) * ‖z‖^2)) ≤ p x) ∧
      (∀ (g : OneParticle d → ℝ) (S : Set (OneParticle d)), MeasurableSet S →
        (∫ x in S, g x ∂P) = r * ∫ x in S, g x * Real.exp (-W x)) ∧
      (∀ R : ℝ, 0 < R →
        P.real {x | ¬ ∀ k : Fin d, |x k| ≤ R} ≤ C * (R^(-2 : ℝ)+R^(-(2/(s+1))))) ∧
      ∀ f : OneParticle d → ℝ, ContDiff ℝ 1 f → ∀ c : ℝ,
        HasCompactSupport (fun x => f x-c) →
        Integrable (fun x => f x^2) P ∧ Integrable (fun x => ‖EuclideanGradient f x‖^2) P ∧
        ((∫ x, f x^2 ∂P) = 1 → (∫ x, ‖EuclideanGradient f x‖^2 ∂P) ≤ 1 →
          let ψ := fun x => f x * Real.sqrt (p x)
          ψ = (fun x => Real.sqrt r * (f x * Real.exp (-W x / 2))) ∧
          (∫ x, ψ x^2) = 1 ∧ ContDiff ℝ 1 ψ ∧
          Integrable (fun x => ψ x^2) volume ∧
          Integrable (fun x => ‖EuclideanGradient ψ x‖^2) volume ∧
          (∫ x, ‖EuclideanGradient ψ x‖^2) ≤ G ∧
          eLpNorm ψ (SobolevExponent d hd) volume ≤ T ∧
          ∀ R : ℝ, 0 < R →
            (∫ x in {x | ¬ ∀ k : Fin d, |x k| ≤ R}, f x^2 ∂P) ≤
              2*C*(R^(-2 : ℝ)+R^(-(2/(s+1))))) := by
-- BODY
  obtain ⟨D, H, hD, hH, hdensity⟩ := AtomicReferenceDensity d hd s A κ M1 hs hsd hA hκ
  obtain ⟨G, T, hG, hT, hsob⟩ := AtomicNormalizedSobolev d hd s A κ hs hsd hA hκ Ca
  obtain ⟨C, hC, htail⟩ := AtomicSquaredTestTail d hd s A κ hs hsd hA hκ Ca
  refine ⟨H, G, C, T, hH, hG, hC, hT, ?_⟩
  intro V hV hmin hlocal hgrowth ι J charges y ε ha hmass hε
  let U := fun x => ∑ j ∈ J, charges j * RieszKernel s ε (x-y j)
  let W := fun x => V x+U x
  let Vn := fun x => V x-V 0
  let Wn := fun x => Vn x+U x
  let r := (ReferencePartition W (fun _ => 1))⁻¹
  let p := fun x => r * Real.exp (-W x)
  let P := ReferenceLaw W (fun _ => 1)
  have hn (x) : Wn x = W x-V 0 := by dsimp [Wn, Vn, W]; ring
  have hU : ContDiff ℝ 2 U := (AtomicInteractionSource d s ε hs hsd hε J charges y ha).1
  have hW : Continuous W := hV.regularity.continuous.add hU.continuous
  obtain ⟨a, _, huniq, _, hquad, _⟩ := (HessianMinimizer V κ hκ hV).2
  have hz : (0 : OneParticle d) = a := huniq 0 hmin
  subst a
  have hq (x) : κ/2*‖x‖^2 ≤ Vn x := by
    have h := hquad x
    simp only [sub_zero] at h
    dsimp [Vn]; linarith
  have hnV : Continuous Vn := hV.regularity.continuous.sub continuous_const
  have hb := hdensity Vn hnV hq hlocal J charges y ε hε ha hmass
  dsimp only at hb
  rcases hb with ⟨_, _, _, _, _, hiWn, hZn, _, hprob, _, hupper, hlower⟩
  have hZscale : ReferencePartition Wn (fun _ => 1) =
      Real.exp (V 0)*ReferencePartition W (fun _ => 1) := by
    have he : Wn = fun x => W x-V 0 := funext hn
    rw [he]; exact offset_partition W (V 0)
  change 0 < ReferencePartition Wn (fun _ => 1) at hZn
  have hZ : 0 < ReferencePartition W (fun _ => 1) := by
    rw [hZscale] at hZn
    exact (mul_pos_iff.mp hZn).elim (fun h => h.2)
      (fun h => False.elim (not_lt_of_ge (Real.exp_pos _).le h.1))
  have hr : 0 < r := inv_pos.mpr hZ
  have hp (x) : (ReferencePartition Wn (fun _ => 1))⁻¹ * Real.exp (-Wn x) = p x := by
    have he : Wn = fun x => W x-V 0 := funext hn
    rw [he]; exact offset_density W (V 0) x
  have hLaw : ReferenceLaw Wn (fun _ => 1) = P := by
    unfold ReferenceLaw
    simp only [one_mul]
    congr 1
    funext x
    simpa only [one_mul] using congrArg ENNReal.ofReal (hp x)
  haveI : IsProbabilityMeasure P := by rwa [hLaw] at hprob
  have hint := actual_integral W hW hZ
  have hall (g : OneParticle d → ℝ) : (∫ x, g x ∂P) = r*∫ x, g x*Real.exp (-W x) := by
    simpa [P, r] using hint g Set.univ MeasurableSet.univ
  have hcube (R : ℝ) : {x : OneParticle d | ¬ ∀ k : Fin d, |x k| ≤ R} ⊆
      {x : OneParticle d | R < ‖x‖} := by
    intro x hx
    by_contra hnrm
    apply hx
    intro k
    have hk : |x k| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x k
    exact hk.trans (le_of_not_gt hnrm)
  have hcubeM (R : ℝ) : MeasurableSet {x : OneParticle d | ¬ ∀ k : Fin d, |x k| ≤ R} := by
    apply MeasurableSet.compl
    have he : {x : OneParticle d | ∀ k : Fin d, |x k| ≤ R} =
        ⋂ k : Fin d, {x : OneParticle d | |x k| ≤ R} := by ext x; simp
    change MeasurableSet {x : OneParticle d | ∀ k : Fin d, |x k| ≤ R}
    rw [he]
    exact MeasurableSet.iInter fun k => measurableSet_le (by fun_prop) measurable_const
  have hradM (R : ℝ) : MeasurableSet {x : OneParticle d | R < ‖x‖} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  have tail (f : OneParticle d → ℝ) (hf : ContDiff ℝ 1 f) (c : ℝ)
      (hc : HasCompactSupport (fun x => f x-c)) (R : ℝ) (hR : 0 < R) :
      (∫ x in {x | ¬ ∀ k : Fin d, |x k| ≤ R}, f x^2 ∂P) ≤
        C*(R^(-2 : ℝ)+R^(-(2/(s+1)))) *
          ((∫ x, ‖EuclideanGradient f x‖^2 ∂P)+(∫ x, f x^2 ∂P)) := by
    have h := htail V hV hmin hgrowth J charges y ε ha hmass hε r hr.le f hf c hc R hR
    dsimp only at h
    simp only [integral_const_mul] at h
    have hconvert := hint (fun x => f x^2) _ (hradM R)
    change (∫ x in {x : OneParticle d | R < ‖x‖}, f x^2 ∂P) =
      r * ∫ x in {x : OneParticle d | R < ‖x‖}, f x^2 * Real.exp (-W x) at hconvert
    have hi := (test_integrable P f hf c hc).1
    have hmono := setIntegral_mono_set hi.integrableOn (Eventually.of_forall fun x => sq_nonneg (f x))
      (Filter.Eventually.of_forall (hcube R))
    apply hmono.trans
    change (∫ x in {x : OneParticle d | R < ‖x‖}, f x^2 ∂P) ≤ _
    rw [hconvert, hall (fun x => ‖EuclideanGradient f x‖^2), hall (fun x => f x^2)]
    simpa only [mul_add, mul_assoc] using h
  dsimp only
  refine ⟨hZ, hr, offset_partition W (V 0), ?_, ?_, ?_, inferInstance,
    by simp [ReferenceLaw, p, P, r], ?_, ?_, ?_, ?_, ?_, hint, ?_, ?_⟩
  · have he : Wn = fun x => W x-V 0 := funext hn
    rw [he] at hLaw
    exact hLaw
  · exact measurable_const.mul hW.measurable.neg.exp
  · intro x; exact mul_pos hr (Real.exp_pos _)
  · exact (measurable_const.mul hW.measurable.neg.exp).real_toNNReal
  · intro x; exact Real.coe_toNNReal _ (mul_pos hr (Real.exp_pos _)).le
  · simpa only [ENNReal.ofReal] using
      (show volume.withDensity (fun x => ENNReal.ofReal (p x)) = P by
        simp [ReferenceLaw, p, P, r])
  · intro x
    change p x ≤ _
    rw [← hp]; exact hupper x
  · intro R MR t hloc x hx ht
    change _ ≤ p x
    rw [← hp]; exact hlower R MR t hloc x hx ht
  · intro R hR
    have hc : HasCompactSupport (fun _ : OneParticle d => (1 : ℝ)-1) := by
      have he : (fun _ : OneParticle d => (1 : ℝ)-1) = (0 : OneParticle d → ℝ) := by
        funext x; norm_num
      rw [he]; exact HasCompactSupport.zero
    have h := tail (fun _ => 1) contDiff_const 1 hc R hR
    simpa only [one_pow, EuclideanGradient, gradient_fun_const, norm_zero,
      zero_pow (by decide : 2 ≠ 0), integral_zero, zero_add, integral_const, smul_eq_mul,
      mul_one, probReal_univ, measureReal_restrict_apply_univ] using h
  · intro f hf c hc
    refine ⟨(test_integrable P f hf c hc).1, (test_integrable P f hf c hc).2, ?_⟩
    intro hunit henergy
    let ψ := fun x => f x * Real.sqrt (p x)
    have heq : ψ = fun x => Real.sqrt r*(f x*Real.exp (-W x/2)) := by
      funext x
      have he : Real.sqrt (Real.exp (-W x)) = Real.exp (-W x/2) := by
        apply (Real.sqrt_eq_iff_eq_sq (Real.exp_pos _).le (Real.exp_pos _).le).mpr
        rw [pow_two, ← Real.exp_add]
        congr 1; ring
      dsimp [ψ, p]
      rw [Real.sqrt_mul hr.le, he]; ring
    have hsquare (x) : ψ x^2 = r*(f x^2*Real.exp (-W x)) := by
      dsimp [ψ]
      rw [mul_pow, Real.sq_sqrt (mul_pos hr (Real.exp_pos _)).le]
      ring
    have hunitψ : (∫ x, ψ x^2) = 1 := by
      simp_rw [hsquare]
      rw [integral_const_mul, ← hall (fun x => f x^2)]
      exact hunit
    have he : r*(∫ x, ‖EuclideanGradient f x‖^2*Real.exp (-W x)) ≤ 1 := by
      rw [← hall]; exact henergy
    have hb := hsob V hV hgrowth J charges y ε ha hmass hε r hr.le f hf c hc
    dsimp only at hb
    have hm := hunitψ
    rw [heq] at hm
    have hb' := hb hm he
    change ContDiff ℝ 1 (fun x => Real.sqrt r*(f x*Real.exp (-W x/2))) ∧
      Integrable (fun x => (Real.sqrt r*(f x*Real.exp (-W x/2)))^2) volume ∧
      Integrable (fun x => ‖EuclideanGradient (fun z => Real.sqrt r*(f z*Real.exp (-W z/2))) x‖^2) volume ∧
      (∫ x, ‖EuclideanGradient (fun z => Real.sqrt r*(f z*Real.exp (-W z/2))) x‖^2) ≤ G ∧
      eLpNorm (fun x => Real.sqrt r*(f x*Real.exp (-W x/2))) (SobolevExponent d hd) volume ≤ T at hb'
    have hcontrols : ContDiff ℝ 1 ψ ∧ Integrable (fun x => ψ x^2) volume ∧
        Integrable (fun x => ‖EuclideanGradient ψ x‖^2) volume ∧
        (∫ x, ‖EuclideanGradient ψ x‖^2) ≤ G ∧
        eLpNorm ψ (SobolevExponent d hd) volume ≤ T := by
      rw [heq]
      exact hb'
    refine ⟨heq, hunitψ, hcontrols.1, hcontrols.2.1, hcontrols.2.2.1,
      hcontrols.2.2.2.1, hcontrols.2.2.2.2, ?_⟩
    intro R hR
    have ht := tail f hf c hc R hR
    rw [hunit] at ht
    have hcoef : 0 ≤ C*(R^(-2 : ℝ)+R^(-(2/(s+1)))) := by positivity
    have hh := mul_le_mul_of_nonneg_left (show (∫ x, ‖EuclideanGradient f x‖^2 ∂P)+1 ≤ 2 by linarith) hcoef
    exact ht.trans (hh.trans_eq (by ring))
