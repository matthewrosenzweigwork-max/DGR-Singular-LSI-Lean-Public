module

public import Tablet.WeightedSpatialApproximation
public import Tablet.ConvexReferenceNormalization
public import Tablet.SoftGibbsNormalization
public import Tablet.FixedNProductCoercivity
public import Tablet.HessianMinimizer
public import Tablet.GibbsRawDensity
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2800000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff
noncomputable section

-- [TABLET NODE: FiniteGibbsSquaredTestTail]
theorem FiniteGibbsSquaredTestTail (N d : ℕ) (hN : 0 < N) (hd : 3 ≤ d)
    (s B κ : ℝ) (hs : 0 < s) (hsd : s ≤ (d : ℝ)-2)
    (hB : 0 ≤ B) (hκ : 0 < κ) (Ca : ℝ → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ V : OneParticle d → ℝ, PotentialBounds d κ V →
      (∀ z, V 0 ≤ V z) →
      (∀ a : ℝ, 0 < a → ∀ z, EuclideanLaplacian V z ≤
        a*‖EuclideanGradient V z‖^(ForceExponent s)+Ca a) →
      ∀ coupling ε : ℝ, 0 ≤ coupling → coupling ≤ B → 0 < ε →
      ∀ f : ParticleConfig d N → ℝ, ContDiff ℝ 1 f → ∀ c : ℝ,
      HasCompactSupport (fun X => f X-c) →
      let P := GibbsLaw (N:=N) (ReferenceLaw V (fun _ => 1)) s coupling ε
      IsProbabilityMeasure P ∧ Integrable (fun X => f X^2) P ∧
      Integrable (fun X => ‖EuclideanGradient f X‖^2) P ∧
      ∀ R : ℝ, 0 < R →
        (∫ X in {X : ParticleConfig d N | R < ‖X‖}, f X^2 ∂P) ≤
          C*(R^(-2 : ℝ)+R^(-(ForceExponent s)))*
            ((∫ X, ‖EuclideanGradient f X‖^2 ∂P)+∫ X, f X^2 ∂P) := by
-- BODY
  classical
  have squared_test_tail_pointwise (v F : ParticleConfig d N → ParticleConfig d N) (ψ : ParticleConfig d N → ℝ)
      (κ θ R : ℝ) (hκ : 0 < κ) (hθ : 0 < θ) (hR : 0 < R)
      (hdrift : ∀ x, κ * ‖x‖ ≤ ‖v x‖) (x : ParticleConfig d N) :
      ({x : ParticleConfig d N | R < ‖x‖}).indicator (fun x => ψ x ^ 2) x ≤
        (4 / (κ ^ 2 * R ^ 2) * ‖v x + F x‖ ^ 2 +
          (2 / (κ * R)) ^ θ * ‖F x‖ ^ θ) * ψ x ^ 2 := by
    have hden : 0 < κ ^ 2 * R ^ 2 := by positivity
    have hc0 : 0 ≤ 4 / (κ ^ 2 * R ^ 2) := by positivity
    have hf0 : 0 ≤ (2 / (κ * R)) ^ θ * ‖F x‖ ^ θ := by positivity
    by_cases hx : R < ‖x‖
    · simp only [Set.indicator, Set.mem_setOf_eq, if_pos hx]
      have htriangle : ‖v x‖ ≤ ‖v x + F x‖ + ‖F x‖ := by
        calc
          ‖v x‖ = ‖(v x + F x) - F x‖ := by congr 1; abel
          _ ≤ _ := norm_sub_le _ _
      by_cases hF : ‖F x‖ ≤ κ * R / 2
      · have htotal : κ * R / 2 ≤ ‖v x + F x‖ := by
          have hh := mul_lt_mul_of_pos_left hx hκ
          linarith [hdrift x]
        have hs : κ ^ 2 * R ^ 2 / 4 ≤ ‖v x + F x‖ ^ 2 := by
          have hh := pow_le_pow_left₀ (by positivity : 0 ≤ κ * R / 2) htotal 2
          nlinarith [hh]
        have hc : 1 ≤ 4 / (κ ^ 2 * R ^ 2) * ‖v x + F x‖ ^ 2 := by
          rw [div_mul_eq_mul_div]
          apply (le_div_iff₀ hden).2
          nlinarith [hs]
        have hcoef : 1 ≤ 4 / (κ ^ 2 * R ^ 2) * ‖v x + F x‖ ^ 2 + (2 / (κ * R)) ^ θ * ‖F x‖ ^ θ := by linarith
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoef (sq_nonneg (ψ x))
      · have hF' : κ * R / 2 ≤ ‖F x‖ := (lt_of_not_ge hF).le
        have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ κ * R / 2) hF' hθ.le
        have hid : (2 / (κ * R)) ^ θ * (κ * R / 2) ^ θ = 1 := by
          rw [← Real.mul_rpow (by positivity) (by positivity)]
          have hh : 2 / (κ * R) * (κ * R / 2) = 1 := by field_simp
          rw [hh, Real.one_rpow]
        have hc : 1 ≤ (2 / (κ * R)) ^ θ * ‖F x‖ ^ θ := by
          rw [← hid]
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
        have hαT := mul_nonneg hc0 (sq_nonneg ‖v x + F x‖)
        have hcoef : 1 ≤ 4 / (κ ^ 2 * R ^ 2) * ‖v x + F x‖ ^ 2 + (2 / (κ * R)) ^ θ * ‖F x‖ ^ θ := by linarith
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoef (sq_nonneg (ψ x))
    · simp only [Set.indicator, Set.mem_setOf_eq, if_neg hx]
      positivity
  
  -- This is a tail of the arbitrary squared test, not tightness of the law alone.
  have squared_test_tail_integral (v F : ParticleConfig d N → ParticleConfig d N) (ψ : ParticleConfig d N → ℝ)
      (κ θ R : ℝ) (hκ : 0 < κ) (hθ : 0 < θ) (hR : 0 < R)
      (hdrift : ∀ x, κ * ‖x‖ ≤ ‖v x‖)
      (hmass : Integrable (fun x => ψ x ^ 2))
      (htotal : Integrable (fun x => ‖v x + F x‖ ^ 2 * ψ x ^ 2))
      (hforce : Integrable (fun x => ‖F x‖ ^ θ * ψ x ^ 2)) :
      (∫ x in {x : ParticleConfig d N | R < ‖x‖}, ψ x ^ 2) ≤
        4 / (κ ^ 2 * R ^ 2) * (∫ x, ‖v x + F x‖ ^ 2 * ψ x ^ 2) +
          (2 / (κ * R)) ^ θ * (∫ x, ‖F x‖ ^ θ * ψ x ^ 2) := by
    have hset : MeasurableSet {x : ParticleConfig d N | R < ‖x‖} := measurableSet_lt measurable_const continuous_norm.measurable
    have H := integral_mono (hmass.indicator hset)
      ((htotal.const_mul (4 / (κ ^ 2 * R ^ 2))).add (hforce.const_mul ((2 / (κ * R)) ^ θ)))
      (fun x => by simpa only [Pi.add_apply, add_mul, mul_assoc] using
        squared_test_tail_pointwise v F ψ κ θ R hκ hθ hR hdrift x)
    simp only [Pi.add_apply] at H
    rw [integral_indicator hset, integral_add (htotal.const_mul _) (hforce.const_mul _),
      integral_const_mul, integral_const_mul] at H
    exact H
  have squared_test_coercive_tail (v F : ParticleConfig d N → ParticleConfig d N) (ψ : ParticleConfig d N → ℝ)
      (κ θ R G S B H : ℝ) (hκ : 0 < κ) (hθ : 0 < θ) (hR : 0 < R)
      (hdrift : ∀ x, κ * ‖x‖ ≤ ‖v x‖)
      (hmass : Integrable (fun x => ψ x ^ 2))
      (htotal : Integrable (fun x => ‖v x + F x‖ ^ 2 * ψ x ^ 2))
      (hforce : Integrable (fun x => ‖F x‖ ^ θ * ψ x ^ 2))
      (hG : 0 ≤ G) (hS : 0 ≤ S) (hH : 0 ≤ H)
      (hform : (∫ x, ‖F x‖ ^ θ * ψ x ^ 2) ≤ H * G)
      (hcoercive : G / 2 + (∫ x, ‖v x + F x‖ ^ 2 * ψ x ^ 2) / 8 + S / 2 ≤ B) :
      (∫ x in {x : ParticleConfig d N | R < ‖x‖}, ψ x ^ 2) ≤
        (32 / κ ^ 2 * R ^ (-2 : ℝ) + 2 * H * (2 / κ) ^ θ * R ^ (-θ)) * B := by
    have hT : 0 ≤ (∫ x, ‖v x + F x‖ ^ 2 * ψ x ^ 2) := integral_nonneg (fun x => by positivity)
    have hGbound : G ≤ 2 * B := by linarith
    have hTbound : (∫ x, ‖v x + F x‖ ^ 2 * ψ x ^ 2) ≤ 8 * B := by linarith
    have Htail := squared_test_tail_integral v F ψ κ θ R hκ hθ hR hdrift hmass htotal hforce
    have hFbound : (∫ x, ‖F x‖ ^ θ * ψ x ^ 2) ≤ H * (2 * B) :=
      hform.trans (mul_le_mul_of_nonneg_left hGbound hH)
    have hα : 0 ≤ 4 / (κ ^ 2 * R ^ 2) := by positivity
    have hβ : 0 ≤ (2 / (κ * R)) ^ θ := by positivity
    have hscaledT := mul_le_mul_of_nonneg_left hTbound hα
    have hscaledF := mul_le_mul_of_nonneg_left hFbound hβ
    have hR2 : R ^ (-2 : ℝ) = (R ^ (2 : ℕ))⁻¹ := by
      rw [Real.rpow_neg hR.le]
      congr 1
      simpa only [Nat.cast_ofNat] using Real.rpow_natCast R 2
    have hRθ : (2 / (κ * R)) ^ θ = (2 / κ) ^ θ * R ^ (-θ) := by
      have hbase : 2 / (κ * R) = (2 / κ) * R⁻¹ := by ring
      rw [hbase, Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_neg_one R, ← Real.rpow_mul hR.le]
      congr 1
      ring
    have hid : 4 / (κ ^ 2 * R ^ 2) * (8 * B) + (2 / (κ * R)) ^ θ * (H * (2 * B)) =
        (32 / κ ^ 2 * R ^ (-2 : ℝ) + 2 * H * (2 / κ) ^ θ * R ^ (-θ)) * B := by
      rw [hR2, hRθ]
      ring
    exact Htail.trans ((add_le_add hscaledT hscaledF).trans_eq hid)
  have continuous_gradient (g : ParticleConfig d N → ℝ) (hg : ContDiff ℝ 1 g) :
      Continuous (EuclideanGradient g) :=
    (InnerProductSpace.toDual ℝ (ParticleConfig d N)).symm.continuous.comp
      (hg.continuous_fderiv (by norm_num))
  have compact_weight_integrable (a ψ : ParticleConfig d N → ℝ)
      (ha : Continuous a) (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) :
      Integrable (fun X => a X*ψ X^2) volume := by
    have hc : HasCompactSupport (fun X => ψ X^2) := hcψ.comp_left (g:=fun z : ℝ => z^2) (by simp)
    exact (ha.mul (hψ.continuous.pow 2)).integrable_of_hasCompactSupport hc.mul_left
  obtain ⟨C₀,hC₀,hcoerc⟩ := FixedNProductCoercivity N d hN hd s B hs hsd hB Ca
  obtain ⟨H,hH,hforce⟩ := PairInteractionForceForm d N hd s B hs hB
  let θ := ForceExponent s
  have hθ : 0 < θ := (ForceExponentRange s hs).1
  let P₀ := max 1 C₀
  have hP₀ : 0 < P₀ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  let L₀ := 32/κ^2+2*H*(2/κ)^θ
  have hL₀ : 0 < L₀ := by dsimp [L₀]; positivity
  refine ⟨L₀*P₀,mul_pos hL₀ hP₀,?_⟩
  intro V hV hmin hgrowth coupling ε ha haB hε f hf c hcf
  let W := fun X : ParticleConfig d N => ∑ i : Fin N, V (ParticlePosition X i)
  let U := PairInteraction (d:=d) (N:=N) s coupling ε
  let Htot := fun X => W X+U X
  obtain ⟨hW,hprod⟩ := ProductConfinementCalculus d N V hV.regularity
  have hsource := PairInteractionSource d N s coupling ε hs hsd ha hε
  have hU : ContDiff ℝ 2 U := hsource.1.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hHtot : ContDiff ℝ 2 Htot := hW.add hU
  have hS (X : ParticleConfig d N) : 0 ≤ -EuclideanLaplacian U X := (hsource.2 X).2
  obtain ⟨_,a,hamin,huniq,_,_,hrowdrift⟩ := HessianMinimizer V κ hκ hV
  have hazero : a=0 := (huniq 0 hmin).symm
  have hrow (z : OneParticle d) : κ*‖z‖ ≤ ‖EuclideanGradient V z‖ := by
    simpa only [hazero,sub_zero] using hrowdrift z
  have hnorm (X : ParticleConfig d N) : ‖X‖^2 = ∑ i : Fin N, ‖ParticlePosition X i‖^2 := by
    simp only [EuclideanSpace.real_norm_sq_eq,Fintype.sum_prod_type,ParticlePosition]
  have hdrift (X : ParticleConfig d N) : κ*‖X‖ ≤ ‖EuclideanGradient W X‖ := by
    have hh := Finset.sum_le_sum (s:=Finset.univ) fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) =>
      pow_le_pow_left₀ (by positivity : 0 ≤ κ*‖ParticlePosition X i‖) (hrow (ParticlePosition X i)) 2
    simp_rw [mul_pow] at hh
    rw [← Finset.mul_sum,← hnorm X,← (hprod X).1] at hh
    rw [← mul_pow] at hh
    exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp hh
  have hcompact (g : ParticleConfig d N → ℝ) (hg : ContDiff ℝ 1 g)
      (hcg : HasCompactSupport g) (R : ℝ) (hR : 0 < R) :
      (∫ X in {X : ParticleConfig d N | R < ‖X‖}, g X^2*Real.exp (-Htot X)) ≤
        (L₀*P₀)*(R^(-2 : ℝ)+R^(-θ))*
          ((∫ X, ‖EuclideanGradient g X‖^2*Real.exp (-Htot X))+
            ∫ X, g X^2*Real.exp (-Htot X)) := by
    let ψ := fun X => g X*Real.exp (-Htot X/2)
    have hψ : ContDiff ℝ 1 ψ := hg.mul (((hHtot.of_le (by norm_num)).neg.div_const 2).exp)
    have hcψ : HasCompactSupport ψ := hcg.mul_right
    have hsquare (X) : ψ X^2 = g X^2*Real.exp (-Htot X) := by
      dsimp [ψ]; rw [mul_pow,← Real.exp_nat_mul]; congr 1; ring
    have hiMass : Integrable (fun X => ψ X^2) volume := by
      simpa only [one_mul] using compact_weight_integrable (fun _ => 1) ψ continuous_const hψ hcψ
    have hiTotal := compact_weight_integrable
      (fun X => ‖EuclideanGradient W X+EuclideanGradient U X‖^2) ψ
      (((continuous_gradient W (hW.of_le (by norm_num))).add
        (continuous_gradient U (hU.of_le (by norm_num)))).norm.pow 2) hψ hcψ
    have hform := hforce coupling ε ha haB hε ψ hψ hcψ
    let E := ∫ X, ‖EuclideanGradient g X‖^2*Real.exp (-Htot X)
    let M := ∫ X, ψ X^2
    let G := ∫ X, ‖EuclideanGradient ψ X‖^2
    let S := ∫ X, -EuclideanLaplacian U X*ψ X^2
    have hG : 0 ≤ G := integral_nonneg fun _ => sq_nonneg _
    have hS' : 0 ≤ S := integral_nonneg fun X => mul_nonneg (hS X) (sq_nonneg _)
    have hE : 0 ≤ E := integral_nonneg fun _ => by positivity
    have hM : 0 ≤ M := integral_nonneg fun _ => sq_nonneg _
    have hc := hcoerc V hV.regularity hgrowth coupling ε ha haB hε g hg hcg
    change G/2+(∫ X, ‖EuclideanGradient W X+EuclideanGradient U X‖^2*ψ X^2)/8+S/2 ≤ E+C₀*M at hc
    have ht := squared_test_coercive_tail (EuclideanGradient W) (EuclideanGradient U) ψ
      κ θ R G S (E+C₀*M) H hκ hθ hR hdrift hiMass hiTotal hform.1 hG hS' hH hform.2 hc
    have henergy : E+C₀*M ≤ P₀*(E+M) := by
      have h1 := mul_le_mul_of_nonneg_right (le_max_left (1:ℝ) C₀) hE
      have h2 := mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) C₀) hM
      dsimp [P₀]; nlinarith
    have hr2 : 0 ≤ R^(-2:ℝ) := Real.rpow_nonneg hR.le _
    have hrθ : 0 ≤ R^(-θ) := Real.rpow_nonneg hR.le _
    have hα : 0 ≤ 32/κ^2 := by positivity
    have hβ : 0 ≤ 2*H*(2/κ)^θ := by positivity
    have hRate : 32/κ^2*R^(-2:ℝ)+2*H*(2/κ)^θ*R^(-θ) ≤ L₀*(R^(-2:ℝ)+R^(-θ)) := by
      dsimp [L₀]; nlinarith [mul_nonneg hα hrθ,mul_nonneg hβ hr2]
    have hfinal := ht.trans ((mul_le_mul_of_nonneg_right hRate (by positivity : 0 ≤ E+C₀*M)).trans
      (mul_le_mul_of_nonneg_left henergy (by positivity : 0 ≤ L₀*(R^(-2:ℝ)+R^(-θ)))))
    simpa only [M,E,hsquare,mul_assoc,mul_left_comm,mul_comm] using hfinal
  let P := GibbsLaw (N:=N) (ReferenceLaw V (fun _ => 1)) s coupling ε
  have hone : BoundedMultiplier d 1 (fun _ => 1) :=
    ⟨measurable_const,1,1,by norm_num,le_rfl,by norm_num,fun _ => ⟨le_rfl,le_rfl⟩⟩
  letI : IsProbabilityMeasure (ReferenceLaw V (fun _ => 1)) :=
    (ConvexReferenceNormalization V (fun _ => 1) κ 1 hκ hV hone).2.2
  have hProb : IsProbabilityMeasure P :=
    (SoftGibbsNormalization (N:=N) (ReferenceLaw V (fun _ => 1)) s coupling ε hs ha hε).2.2
  letI : IsProbabilityMeasure P := hProb
  obtain ⟨fn,hreg,_,_,_,_,hmasslim,henergylim,htailall⟩ :=
    WeightedSpatialApproximation P f hf c hcf
  have hb : BoundedMultiplier d 1 (fun _ => 1) :=
    ⟨measurable_const,1,1,by norm_num,le_rfl,by norm_num,fun _ => ⟨le_rfl,le_rfl⟩⟩
  have hZref : 0 < ReferencePartition V (fun _ => 1) :=
    (ConvexReferenceNormalization V (fun _ => 1) κ 1 hκ hV hb).2.1
  letI : IsProbabilityMeasure (ReferenceLaw V (fun _ => 1)) :=
    (ConvexReferenceNormalization V (fun _ => 1) κ 1 hκ hV hb).2.2
  have hZG : 0 < GibbsPartition (N:=N) (ReferenceLaw V (fun _ => 1)) s coupling ε :=
    (SoftGibbsNormalization (N:=N) (ReferenceLaw V (fun _ => 1)) s coupling ε hs ha hε).2.1.1
  let r := ((ReferencePartition V (fun _ => 1))^N*
    GibbsPartition (N:=N) (ReferenceLaw V (fun _ => 1)) s coupling ε)⁻¹
  have hr : 0 < r := inv_pos.mpr (mul_pos (pow_pos hZref N) hZG)
  have hw (X : ParticleConfig d N) : InteractionWeight s coupling ε X = Real.exp (-U X) := by
    by_cases h : coupling=0
    · simp [h,InteractionWeight,U,PairInteraction]
    · simp [InteractionWeight,h,ne_of_gt hε,U]
  have hp (X : ParticleConfig d N) : GibbsLebesgueDensity V (fun _ => 1) s coupling ε X =
      r*Real.exp (-Htot X) := by
    dsimp [GibbsLebesgueDensity,r,Htot,W]
    rw [hw,neg_add,Real.exp_add]
    simp only [Finset.prod_const_one,mul_one]
    ring
  have hlaw : P=volume.withDensity (fun X => ENNReal.ofReal (r*Real.exp (-Htot X))) := by
    have h := GibbsRawDensity (N:=N) (by omega : 0<d) V (fun _ => 1) κ 1 hκ hV hb s coupling ε hs ha hε.le
    simp_rw [hp] at h
    exact h
  have hint (μ : Measure (ParticleConfig d N)) (g : ParticleConfig d N → ℝ) :
      (∫ X, g X ∂μ.withDensity (fun X => ENNReal.ofReal (r*Real.exp (-Htot X)))) =
        r*∫ X, g X*Real.exp (-Htot X) ∂μ := by
    have hm : Measurable (fun X => ENNReal.ofReal (r*Real.exp (-Htot X))) :=
      (measurable_const.mul hHtot.continuous.measurable.neg.exp).ennreal_ofReal
    rw [integral_withDensity_eq_integral_toReal_smul hm (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp_rw [ENNReal.toReal_ofReal (mul_pos hr (Real.exp_pos _)).le,smul_eq_mul]
    have he (X) : r*Real.exp (-Htot X)*g X = r*(g X*Real.exp (-Htot X)) := by ring
    simp_rw [he]
    rw [integral_const_mul]
  have hall (g : ParticleConfig d N → ℝ) : (∫ X, g X ∂P)=r*∫ X, g X*Real.exp (-Htot X) := by
    rw [hlaw]; exact hint volume g
  have hrest (S : Set (ParticleConfig d N)) (hS : MeasurableSet S) (g : ParticleConfig d N → ℝ) :
      (∫ X in S, g X ∂P)=r*∫ X in S, g X*Real.exp (-Htot X) := by
    rw [hlaw,restrict_withDensity hS]; exact hint (volume.restrict S) g
  obtain ⟨F,hFb⟩ := hcf.exists_bound_of_continuous (hf.continuous.sub continuous_const)
  let A := max 0 F+|c|
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hfbound (X) : |f X| ≤ A := by
    have h := abs_add_le (f X-c) c
    have he : f X-c+c=f X := by ring
    rw [he] at h
    have hb : |f X-c| ≤ F := by simpa only [Real.norm_eq_abs] using hFb X
    dsimp [A]; linarith [le_max_right (0:ℝ) F]
  have hfd := hcf.fderiv ℝ
  obtain ⟨G,hGb⟩ := hfd.exists_bound_of_continuous ((hf.sub contDiff_const).continuous_fderiv (by norm_num))
  have hG : 0 ≤ G := (norm_nonneg _).trans (hGb 0)
  have hgbound (X) : ‖EuclideanGradient f X‖ ≤ G := by
    have h := hGb X
    rw [fderiv_sub_const c] at h
    simpa only [(GradientNormIdentity f X).2] using h
  have hiMass : Integrable (fun X => f X^2) P :=
    (integrable_const (A^2)).mono' (hf.continuous.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hfbound X) 2)
  have hiEnergy : Integrable (fun X => ‖EuclideanGradient f X‖^2) P :=
    (integrable_const (G^2)).mono' ((continuous_gradient f hf).norm.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hgbound X) 2)
  dsimp only
  refine ⟨hProb,hiMass,hiEnergy,?_⟩
  intro R hR
  let T := {X : ParticleConfig d N | R < ‖X‖}
  have hT : MeasurableSet T := measurableSet_lt measurable_const continuous_norm.measurable
  have hbound (n : ℕ) : (∫ X in T, fn n X^2 ∂P) ≤
      (L₀*P₀)*(R^(-2:ℝ)+R^(-θ))*
        ((∫ X, ‖EuclideanGradient (fn n) X‖^2 ∂P)+∫ X, fn n X^2 ∂P) := by
    have h := mul_le_mul_of_nonneg_left (hcompact (fn n) (hreg n).1 (hreg n).2 R hR) hr.le
    rw [hrest T hT,hall (fun X => ‖EuclideanGradient (fn n) X‖^2),hall (fun X => fn n X^2)]
    nlinarith [h]
  have hright := (henergylim.add hmasslim).const_mul ((L₀*P₀)*(R^(-2:ℝ)+R^(-θ)))
  exact le_of_tendsto_of_tendsto (htailall T) hright (Eventually.of_forall hbound)

#print axioms FiniteGibbsSquaredTestTail
