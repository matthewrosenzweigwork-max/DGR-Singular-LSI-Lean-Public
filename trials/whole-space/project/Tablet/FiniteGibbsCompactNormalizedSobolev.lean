import Tablet.WeightedSpatialApproximation
import Tablet.ConvexReferenceNormalization
import Tablet.SoftGibbsNormalization
import Tablet.FixedNProductCoercivity
import Tablet.GibbsRawDensity
import Tablet.EuclideanSobolev
import Tablet.CriticalNormControls
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 3000000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff
noncomputable section

-- [TABLET NODE: FiniteGibbsCompactNormalizedSobolev]
theorem FiniteGibbsCompactNormalizedSobolev (N d : ℕ) (hN : 0 < N) (hd : 3 ≤ d)
    (s B κ : ℝ) (hs : 0 < s) (hsd : s ≤ (d : ℝ)-2)
    (hB : 0 ≤ B) (hκ : 0 < κ) (Ca : ℝ → ℝ) :
    ∃ (G : ℝ) (T : ℝ≥0∞), 0 ≤ G ∧ T < ⊤ ∧
      ∀ V : OneParticle d → ℝ, PotentialBounds d κ V →
      (∀ a : ℝ, 0 < a → ∀ z, EuclideanLaplacian V z ≤
        a*‖EuclideanGradient V z‖^(ForceExponent s)+Ca a) →
      ∀ coupling ε : ℝ, 0 ≤ coupling → coupling ≤ B → 0 < ε →
      ∀ f : ParticleConfig d N → ℝ, ContDiff ℝ 1 f → ∀ c : ℝ,
      HasCompactSupport (fun X => f X-c) →
      let P := GibbsLaw (N:=N) (ReferenceLaw V (fun _ => 1)) s coupling ε
      let ψ := fun X => f X*Real.sqrt (GibbsLebesgueDensity V (fun _ => 1) s coupling ε X)
      let p := SobolevExponent (N*d) (hd.trans (Nat.le_mul_of_pos_left d hN))
      (∫ X, f X^2 ∂P)=1 → (∫ X, ‖EuclideanGradient f X‖^2 ∂P) ≤ 1 →
      IsProbabilityMeasure P ∧ (2 : ℝ) < p ∧ (∫ X, ψ X^2)=1 ∧
      ContDiff ℝ 1 ψ ∧ Integrable (fun X => ψ X^2) volume ∧
      Integrable (fun X => ‖EuclideanGradient ψ X‖^2) volume ∧
      (∫ X, ‖EuclideanGradient ψ X‖^2) ≤ G ∧ eLpNorm ψ p volume ≤ T ∧
      Integrable (fun X => |ψ X|^(p : ℝ)) volume ∧
      MemLp (fun X => ψ X^2) (ENNReal.ofReal ((p : ℝ)/2)) volume ∧
      (∫ X, |ψ X|^(p : ℝ)) ≤ T.toReal^(p : ℝ) ∧
      (∀ S : Set (ParticleConfig d N), MeasurableSet S → volume S ≠ ⊤ →
        (∫ X in S, ψ X^2) ≤
          (T.toReal^(p : ℝ))^(2/(p : ℝ))*(volume.real S)^(1-2/(p : ℝ))) := by
-- BODY
  classical
  have hn : 3 ≤ N*d := hd.trans (Nat.le_mul_of_pos_left d hN)
  have hcard : 3 ≤ Fintype.card (Fin N × Fin d) := by simpa using hn
  let p := SobolevExponent (N*d) hn
  have hpcrit : (2 : ℝ) < p := by
    have hnR : (3 : ℝ) ≤ (N*d : ℕ) := by exact_mod_cast hn
    change (2 : ℝ) < 2*(N*d : ℕ)/((N*d : ℕ)-2 : ℝ)
    apply (lt_div_iff₀ (by linarith : 0 < ((N*d : ℕ) : ℝ)-2)).2
    nlinarith
  obtain ⟨C,hC,hcoerc⟩ := FixedNProductCoercivity N d hN hd s B hs hsd hB Ca
  obtain ⟨S,hSob⟩ := EuclideanSobolev (ι:=Fin N × Fin d) hcard
  simp only [Fintype.card_prod,Fintype.card_fin] at hSob
  let G := 4*(1+C)
  let T : ℝ≥0∞ := S*ENNReal.ofReal G^(1/2:ℝ)
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hT : T < ⊤ := by dsimp [T]; finiteness
  refine ⟨G,T,hG,hT,?_⟩
  intro V hV hgrowth coupling ε ha haB hε f hf c hcf
  dsimp only
  intro hunit henergy
  let W := fun X : ParticleConfig d N => ∑ i : Fin N, V (ParticlePosition X i)
  let U := PairInteraction (d:=d) (N:=N) s coupling ε
  let Htot := fun X => W X+U X
  have hW := (ProductConfinementCalculus d N V hV.regularity).1
  have hsource := PairInteractionSource d N s coupling ε hs hsd ha hε
  have hU : ContDiff ℝ 2 U := hsource.1.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hHtot : ContDiff ℝ 2 Htot := hW.add hU
  have hS (X : ParticleConfig d N) : 0 ≤ -EuclideanLaplacian U X := (hsource.2 X).2
  let P := GibbsLaw (N:=N) (ReferenceLaw V (fun _ => 1)) s coupling ε
  have hone : BoundedMultiplier d 1 (fun _ => 1) :=
    ⟨measurable_const,1,1,by norm_num,le_rfl,by norm_num,fun _ => ⟨le_rfl,le_rfl⟩⟩
  letI : IsProbabilityMeasure (ReferenceLaw V (fun _ => 1)) :=
    (ConvexReferenceNormalization V (fun _ => 1) κ 1 hκ hV hone).2.2
  have hProb : IsProbabilityMeasure P :=
    (SoftGibbsNormalization (N:=N) (ReferenceLaw V (fun _ => 1)) s coupling ε hs ha hε).2.2
  letI : IsProbabilityMeasure P := hProb
  obtain ⟨fn,hreg,hval,hgrad,_,_,hmasslim,henergylim,_⟩ :=
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

  let ground := fun g : ParticleConfig d N → ℝ => fun X => g X*Real.exp (-Htot X/2)
  let tr := fun g : ParticleConfig d N → ℝ => fun X => Real.sqrt r*ground g X
  have hground (g : ParticleConfig d N → ℝ) (hg : ContDiff ℝ 1 g) : ContDiff ℝ 1 (ground g) :=
    hg.mul (((hHtot.of_le (by norm_num)).neg.div_const 2).exp)
  have htr (g : ParticleConfig d N → ℝ) (hg : ContDiff ℝ 1 g) : ContDiff ℝ 1 (tr g) :=
    contDiff_const.mul (hground g hg)
  have continuous_gradient (g : ParticleConfig d N → ℝ) (hg : ContDiff ℝ 1 g) :
      Continuous (EuclideanGradient g) :=
    (InnerProductSpace.toDual ℝ (ParticleConfig d N)).symm.continuous.comp (hg.continuous_fderiv (by norm_num))
  have gradient_scale (g : ParticleConfig d N → ℝ) (hg : ContDiff ℝ 1 g) (a : ℝ) (X) :
      EuclideanGradient (fun Y => a*g Y) X=a • EuclideanGradient g X := by
    simp only [EuclideanGradient,gradient,fderiv_const_mul (hg.differentiable (by norm_num) X),map_smul]
  have hgscale (g : ParticleConfig d N → ℝ) (hg : ContDiff ℝ 1 g) (X) :
      ‖EuclideanGradient (tr g) X‖^2=r*‖EuclideanGradient (ground g) X‖^2 := by
    dsimp only [tr]
    rw [gradient_scale (ground g) (hground g hg),norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt hr.le]
  have hsquare (g : ParticleConfig d N → ℝ) (X) : tr g X^2=r*(g X^2*Real.exp (-Htot X)) := by
    dsimp [tr,ground]
    rw [mul_pow,mul_pow,Real.sq_sqrt hr.le,← Real.exp_nat_mul]
    congr 2
    ring
  have heq : (fun X => f X*Real.sqrt (GibbsLebesgueDensity V (fun _ => 1) s coupling ε X))=tr f := by
    funext X
    rw [hp X]
    have he : Real.sqrt (Real.exp (-Htot X))=Real.exp (-Htot X/2) := by
      apply (Real.sqrt_eq_iff_eq_sq (Real.exp_pos _).le (Real.exp_pos _).le).mpr
      rw [← Real.exp_nat_mul]
      congr 1; ring
    rw [Real.sqrt_mul hr.le,he]
    dsimp [tr,ground]; ring
  have hM : (∫ X, tr f X^2)=1 := by
    simp_rw [hsquare]
    rw [integral_const_mul,← hall (fun X => f X^2)]
    exact hunit
  have hiMass : Integrable (fun X => tr f X^2) volume := by
    by_contra hi
    rw [integral_undef hi] at hM
    norm_num at hM
  have rawsquare (g : ParticleConfig d N → ℝ) (X) : ground g X^2=g X^2*Real.exp (-Htot X) := by
    dsimp [ground]; rw [mul_pow,← Real.exp_nat_mul]; congr 1; ring
  have hgb (g : ParticleConfig d N → ℝ) (hg : ContDiff ℝ 1 g)
      (hcg : HasCompactSupport g) :
      Integrable (fun X => ‖EuclideanGradient (tr g) X‖^2) volume ∧
        (∫ X, ‖EuclideanGradient (tr g) X‖^2) ≤
          2*((∫ X, ‖EuclideanGradient g X‖^2 ∂P)+C*(∫ X, g X^2 ∂P)) := by
    have hcompact : HasCompactSupport (tr g) := hcg.mul_right.mul_left
    have hcder : HasCompactSupport (fun X => ‖fderiv ℝ (tr g) X‖^2) :=
      (hcompact.fderiv ℝ).comp_left (g:=fun A : ParticleConfig d N →L[ℝ] ℝ => ‖A‖^2) (by simp)
    have hider := ((htr g hg).continuous_fderiv (by norm_num)).norm.pow 2 |>.integrable_of_hasCompactSupport
      (μ:=(volume : Measure (ParticleConfig d N))) hcder
    have hi : Integrable (fun X => ‖EuclideanGradient (tr g) X‖^2) volume :=
      hider.congr (Eventually.of_forall fun X => by
        change ‖fderiv ℝ (tr g) X‖^2=‖EuclideanGradient (tr g) X‖^2
        rw [(GradientNormIdentity (tr g) X).2])
    have hc := hcoerc V hV.regularity hgrowth coupling ε ha haB hε g hg hcg
    change (∫ X, ‖EuclideanGradient (ground g) X‖^2)/2+
      (∫ X, ‖EuclideanGradient W X+EuclideanGradient U X‖^2*ground g X^2)/8+
      (∫ X, -EuclideanLaplacian U X*ground g X^2)/2 ≤
      (∫ X, ‖EuclideanGradient g X‖^2*Real.exp (-Htot X))+C*(∫ X, ground g X^2) at hc
    have hT0 : 0 ≤ ∫ X, ‖EuclideanGradient W X+EuclideanGradient U X‖^2*ground g X^2 :=
      integral_nonneg fun X => mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hS0 : 0 ≤ ∫ X, -EuclideanLaplacian U X*ground g X^2 :=
      integral_nonneg fun X => mul_nonneg (hS X) (sq_nonneg _)
    have hmass : (∫ X, ground g X^2)=(∫ X, g X^2*Real.exp (-Htot X)) := by simp_rw [rawsquare]
    rw [hmass] at hc
    have hraw : (∫ X, ‖EuclideanGradient (ground g) X‖^2) ≤
        2*((∫ X, ‖EuclideanGradient g X‖^2*Real.exp (-Htot X))+C*(∫ X, g X^2*Real.exp (-Htot X))) := by
      linarith
    refine ⟨hi,?_⟩
    simp_rw [hgscale g hg]
    rw [integral_const_mul,hall (fun X => ‖EuclideanGradient g X‖^2),hall (fun X => g X^2)]
    have h := mul_le_mul_of_nonneg_left hraw hr.le
    nlinarith [h]
  have hlt : 2*((∫ X, ‖EuclideanGradient f X‖^2 ∂P)+C*(∫ X, f X^2 ∂P)) < G := by
    rw [hunit]; dsimp [G]; nlinarith
  have hevent : ∀ᶠ n : ℕ in atTop, 2*((∫ X, ‖EuclideanGradient (fn n) X‖^2 ∂P)+
      C*(∫ X, fn n X^2 ∂P)) ≤ G :=
    (((henergylim.add (hmasslim.const_mul C)).const_mul 2).eventually
      (eventually_lt_nhds hlt)).mono fun n hn => hn.le
  have gradient_L2 (g : ParticleConfig d N → ℝ)
      (hi : Integrable (fun X => ‖EuclideanGradient g X‖^2) volume) :
      eLpNorm (EuclideanGradient g) 2 volume=ENNReal.ofReal (∫ X, ‖EuclideanGradient g X‖^2)^(1/2:ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2:ℝ≥0∞) ≠ 0) (by norm_num : (2:ℝ≥0∞) ≠ ⊤)]
    norm_num only [ENNReal.toReal_ofNat]
    congr 1
    rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun X => sq_nonneg _)]
    apply lintegral_congr
    intro X
    rw [ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm]
    simpa only [Nat.cast_ofNat] using ENNReal.rpow_natCast ‖EuclideanGradient g X‖ₑ 2
  have hnormbound : ∀ᶠ n : ℕ in atTop, eLpNorm (tr (fn n)) p volume ≤ T := by
    filter_upwards [hevent] with n hn
    have hcomp : HasCompactSupport (tr (fn n)) := (hreg n).2.mul_right.mul_left
    have hgn := hgb (fn n) (hreg n).1 (hreg n).2
    have hs := hSob (tr (fn n)) (htr (fn n) (hreg n).1) hcomp
    change eLpNorm (tr (fn n)) p volume ≤ S*eLpNorm (EuclideanGradient (tr (fn n))) 2 volume at hs
    rw [gradient_L2 _ hgn.1] at hs
    apply hs.trans
    exact mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hgn.2.trans hn)) (by norm_num : (0:ℝ) ≤ 1/2)) (by positivity)
  let q := fun X : ParticleConfig d N => Real.exp (-Htot X/2)
  have hq : ContDiff ℝ 1 q := ((hHtot.of_le (by norm_num)).neg.div_const 2).exp
  have gradient_product (g h : ParticleConfig d N → ℝ)
      (hg : Differentiable ℝ g) (hh : Differentiable ℝ h) (X) :
      EuclideanGradient (fun Y => g Y*h Y) X=
        h X • EuclideanGradient g X+g X • EuclideanGradient h X := by
    apply (InnerProductSpace.toDual ℝ (ParticleConfig d N)).injective
    rw [map_add,map_smul,map_smul,EuclideanGradient,EuclideanGradient,EuclideanGradient,
      toDual_gradient,toDual_gradient,toDual_gradient,fderiv_fun_mul (hg X) (hh X)]
    simp only [smul_eq_mul,add_comm]
  have hprod (g : ParticleConfig d N → ℝ) (hg : ContDiff ℝ 1 g) (X) :
      EuclideanGradient (tr g) X=Real.sqrt r •
        (q X • EuclideanGradient g X+g X • EuclideanGradient q X) := by
    change EuclideanGradient (fun Y => Real.sqrt r*(g Y*q Y)) X=_
    rw [gradient_scale (fun Y => g Y*q Y) (hg.mul hq),
      gradient_product g q (hg.differentiable (by norm_num)) (hq.differentiable (by norm_num))]
  have hgradlim (X) : Tendsto (fun n => EuclideanGradient (tr (fn n)) X) atTop
      (𝓝 (EuclideanGradient (tr f) X)) := by
    have he (n) := hprod (fn n) (hreg n).1 X
    simp_rw [he]
    rw [hprod f hf X]
    exact (((hgrad X).const_smul (q X)).add ((hval X).smul_const (EuclideanGradient q X))).const_smul (Real.sqrt r)
  let D := fun n X => ENNReal.ofReal (‖EuclideanGradient (tr (fn n)) X‖^2)
  have hDm (n : ℕ) : Measurable (D n) :=
    ((continuous_gradient (tr (fn n)) (htr (fn n) (hreg n).1)).norm.pow 2).measurable.ennreal_ofReal
  have hDlim (X) : Tendsto (fun n => D n X) atTop
      (𝓝 (ENNReal.ofReal (‖EuclideanGradient (tr f) X‖^2))) :=
    ENNReal.tendsto_ofReal ((hgradlim X).norm.pow 2)
  have HF : (∫⁻ X, ENNReal.ofReal (‖EuclideanGradient (tr f) X‖^2)) ≤
      liminf (fun n => ∫⁻ X, D n X) atTop := by
    calc
      _ = ∫⁻ X, liminf (fun n => D n X) atTop :=
        lintegral_congr fun X => (hDlim X).liminf_eq.symm
      _ ≤ _ := lintegral_liminf_le hDm
  have hDcap : ∀ᶠ n : ℕ in atTop, (∫⁻ X, D n X) ≤ ENNReal.ofReal G := by
    filter_upwards [hevent] with n hn
    have hgn := hgb (fn n) (hreg n).1 (hreg n).2
    have he := ofReal_integral_eq_lintegral_ofReal hgn.1
      (Eventually.of_forall fun X => sq_nonneg ‖EuclideanGradient (tr (fn n)) X‖)
    change (∫⁻ X, ENNReal.ofReal (‖EuclideanGradient (tr (fn n)) X‖^2)) ≤ ENNReal.ofReal G
    rw [← he]
    exact ENNReal.ofReal_le_ofReal (hgn.2.trans hn)
  have HR : (∫⁻ X, ENNReal.ofReal (‖EuclideanGradient (tr f) X‖^2)) ≤ ENNReal.ofReal G :=
    HF.trans ((liminf_le_liminf hDcap).trans_eq tendsto_const_nhds.liminf_eq)
  have hiGrad : Integrable (fun X => ‖EuclideanGradient (tr f) X‖^2) volume :=
    (lintegral_ofReal_ne_top_iff_integrable
      ((continuous_gradient (tr f) (htr f hf)).norm.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun X => sq_nonneg _)).mp
      (ne_of_lt (HR.trans_lt ENNReal.ofReal_lt_top))
  have hcap : (∫ X, ‖EuclideanGradient (tr f) X‖^2) ≤ G := by
    rw [← ofReal_integral_eq_lintegral_ofReal hiGrad (Eventually.of_forall fun X => sq_nonneg _)] at HR
    exact (ENNReal.ofReal_le_ofReal_iff hG).mp HR
  have hnorm : eLpNorm (tr f) p volume ≤ T :=
    Lp.eLpNorm_le_of_ae_tendsto hnormbound
      (fun n => (htr (fn n) (hreg n).1).continuous.aestronglyMeasurable)
      (Eventually.of_forall fun X => ((hval X).mul_const (Real.exp (-Htot X/2))).const_mul (Real.sqrt r))
  have hcrit := CriticalNormControls volume p hpcrit T hT (tr f) (htr f hf).continuous.aestronglyMeasurable hnorm
  rw [heq]
  have heqval (X) : f X*Real.sqrt (GibbsLebesgueDensity V (fun _ => 1) s coupling ε X)=tr f X := congrFun heq X
  simp_rw [heqval]
  exact ⟨hProb,hpcrit,hM,htr f hf,hiMass,hiGrad,hcap,hnorm,hcrit⟩

#print axioms FiniteGibbsCompactNormalizedSobolev
