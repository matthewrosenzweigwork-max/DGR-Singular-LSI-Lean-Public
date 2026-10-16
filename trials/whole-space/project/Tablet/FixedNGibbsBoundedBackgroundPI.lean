import Tablet.FixedNGibbsAmplitudeClipping
import Tablet.ConfigurationCoordinateTransport
import Tablet.CutoffCubeApproximation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic
import Tablet.FiniteGibbsProductBoundedTilt
set_option autoImplicit false
set_option maxHeartbeats 6000000
open MeasureTheory Filter Set Metric
open scoped ENNReal NNReal Topology ContDiff
noncomputable section

-- [TABLET NODE: FixedNGibbsBoundedBackgroundPI]
theorem FixedNGibbsBoundedBackgroundPI (N d : ℕ) (hN : 2 ≤ N) (hd : 3 ≤ d)
    (s B κ L : ℝ) (hs : 0 < s) (hsd : s ≤ (d : ℝ)-2)
    (hB : 0 ≤ B) (hκ : 0 < κ) (hL : 1 ≤ L) (Ca Mloc : ℝ → ℝ) :
    ∃ rate σ : ℝ, 0 < rate ∧ 0 < σ ∧ σ=rate/L^N ∧
      ∀ V : OneParticle d → ℝ, PotentialBounds d κ V → (∀ z, V 0 ≤ V z) →
      (∀ R, 0 < R → ∀ z, ‖z‖ ≤ R → V z-V 0 ≤ Mloc R) →
      (∀ a, 0 < a → ∀ z, EuclideanLaplacian V z ≤
        a*‖EuclideanGradient V z‖^(ForceExponent s)+Ca a) →
      ∀ b : OneParticle d → ℝ, BoundedMultiplier d L b →
      ∀ coupling ε : ℝ, 0 ≤ coupling → coupling ≤ B → 0 < ε →
      ∀ f : ParticleConfig d N → ℝ, ContDiff ℝ 1 f → ∀ c : ℝ,
      HasCompactSupport (fun X => f X-c) →
      let Q := GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε
      IsProbabilityMeasure Q ∧
      rate*ProbabilityTheory.variance f Q ≤ L^N*(∫ X, ‖EuclideanGradient f X‖^2 ∂Q) ∧
      σ*ProbabilityTheory.variance f Q ≤ (∫ X, ‖EuclideanGradient f X‖^2 ∂Q) := by
-- BODY
  have fixed_normalized_gap (N d : ℕ) (hN : 2 ≤ N) (hd : 3 ≤ d)
      (s B κ : ℝ) (hs : 0 < s) (hsd : s ≤ (d:ℝ)-2)
      (hB : 0 ≤ B) (hκ : 0 < κ) (Ca Mloc : ℝ → ℝ) :
      ∃ σ : ℝ, 0 < σ ∧ ∀ V : OneParticle d → ℝ, PotentialBounds d κ V →
        (∀ x, V 0 ≤ V x) →
        (∀ R, 0 < R → ∀ x, ‖x‖ ≤ R → V x-V 0 ≤ Mloc R) →
        (∀ a, 0 < a → ∀ x, EuclideanLaplacian V x ≤ a*‖EuclideanGradient V x‖^ForceExponent s+Ca a) →
        ∀ coupling ε : ℝ, 0 ≤ coupling → coupling ≤ B → 0 < ε →
        ∀ f : ParticleConfig d N → ℝ, ContDiff ℝ 1 f → ∀ c : ℝ,
        HasCompactSupport (fun X => f X-c) →
        let P := GibbsLaw (N:=N) (ReferenceLaw V (fun _ => 1)) s coupling ε
        (∫ X, f X ∂P)=0 → (∫ X, f X^2 ∂P)=1 →
        (∫ X, ‖EuclideanGradient f X‖^2 ∂P) ≤ 1 →
        σ ≤ (∫ X, ‖EuclideanGradient f X‖^2 ∂P) := by
    have hn : 0 < N := by omega
    obtain ⟨clip,K,hK,hclip,hClip⟩ := FixedNGibbsAmplitudeClipping N d hN hd s B κ hs hsd hB hκ Ca Mloc
    obtain ⟨m,hm,hClipM⟩ := hClip (1/1200) (by norm_num)
    let tailTolerance : ℝ := 1/100
    have hTailTolerance : 0 < tailTolerance := by norm_num
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
      have hhalf : Ctail*(R^(-2:ℝ)+R^(-(ForceExponent s))) ≤ tailTolerance/2 := by
        calc
          _ = (2*Ctail*(R^(-2:ℝ)+R^(-(ForceExponent s))))/2 := by ring
          _ ≤ tailTolerance/2 := div_le_div_of_nonneg_right hRate.le (by norm_num)
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
    obtain ⟨C,hC,hApprox⟩ := CutoffCubeApproximation (N*d)
    obtain ⟨Cden,D,hCden,hD,beta,hBeta,hDensity⟩ := FiniteGibbsCommonDensity d N hd (by omega) s B κ 1 hs hsd hB hκ le_rfl Mloc
    obtain ⟨χ,Dχ,hDχ,hχ,hLocal⟩ := FinitePairLocalCutoffEnergy d N hd hN s B hs hsd hB
    let Rb : ℝ := ((N*d:ℕ)+1:ℝ)*R
    have hRb : 0 < Rb := by dsimp [Rb]; positivity
    obtain ⟨Vcap,Scap,hVcap,hScap,hLocalR⟩ := hLocal Rb hRb
    let A := D*C*(R-(-R))^2
    have hA : 0 ≤ A := by dsimp [A]; positivity
    let W := D*(2*m)^2*Vcap+A*8*m^2*Scap
    have hW : 0 ≤ W := by dsimp [W]; positivity
    let T := 1+1200*W
    have hT : 0 < T := by dsimp [T]; positivity
    have hWT : W/T ≤ 1/1200 := by
      rw [div_le_iff₀ hT]
      dsimp [T]; nlinarith
    let Bcoef := 2*K^2/(beta Rb T)
    have hBcoef : 0 ≤ Bcoef := div_nonneg (by positivity) (hBeta Rb T hRb hT).le
    let σ := 1/(1200*(A*Bcoef+1))
    have hσ : 0 < σ := by dsimp [σ]; positivity
    have hσBound : A*Bcoef*σ ≤ 1/1200 := by
      dsimp [σ]
      rw [mul_one_div]
      apply (div_le_iff₀ (show 0 < 1200*(A*Bcoef+1) by positivity)).mpr
      nlinarith
    have probability_centered_square_integrable 
        (ν : Measure (ParticleConfig d N)) [IsProbabilityMeasure ν] (f : (ParticleConfig d N) → ℝ)
        (hf : Integrable f ν) (hSq : Integrable (fun x => f x^2) ν) (c : ℝ) :
        Integrable (fun x => (f x-c)^2) ν := by
      have heq : (fun x => (f x-c)^2) = (fun x => f x^2-(2*c)*f x+c^2) := by
        funext x; ring
      rw [heq]
      exact (hSq.sub (hf.const_mul (2*c))).add (integrable_const (c^2))
    have probability_centered_square_identity 
        (ν : Measure (ParticleConfig d N)) [IsProbabilityMeasure ν] (f : (ParticleConfig d N) → ℝ)
        (hf : Integrable f ν) (hSq : Integrable (fun x => f x^2) ν)
        (hMean : (∫ x, f x ∂ν)=0) (c : ℝ) :
        (∫ x, (f x-c)^2 ∂ν) = (∫ x, f x^2 ∂ν)+c^2 := by
      have heq : (fun x => (f x-c)^2) = (fun x => f x^2-(2*c)*f x+c^2) := by
        funext x; ring
      rw [heq,integral_add (f := fun x => f x^2-(2*c)*f x) (g := fun _ => c^2)
        (hSq.sub (hf.const_mul (2*c))) (integrable_const (c^2)),
        integral_sub hSq (hf.const_mul (2*c)),integral_const_mul,hMean,integral_const]
      simp
    have probability_local_constant_square_bound 
        (ν : Measure (ParticleConfig d N)) [IsProbabilityMeasure ν] (f : (ParticleConfig d N) → ℝ)
        (hf : Integrable f ν) (hSq : Integrable (fun x => f x^2) ν)
        (hUnit : (∫ x, f x^2 ∂ν)=1) (S : Set (ParticleConfig d N)) (hS : MeasurableSet S)
        (hMass : 1/2 ≤ ν.real S) (c e : ℝ)
        (hLocal : (∫ x in S, (f x-c)^2 ∂ν) ≤ e) : c^2 ≤ 4+4*e := by
      have hcI := probability_centered_square_integrable ν f hf hSq c
      have hR : IntegrableOn (fun x => 2*f x^2+2*(f x-c)^2) S ν :=
        (hSq.integrableOn.const_mul 2).add (hcI.integrableOn.const_mul 2)
      have hpoint (x : (ParticleConfig d N)) : c^2 ≤ 2*f x^2+2*(f x-c)^2 := by nlinarith [sq_nonneg (2*f x-c)]
      have hi := integral_mono (integrable_const (c^2) : Integrable (fun _ : (ParticleConfig d N) => c^2) (ν.restrict S))
        hR hpoint
      rw [integral_const,integral_add (hSq.integrableOn.const_mul 2) (hcI.integrableOn.const_mul 2),
        integral_const_mul,integral_const_mul] at hi
      simp only [smul_eq_mul,measureReal_restrict_apply_univ] at hi
      have hInner := (setIntegral_le_integral hSq (Filter.Eventually.of_forall (fun x => sq_nonneg (f x))) (s := S))
      rw [hUnit] at hInner
      have hm := mul_le_mul_of_nonneg_left hMass (sq_nonneg c)
      nlinarith
    have probability_local_approximation_obstruction 
        (ν : Measure (ParticleConfig d N)) [IsProbabilityMeasure ν] (f : (ParticleConfig d N) → ℝ)
        (hf : Integrable f ν) (hSq : Integrable (fun x => f x^2) ν)
        (hMean : (∫ x, f x ∂ν)=0) (hUnit : (∫ x, f x^2 ∂ν)=1)
        (S : Set (ParticleConfig d N)) (hS : MeasurableSet S) (hMass : 1/2 ≤ ν.real S)
        (c e t q : ℝ) (he : 0 ≤ e) (ht : 0 ≤ t) (hq : 0 ≤ q)
        (hLocal : (∫ x in S, (f x-c)^2 ∂ν) ≤ e)
        (hTail : (∫ x in Sᶜ, f x^2 ∂ν) ≤ t) (hOutside : ν.real Sᶜ ≤ q) :
        1 ≤ e+2*t+(8+8*e)*q := by
      have hcI := probability_centered_square_integrable ν f hf hSq c
      have hc := probability_local_constant_square_bound ν f hf hSq hUnit S hS hMass c e hLocal
      have hR : IntegrableOn (fun x => 2*f x^2+2*c^2) Sᶜ ν :=
        (hSq.integrableOn.const_mul 2).add (integrable_const (2*c^2))
      have hpoint (x : (ParticleConfig d N)) : (f x-c)^2 ≤ 2*f x^2+2*c^2 := by nlinarith [sq_nonneg (f x+c)]
      have hi := integral_mono (hcI.integrableOn (s := Sᶜ)) hR hpoint
      rw [integral_add (hSq.integrableOn.const_mul 2) (integrable_const (2*c^2)),
        integral_const_mul,integral_const] at hi
      simp only [smul_eq_mul,measureReal_restrict_apply_univ] at hi
      have hO : 2*c^2*ν.real Sᶜ ≤ (8+8*e)*q := by
        have h1 := mul_le_mul_of_nonneg_right (show 2*c^2 ≤ 8+8*e by nlinarith) (measureReal_nonneg (μ := ν) (s := Sᶜ))
        have h2 := mul_le_mul_of_nonneg_left hOutside (show 0 ≤ 8+8*e by positivity)
        exact h1.trans h2
      have hSplit := integral_add_compl hS hcI
      rw [probability_centered_square_identity ν f hf hSq hMean c,hUnit] at hSplit
      nlinarith [sq_nonneg c]
    have probability_small_local_approximation_impossible 
        (ν : Measure (ParticleConfig d N)) [IsProbabilityMeasure ν] (f : (ParticleConfig d N) → ℝ)
        (hf : Integrable f ν) (hSq : Integrable (fun x => f x^2) ν)
        (hMean : (∫ x, f x ∂ν)=0) (hUnit : (∫ x, f x^2 ∂ν)=1)
        (S : Set (ParticleConfig d N)) (hS : MeasurableSet S) (hMass : 1/2 ≤ ν.real S) (c : ℝ)
        (hLocal : (∫ x in S, (f x-c)^2 ∂ν) ≤ 1/100)
        (hTail : (∫ x in Sᶜ, f x^2 ∂ν) ≤ 1/100) (hOutside : ν.real Sᶜ ≤ 1/100) : False := by
      have h := probability_local_approximation_obstruction ν f hf hSq hMean hUnit S hS hMass
        c (1/100) (1/100) (1/100) (by norm_num) (by norm_num) (by norm_num) hLocal hTail hOutside
      norm_num at h
    refine ⟨σ,hσ,?_⟩
    intro V hV hmin hlocal hgrowth coupling ε ha haB hε f hf c hcf
    dsimp only
    intro hmean hunit henergy
    let P := GibbsLaw (N:=N) (ReferenceLaw V (fun _ => 1)) s coupling ε
    let U := PairInteraction (d:=d) (N:=N) s coupling ε
    let Q : Set (ParticleConfig d N) := {X | ∀ k, |X k| ≤ R}
    let Ball := closedBall (0:ParticleConfig d N) Rb
    have hone : BoundedMultiplier d 1 (fun _ => 1) := by
      refine ⟨measurable_const,1,1,zero_lt_one,le_rfl,?_,fun x => ⟨le_rfl,le_rfl⟩⟩
      norm_num
    obtain ⟨_,_,_,_,_,hpm,hpn,_,hprob,hlaw,hupper,hlower⟩ :=
      hDensity V (fun _ => 1) hV hmin hlocal hone N (by omega) le_rfl coupling ε ha haB hε
    letI : IsProbabilityMeasure P := hprob
    let ρ : ParticleConfig d N → ℝ≥0 := fun X => ⟨GibbsLebesgueDensity (N:=N) V (fun _ => 1) s coupling ε X,hpn X⟩
    have hρ : Measurable ρ := hpm.subtype_mk
    have hP : P = volume.withDensity (fun X => (ρ X:ℝ≥0∞)) := by
      change GibbsLaw (N:=N) (ReferenceLaw V (fun _ => 1)) s coupling ε = _
      rw [hlaw]
      congr 1
      funext X
      change ENNReal.ofReal (ρ X:ℝ) = (ρ X:ℝ≥0∞)
      simp only [ENNReal.ofReal_coe_nnreal]
    have hfi := ((FiniteGibbsSquaredTestTail N d hn hd s B κ hs hsd hB hκ Ca).choose_spec.2
      V hV hmin hgrowth coupling ε ha haB hε f hf c hcf)
    have hfI : Integrable f P := by
      have hi : Integrable (fun X => f X-c) P := (hf.continuous.sub continuous_const).integrable_of_hasCompactSupport (μ:=P) hcf
      have hic : Integrable (fun _ : ParticleConfig d N => c) P := integrable_const c
      exact (hi.add hic).congr (Eventually.of_forall (fun X => sub_add_cancel (f X) c))
    have hQ : MeasurableSet Q := by
      simp only [Q,Set.ofPred_forall]
      exact MeasurableSet.iInter (fun k => measurableSet_le ((continuous_abs.comp (PiLp.continuous_apply 2 _ k)).measurable) measurable_const)
    have hsubset : Q ⊆ Ball := by
      intro X hx
      rw [mem_closedBall,dist_zero_right]
      exact (ConfigurationCoordinateTransport N d).2.2.2.1 R hR.le X hx
    have hUC : ContDiff ℝ 1 U :=
      (PairInteractionSource d N s coupling ε hs hsd ha hε).1.of_le (by norm_num)
    obtain ⟨_,hGi,hErrI,hGB,hErrB⟩ := (hLocalR coupling ε ha haB hε).2 T hT
    have hSource : (∫ X in Q, ‖EuclideanGradient (fun Y => χ T (U Y)) X‖^2) ≤ Scap/T :=
      (setIntegral_mono_set hGi (Eventually.of_forall (fun X => sq_nonneg _)) (Eventually.of_forall hsubset)).trans hGB
    have hError : (∫ X in Q, (1-χ T (U X))^2) ≤ Vcap/T :=
      (setIntegral_mono_set hErrI (Eventually.of_forall (fun X => sq_nonneg _)) (Eventually.of_forall hsubset)).trans hErrB
    have hUpper : ∀ X ∈ Q, (ρ X:ℝ) ≤ D := by
      intro X _
      have he : Real.exp (-(κ/2)*‖X‖^2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖X‖])
      exact (hupper X).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left he hD.le)
    have hLower : ∀ X ∈ Q, U X ≤ 2*T → beta Rb T ≤ (ρ X:ℝ) := by
      intro X hx hUX
      exact hlower Rb T hRb hT X ((ConfigurationCoordinateTransport N d).2.2.2.1 R hR.le X hx) hUX
    have hχrange : ∀ u, 0 ≤ χ T u ∧ χ T u ≤ 1 ∧ (2*T ≤ u → χ T u=0) := by
      intro u
      exact ⟨((hχ T hT).2 u).1,((hχ T hT).2 u).2.1,((hχ T hT).2 u).2.2.2.1⟩
    have hhrange : ∀ u, |clip m u| ≤ 2*m ∧ |deriv (clip m) u| ≤ K :=
      fun u => ⟨((hclip m hm).2 u).1,((hclip m hm).2 u).2.1⟩
    have hfinite : IsFiniteMeasure (volume.withDensity (fun X => (ρ X:ℝ≥0∞))) := by rw [← hP]; infer_instance
    have hSq : Integrable (fun X => f X^2) (volume.withDensity (fun X => (ρ X:ℝ≥0∞))) := by
      rw [← hP]; exact hfi.2.1
    have hEi : Integrable (fun X => ‖EuclideanGradient f X‖^2) (volume.withDensity (fun X => (ρ X:ℝ≥0∞))) := by
      rw [← hP]; exact hfi.2.2.1
    let χc := χ T
    let hc := clip m
    have hχC : ContDiff ℝ 1 χc := (hχ T hT).1.of_le (by norm_num)
    have hhC : ContDiff ℝ 1 hc := (hclip m hm).1.of_le (by norm_num)
    let e := ConfigurationFlatten N d
    let Qf := {y : EuclideanSpace ℝ (Fin (N*d)) | ∀ k, -R ≤ y k ∧ y k ≤ R}
    let ν := volume.withDensity (fun X => (ρ X : ℝ≥0∞))
    let νf := volume.withDensity (fun y => (ρ (e.symm y) : ℝ≥0∞))
    have he : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
    have hmap : ν.map e = νf := (ConfigurationCoordinateTransport N d).2.2.2.2.2 ρ
    have hpre : e ⁻¹' Qf = Q := by
      ext X
      exact ((ConfigurationCoordinateTransport N d).2.2.1 R X).symm
    have hweighted (g : ParticleConfig d N → ℝ) (Scap : Set (EuclideanSpace ℝ (Fin (N*d)))) :
        (∫ y in Scap, g (e.symm y) ∂νf) = ∫ X in e ⁻¹' Scap, g X ∂ν := by
      rw [← hmap,he.setIntegral_map]
      simp only [LinearIsometryEquiv.symm_apply_apply]
    have hglobal (g : ParticleConfig d N → ℝ) : (∫ y, g (e.symm y) ∂νf) = ∫ X, g X ∂ν := by
      rw [← hmap,he.integral_map]
      simp only [LinearIsometryEquiv.symm_apply_apply]
    have hvol (g : ParticleConfig d N → ℝ) : (∫ y in Qf, g (e.symm y)) = ∫ X in Q, g X := by
      rw [(ConfigurationCoordinateTransport N d).2.2.2.2.1 g Qf,hpre]
    have hgrad (y) : ‖EuclideanGradient (f ∘ e.symm) y‖ = ‖EuclideanGradient f (e.symm y)‖ :=
      ((ConfigurationCoordinateTransport N d).2.1 f hf).2 y
    have hgradχ (y) : ‖EuclideanGradient (fun z => χc (U (e.symm z))) y‖ =
        ‖EuclideanGradient (fun X => χc (U X)) (e.symm y)‖ :=
      ((ConfigurationCoordinateTransport N d).2.1 (fun X => χc (U X)) (hχC.comp hUC)).2 y
    have hSf : Integrable (fun y => (f (e.symm y))^2) νf := by
      rw [← hmap,he.integrable_map_iff]
      simpa only [Function.comp_def,LinearIsometryEquiv.symm_apply_apply] using hSq
    have hEf : Integrable (fun y => ‖EuclideanGradient (f ∘ e.symm) y‖^2) νf := by
      simp_rw [hgrad]
      rw [← hmap,he.integrable_map_iff]
      simpa only [Function.comp_def,LinearIsometryEquiv.symm_apply_apply] using hEi
    letI : IsFiniteMeasure ν := hfinite
    have hfinitef : IsFiniteMeasure νf := by rw [← hmap]; infer_instance
    have hρf : Measurable (fun y => ρ (e.symm y)) := hρ.comp e.symm.toHomeomorph.measurable
    have hUf : ContDiff ℝ 1 (U ∘ e.symm) := hUC.comp e.symm.toContinuousLinearEquiv.contDiff
    have hFf : ContDiff ℝ 1 (f ∘ e.symm) := (ConfigurationCoordinateTransport N d).2.1 f hf |>.1
    have hmem (y) (hy : y ∈ Qf) : e.symm y ∈ Q := by
      rw [← hpre]
      simpa only [mem_preimage,LinearIsometryEquiv.apply_symm_apply] using hy
    have hErrf : (∫ y in Qf, (1-χc (U (e.symm y)))^2) ≤ Vcap/T := by rw [hvol (fun X => (1-χc (U X))^2)]; exact hError
    have hSourcef : (∫ y in Qf, ‖EuclideanGradient (fun z => χc (U (e.symm z))) y‖^2) ≤ Scap/T := by
      simp_rw [hgradχ]
      rw [hvol (fun X => ‖EuclideanGradient (fun Y => χc (U Y)) X‖^2)]
      exact hSource
    have hCubeResult := hApprox (-R) R (by linarith) (f ∘ e.symm) (U ∘ e.symm) hFf hUf
      (fun y => ρ (e.symm y)) hρf hfinitef hSf hEf χc hc hχC hhC m T D (beta Rb T) K Vcap Scap
      hm hT hD.le (hBeta Rb T hRb hT) hK.le hVcap hScap hχrange hhrange
      (fun y hy => hUpper _ (hmem y hy)) (fun y hy hu => hLower _ (hmem y hy) hu) hErrf hSourcef
    let a := (∫ y in Qf, χc (U (e.symm y))*hc (f (e.symm y)))/(R-(-R))^(N*d)
    have haError := hCubeResult.2.2.2
    change (∫ y in Qf, (f (e.symm y)-a)^2 ∂νf) ≤ _ at haError
    rw [hweighted (fun X => (f X-a)^2) Qf,hpre] at haError
    change (∫ X in Q, (f X-a)^2 ∂ν) ≤
      3*((∫ y, (f (e.symm y)-hc (f (e.symm y)))^2 ∂νf)+D*(2*m)^2*(Vcap/T)+
        D*C*(R-(-R))^2*((2*K^2/(beta Rb T))*(∫ y in Qf, ‖EuclideanGradient (f ∘ e.symm) y‖^2 ∂νf)+8*m^2*(Scap/T))) at haError
    simp_rw [hgrad] at haError
    rw [hglobal (fun X => (f X-hc (f X))^2),hweighted (fun X => ‖EuclideanGradient f X‖^2) Qf,hpre] at haError
    dsimp only [ν] at haError
    rw [← hP] at haError
    have hClipErr := (hClipM V hV hmin hlocal hgrowth coupling ε ha haB hε f hf c hcf hunit henergy).2.2
    have ht := hTail V hV hmin hgrowth coupling ε ha haB hε
    have hTestTail := (ht.2.2 f hf c hcf).2 hunit henergy
    have hMassTail : P.real Qᶜ ≤ 1/100 := ht.2.1
    by_contra hnot
    have hEnergySmall : (∫ X, ‖EuclideanGradient f X‖^2 ∂P) ≤ σ := (lt_of_not_ge hnot).le
    have hIn := setIntegral_le_integral hfi.2.2.1 (Eventually.of_forall (fun X => sq_nonneg _)) (s:=Q)
    have hSmall : A*Bcoef*(∫ X in Q, ‖EuclideanGradient f X‖^2 ∂P) ≤ 1/1200 :=
      (mul_le_mul_of_nonneg_left (hIn.trans hEnergySmall) (mul_nonneg hA hBcoef)).trans hσBound
    have hRest : D*(2*m)^2*(Vcap/T)+A*8*m^2*(Scap/T) ≤ 1/1200 := by
      calc
        _ = W/T := by dsimp [W]; ring
        _ ≤ _ := hWT
    have hLocalError : (∫ X in Q, (f X-a)^2 ∂P) ≤ 1/100 := by
      change (∫ X in Q, (f X-a)^2 ∂P) ≤
        3*((∫ X, (f X-clip m (f X))^2 ∂P)+D*(2*m)^2*(Vcap/T)+
          A*(Bcoef*(∫ X in Q, ‖EuclideanGradient f X‖^2 ∂P)+8*m^2*(Scap/T))) at haError
      nlinarith
    have hMass : 1/2 ≤ P.real Q := by
      have hm := measureReal_add_measureReal_compl (μ:=P) hQ
      have hu : P.real Set.univ=1 := by simp
      rw [hu] at hm
      linarith
    exact probability_small_local_approximation_impossible P f hfI hfi.2.1 hmean hunit Q hQ hMass a
      hLocalError hTestTail hMassTail
  have fixed_natural_pi (N d : ℕ) (hN : 2 ≤ N) (hd : 3 ≤ d)
      (s B κ : ℝ) (hs : 0 < s) (hsd : s ≤ (d:ℝ)-2)
      (hB : 0 ≤ B) (hκ : 0 < κ) (Ca Mloc : ℝ → ℝ) :
      ∃ rate : ℝ, 0 < rate ∧ ∀ V : OneParticle d → ℝ, PotentialBounds d κ V →
        (∀ x, V 0 ≤ V x) →
        (∀ R, 0 < R → ∀ x, ‖x‖ ≤ R → V x-V 0 ≤ Mloc R) →
        (∀ a, 0 < a → ∀ x, EuclideanLaplacian V x ≤ a*‖EuclideanGradient V x‖^ForceExponent s+Ca a) →
        ∀ coupling ε : ℝ, 0 ≤ coupling → coupling ≤ B → 0 < ε →
        ∀ f : ParticleConfig d N → ℝ, ContDiff ℝ 1 f → ∀ c : ℝ,
        HasCompactSupport (fun X => f X-c) →
        let P := GibbsLaw (N:=N) (ReferenceLaw V (fun _ => 1)) s coupling ε
        IsProbabilityMeasure P ∧
        rate * ProbabilityTheory.variance f P ≤ (∫ X, ‖EuclideanGradient f X‖^2 ∂P) := by
    have hn : 0 < N := by omega
    obtain ⟨σ,hσ,hgap⟩ := fixed_normalized_gap N d hN hd s B κ hs hsd hB hκ Ca Mloc
    refine ⟨min σ 1,lt_min hσ zero_lt_one,?_⟩
    intro V hV hmin hlocal hgrowth coupling ε ha haB hε f hf c hcf
    dsimp only
    let P := GibbsLaw (N:=N) (ReferenceLaw V (fun _ => 1)) s coupling ε
    have hfi := ((FiniteGibbsSquaredTestTail N d hn hd s B κ hs hsd hB hκ Ca).choose_spec.2
      V hV hmin hgrowth coupling ε ha haB hε f hf c hcf)
    letI : IsProbabilityMeasure P := hfi.1
    refine ⟨hfi.1,?_⟩
    have hfI : Integrable f P := by
      have hi : Integrable (fun X => f X-c) P := (hf.continuous.sub continuous_const).integrable_of_hasCompactSupport (μ:=P) hcf
      have hic : Integrable (fun _ : ParticleConfig d N => c) P := integrable_const c
      exact (hi.add hic).congr (Eventually.of_forall (fun X => sub_add_cancel (f X) c))
    let a := ∫ X, f X ∂P
    let v := ProbabilityTheory.variance f P
    have hv : 0 ≤ v := ProbabilityTheory.variance_nonneg f P
    have hE : 0 ≤ ∫ X, ‖EuclideanGradient f X‖^2 ∂P := integral_nonneg (fun X => sq_nonneg _)
    change min σ 1 * v ≤ ∫ X, ‖EuclideanGradient f X‖^2 ∂P
    by_cases hv0 : v=0
    · simpa only [hv0,mul_zero] using hE
    have hvp : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0)
    let t := (Real.sqrt v)⁻¹
    let g := fun X => t*(f X-a)
    have hg : ContDiff ℝ 1 g := contDiff_const.mul (hf.sub contDiff_const)
    have hcg : HasCompactSupport (fun X => g X-t*(c-a)) := by
      have he : (fun X => g X-t*(c-a)) = fun X => t*(f X-c) := by funext X; dsimp [g]; ring
      rw [he]
      exact hcf.mul_left
    have hmean : (∫ X, g X ∂P)=0 := by
      dsimp [g]
      rw [integral_const_mul,integral_sub hfI (integrable_const a)]
      simp [a]
    have hsquare : (∫ X, g X^2 ∂P)=1 := by
      have he : (fun X => g X^2) = fun X => t^2*(f X-a)^2 := by funext X; dsimp [g]; ring
      rw [he,integral_const_mul,← ProbabilityTheory.variance_eq_integral hf.continuous.measurable.aemeasurable]
      change (Real.sqrt v)⁻¹^2*v=1
      rw [inv_pow,Real.sq_sqrt hv]
      exact inv_mul_cancel₀ hv0
    have hgradient : (∫ X, ‖EuclideanGradient g X‖^2 ∂P) = v⁻¹*(∫ X, ‖EuclideanGradient f X‖^2 ∂P) := by
      have he : (fun X => ‖EuclideanGradient g X‖^2) = fun X => v⁻¹*‖EuclideanGradient f X‖^2 := by
        funext X
        have hgrad : EuclideanGradient g X = t • EuclideanGradient f X := by
          simp only [g,EuclideanGradient,gradient,fderiv_const_mul ((hf.sub contDiff_const).differentiable (by norm_num) X),fderiv_sub_const,map_smul]
        rw [hgrad,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
        congr 1
        dsimp [t]
        rw [inv_pow,Real.sq_sqrt hv]
      rw [he,integral_const_mul]
    have hh : min σ 1 ≤ v⁻¹*(∫ X, ‖EuclideanGradient f X‖^2 ∂P) := by
      by_cases he : (∫ X, ‖EuclideanGradient g X‖^2 ∂P) ≤ 1
      · have hgg : σ ≤ ∫ X, ‖EuclideanGradient g X‖^2 ∂P := hgap V hV hmin hlocal hgrowth coupling ε ha haB hε g hg _ hcg hmean hsquare he
        rw [hgradient] at hgg
        exact (min_le_left _ _).trans hgg
      · rw [hgradient] at he
        exact (min_le_right _ _).trans (le_of_lt (lt_of_not_ge he))
    have hscaled := mul_le_mul_of_nonneg_right hh hv
    rw [mul_assoc,mul_comm (∫ X, ‖EuclideanGradient f X‖^2 ∂P) v,
      ← mul_assoc,inv_mul_cancel₀ hv0,one_mul] at hscaled
    exact hscaled
  classical
  have tilt_transfer {α : Type} [MeasurableSpace α] [Nonempty α]
      (P : Measure α) [IsProbabilityMeasure P] (b : α → ℝ) (hb : Measurable b)
      (l u c : ℝ) (hl : 0 < l) (hc : 0 < c) (hbound : ∀ x, l ≤ b x ∧ b x ≤ u)
      (f e : α → ℝ) (hf : MemLp f 2 P) (he : Integrable e P) (hep : ∀ x, 0 ≤ e x)
      (hPI : c*ProbabilityTheory.variance f P ≤ ∫ x, e x ∂P) :
      let Q := P.withDensity (fun x => ENNReal.ofReal (b x/(∫ y, b y ∂P)))
      (c*l/u)*ProbabilityTheory.variance f Q ≤ ∫ x, e x ∂Q := by
    let Z := ∫ x, b x ∂P
    let Q := P.withDensity (fun x => ENNReal.ofReal (b x/Z))
    have hu : 0 < u := hl.trans_le ((hbound (Classical.arbitrary α)).1.trans (hbound _).2)
    have hi : Integrable b P := (integrable_const u).mono' hb.aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hl.le.trans (hbound x).1)]
        exact (hbound x).2)
    have hlo : l ≤ Z := by simpa [Z] using integral_mono (integrable_const l) hi (fun x => (hbound x).1)
    have hZ : 0 < Z := hl.trans_le hlo
    have hpos (x) : 0 ≤ b x/Z := div_nonneg (hl.le.trans (hbound x).1) hZ.le
    have hm : Measurable (fun x => ENNReal.ofReal (b x/Z)) := (hb.div_const Z).ennreal_ofReal
    have hQprob : IsProbabilityMeasure Q := by
      apply isProbabilityMeasure_iff.mpr
      change P.withDensity (fun x => ENNReal.ofReal (b x/Z)) Set.univ = 1
      rw [withDensity_apply _ MeasurableSet.univ]
      simp only [Measure.restrict_univ]
      rw [← ofReal_integral_eq_lintegral_ofReal (hi.div_const Z) (Eventually.of_forall hpos), integral_div]
      simp [Z, hZ.ne']
    letI : IsProbabilityMeasure Q := hQprob
    have hhigh : Q ≤ ENNReal.ofReal (u/Z) • P := by
      rw [← withDensity_const]
      apply withDensity_mono
      exact Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_right (hbound x).2 hZ.le)
    have hlow : ENNReal.ofReal (l/Z) • P ≤ Q := by
      rw [← withDensity_const]
      apply withDensity_mono
      exact Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_right (hbound x).1 hZ.le)
    have hfQ : MemLp f 2 Q := hf.of_measure_le_smul ENNReal.ofReal_ne_top hhigh
    have heQ : Integrable e Q := he.of_measure_le_smul ENNReal.ofReal_ne_top hhigh
    have hEnergy : (l/Z)*(∫ x, e x ∂P) ≤ ∫ x, e x ∂Q := by
      have h := integral_mono_measure hlow (Eventually.of_forall hep) heQ
      simpa only [integral_smul_measure, ENNReal.toReal_ofReal (div_nonneg hl.le hZ.le),
        smul_eq_mul] using h
    let a := ∫ x, f x ∂P
    have hgI : Integrable (fun x => (f x-a)^2) P := (hf.sub (memLp_const a)).integrable_sq
    have hcomp : (∫ x, (f x-a)^2 ∂Q) ≤ (u/Z)*(∫ x, (f x-a)^2 ∂P) := by
      have hh := integral_mono_measure hhigh (Eventually.of_forall (fun x => sq_nonneg (f x-a)))
        (hgI.smul_measure ENNReal.ofReal_ne_top)
      simpa only [integral_smul_measure, ENNReal.toReal_ofReal (div_nonneg hu.le hZ.le), smul_eq_mul] using hh
    have hvar : ProbabilityTheory.variance f Q ≤ (u/Z)*ProbabilityTheory.variance f P := by
      have hv := ProbabilityTheory.variance_eq_sub (hfQ.sub (memLp_const a))
      change ProbabilityTheory.variance (fun x => f x-a) Q =
        (∫ x, (f x-a)^2 ∂Q)-(∫ x, f x-a ∂Q)^2 at hv
      rw [ProbabilityTheory.variance_sub_const hfQ.aestronglyMeasurable a] at hv
      change ProbabilityTheory.variance f Q = (∫ x, (f x-a)^2 ∂Q)-(∫ x, f x-a ∂Q)^2 at hv
      have hmin : ProbabilityTheory.variance f Q ≤ ∫ x, (f x-a)^2 ∂Q := by nlinarith [sq_nonneg (∫ x, f x-a ∂Q)]
      have hbase : (∫ x, (f x-a)^2 ∂P) = ProbabilityTheory.variance f P :=
        (ProbabilityTheory.variance_eq_integral hf.aestronglyMeasurable.aemeasurable).symm
      rw [hbase] at hcomp
      exact hmin.trans hcomp
    have hcancel : (c*l/u)*(u/Z) = (l/Z)*c := by field_simp
    calc
      _ ≤ (c*l/u)*((u/Z)*ProbabilityTheory.variance f P) :=
        mul_le_mul_of_nonneg_left hvar (by positivity)
      _ = (l/Z)*(c*ProbabilityTheory.variance f P) := by rw [← mul_assoc, hcancel, mul_assoc]
      _ ≤ (l/Z)*(∫ x, e x ∂P) := mul_le_mul_of_nonneg_left hPI (by positivity)
      _ ≤ _ := hEnergy
  obtain ⟨rate,hrate,hbase⟩ := fixed_natural_pi N d hN hd s B κ hs hsd hB hκ Ca Mloc
  have hLN : 0 < L^N := pow_pos (by linarith) N
  refine ⟨rate,rate/L^N,hrate,div_pos hrate hLN,rfl,?_⟩
  intro V hV hmin hlocal hgrowth b hb coupling ε ha haB hε f hf c hcf
  dsimp only
  let P := GibbsLaw (N:=N) (ReferenceLaw V (fun _ => 1)) s coupling ε
  let Q := GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε
  let w := fun X : ParticleConfig d N => ∏ i : Fin N, b (ParticlePosition X i)
  have hbasePI := hbase V hV hmin hlocal hgrowth coupling ε ha haB hε f hf c hcf
  letI : IsProbabilityMeasure P := hbasePI.1
  obtain ⟨_,hQprob,hwm,_,_,hTilt,m,hm,hprod⟩ :=
    FiniteGibbsProductBoundedTilt N d (by omega) V b κ L hκ hL hV hb s coupling ε hs ha hε
  obtain ⟨F,hFb⟩ := hcf.exists_bound_of_continuous (hf.continuous.sub continuous_const)
  let A := max 0 F+|c|
  have hfbound (X) : |f X| ≤ A := by
    have h := abs_add_le (f X-c) c
    have he : f X-c+c=f X := by ring
    rw [he] at h
    have hb : |f X-c| ≤ F := by simpa only [Real.norm_eq_abs] using hFb X
    dsimp [A]; linarith [le_max_right (0:ℝ) F]
  have hfLp : MemLp f 2 P := MemLp.of_bound hf.continuous.aestronglyMeasurable A
    (Eventually.of_forall fun X => by simpa only [Real.norm_eq_abs] using hfbound X)
  have hderiv : fderiv ℝ (fun X => f X-c)=fderiv ℝ f := by funext X; rw [fderiv_sub_const c]
  have hcder := hcf.fderiv ℝ
  rw [hderiv] at hcder
  have hce : HasCompactSupport (fun X => ‖fderiv ℝ f X‖^2) :=
    hcder.comp_left (g:=fun A : ParticleConfig d N →L[ℝ] ℝ => ‖A‖^2) (by simp)
  have hider := ((hf.continuous_fderiv (by norm_num)).norm.pow 2).integrable_of_hasCompactSupport (μ:=P) hce
  have he : Integrable (fun X => ‖EuclideanGradient f X‖^2) P :=
    hider.congr (Eventually.of_forall fun X => by
      change ‖fderiv ℝ f X‖^2=‖EuclideanGradient f X‖^2
      rw [(GradientNormIdentity f X).2])
  have h := tilt_transfer (α:=ParticleConfig d N) P w hwm (m^N) (L^N*m^N) rate (pow_pos hm N) hrate hprod
    f (fun X => ‖EuclideanGradient f X‖^2) hfLp he (fun X => sq_nonneg _) hbasePI.2
  dsimp only at h
  rw [← hTilt] at h
  have hcoef : rate*m^N/(L^N*m^N)=rate/L^N := by field_simp
  rw [hcoef] at h
  have hsharp : rate*ProbabilityTheory.variance f Q ≤ L^N*(∫ X, ‖EuclideanGradient f X‖^2 ∂Q) :=
    by
      have hh := (div_le_iff₀ hLN).mp (by simpa only [div_mul_eq_mul_div] using h)
      exact hh.trans_eq (mul_comm _ _)
  exact ⟨hQprob,hsharp,h⟩

#print axioms FixedNGibbsBoundedBackgroundPI
