module

public import Tablet.AtomicTestClipping
public import Tablet.CutoffCubeApproximation
public import Tablet.LawVariance
public import Tablet.BoundedMultiplier
public import Mathlib.Probability.Moments.Variance

@[expose] public section

open MeasureTheory Set Filter
open scoped ContDiff ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 1600000

namespace AtomicOneSitePI

private theorem cube_norm (d : ℕ) (R : ℝ) (hR : 0 < R) (x : OneParticle d)
    (hx : ∀ k : Fin d, -R ≤ x k ∧ x k ≤ R) : ‖x‖ ≤ (d : ℝ)*R+1 := by
  have hs : ∑ k : Fin d, ‖x k‖^2 ≤ (d : ℝ)*R^2 := by
    calc
      _ ≤ ∑ _k : Fin d, R^2 := Finset.sum_le_sum (fun k _ =>
        pow_le_pow_left₀ (norm_nonneg _) (by simpa only [Real.norm_eq_abs, abs_le] using hx k) 2)
      _ = _ := by simp
  have hn : ‖x‖^2 = ∑ k : Fin d, ‖x k‖^2 := EuclideanSpace.norm_sq_eq x
  have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
  have hd1 : (d : ℝ) ≤ (d : ℝ)^2 := by
    by_cases hd : d = 0
    · simp [hd]
    · have hh : 1 ≤ (d : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd
      nlinarith
  have hp : ‖x‖^2 ≤ ((d : ℝ)*R)^2 := by
    calc
      _ ≤ (d : ℝ)*R^2 := hn.trans_le hs
      _ ≤ (d : ℝ)^2*R^2 := mul_le_mul_of_nonneg_right hd1 (sq_nonneg R)
      _ = _ := by ring
  have hpos : 0 ≤ (d : ℝ)*R := mul_nonneg hd0 hR.le
  have hh := (sq_le_sq₀ (norm_nonneg x) hpos).mp hp
  linarith

private theorem centered_integrable {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (f : α → ℝ)
    (hf : Integrable f ν) (hSq : Integrable (fun x => f x^2) ν) (c : ℝ) :
    Integrable (fun x => (f x-c)^2) ν := by
  have he : (fun x => (f x-c)^2) = fun x => f x^2-(2*c)*f x+c^2 := by funext x; ring
  rw [he]
  exact (hSq.sub (hf.const_mul (2*c))).add (integrable_const (c^2))

private theorem centered_identity {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (f : α → ℝ)
    (hf : Integrable f ν) (hSq : Integrable (fun x => f x^2) ν)
    (hmean : (∫ x, f x ∂ν) = 0) (c : ℝ) :
    (∫ x, (f x-c)^2 ∂ν) = (∫ x, f x^2 ∂ν)+c^2 := by
  have he : (fun x => (f x-c)^2) = fun x => f x^2-(2*c)*f x+c^2 := by funext x; ring
  rw [he, integral_add (f := fun x => f x^2-(2*c)*f x) (g := fun _ => c^2)
    (hSq.sub (hf.const_mul (2*c))) (integrable_const (c^2)),
    integral_sub (f := fun x => f x^2) (g := fun x => (2*c)*f x)
      hSq (hf.const_mul (2*c)), integral_const_mul, hmean, integral_const]
  simp

private theorem local_obstruction {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (f : α → ℝ)
    (hf : Integrable f ν) (hSq : Integrable (fun x => f x^2) ν)
    (hmean : (∫ x, f x ∂ν) = 0) (hunit : (∫ x, f x^2 ∂ν) = 1)
    (Q : Set α) (hQ : MeasurableSet Q) (hmass : 1/2 ≤ ν.real Q) (c : ℝ)
    (hlocal : (∫ x in Q, (f x-c)^2 ∂ν) ≤ 1/100)
    (htail : (∫ x in Qᶜ, f x^2 ∂ν) ≤ 1/100)
    (hout : ν.real Qᶜ ≤ 1/100) : False := by
  have hci := centered_integrable ν f hf hSq c
  have hpoint (x) : c^2 ≤ 2*f x^2+2*(f x-c)^2 := by nlinarith [sq_nonneg (2*f x-c)]
  have h := integral_mono (μ := ν.restrict Q) (integrable_const (c^2))
    ((hSq.integrableOn.const_mul 2).add (hci.integrableOn.const_mul 2)) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_const, integral_add (μ := ν.restrict Q)
    (hSq.integrableOn.const_mul 2) (hci.integrableOn.const_mul 2),
    integral_const_mul, integral_const_mul] at h
  simp only [smul_eq_mul, measureReal_restrict_apply_univ] at h
  have hinner := setIntegral_le_integral hSq (Eventually.of_forall (fun x => sq_nonneg (f x))) (s := Q)
  rw [hunit] at hinner
  have hc : c^2 ≤ 4+4*(1/100 : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hmass (sq_nonneg c)
    nlinarith
  have hpoint' (x) : (f x-c)^2 ≤ 2*f x^2+2*c^2 := by nlinarith [sq_nonneg (f x+c)]
  have h' := integral_mono (μ := ν.restrict Qᶜ) hci.integrableOn
    ((hSq.integrableOn.const_mul 2).add (integrable_const (2*c^2))) hpoint'
  simp only [Pi.add_apply] at h'
  rw [integral_add (μ := ν.restrict Qᶜ) (hSq.integrableOn.const_mul 2) (integrable_const (2*c^2)),
    integral_const_mul, integral_const] at h'
  simp only [smul_eq_mul, measureReal_restrict_apply_univ] at h'
  have ho : 2*c^2*ν.real Qᶜ ≤ (8+8*(1/100 : ℝ))*(1/100) :=
    (mul_le_mul_of_nonneg_right (by nlinarith : 2*c^2 ≤ 8+8*(1/100 : ℝ))
      measureReal_nonneg).trans (mul_le_mul_of_nonneg_left hout (by norm_num))
  have hsplit := integral_add_compl hQ hci
  rw [centered_identity ν f hf hSq hmean c, hunit] at hsplit
  nlinarith [sq_nonneg c]

private theorem rescale {d : ℕ} (P : Measure (OneParticle d)) [IsProbabilityMeasure P]
    (σ : ℝ) (hσ : 0 < σ)
    (htests : ∀ f : OneParticle d → ℝ, ContDiff ℝ 1 f → ∀ c : ℝ,
      HasCompactSupport (fun x => f x-c) → Integrable (fun x => f x^2) P)
    (hgap : ∀ f : OneParticle d → ℝ, ContDiff ℝ 1 f → ∀ c : ℝ,
      HasCompactSupport (fun x => f x-c) →
      (∫ x, f x ∂P) = 0 → (∫ x, f x^2 ∂P) = 1 →
      (∫ x, ‖EuclideanGradient f x‖^2 ∂P) ≤ 1 →
      σ ≤ (∫ x, ‖EuclideanGradient f x‖^2 ∂P))
    (f : OneParticle d → ℝ) (hf : ContDiff ℝ 1 f) (c : ℝ)
    (hc : HasCompactSupport (fun x => f x-c)) :
    min σ 1*LawVariance P f ≤ (∫ x, ‖EuclideanGradient f x‖^2 ∂P) := by
  have hi : Integrable f P :=
    ((memLp_two_iff_integrable_sq hf.continuous.aestronglyMeasurable).mpr
      (htests f hf c hc)).integrable (by norm_num)
  let a := ∫ x, f x ∂P
  let v := ProbabilityTheory.variance f P
  have hv : 0 ≤ v := ProbabilityTheory.variance_nonneg f P
  have hE : 0 ≤ ∫ x, ‖EuclideanGradient f x‖^2 ∂P := integral_nonneg (fun _ => sq_nonneg _)
  by_cases hv0 : v = 0
  · simpa only [LawVariance, v, hv0, mul_zero] using hE
  have hvp : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0)
  let t := (Real.sqrt v)⁻¹
  let g := fun x => t*(f x-a)
  have hg : ContDiff ℝ 1 g := contDiff_const.mul (hf.sub contDiff_const)
  have hcg : HasCompactSupport (fun x => g x-t*(c-a)) := by
    have he : (fun x => g x-t*(c-a)) = fun x => t*(f x-c) := by funext x; dsimp [g]; ring
    rw [he]; exact hc.mul_left
  have hmean : (∫ x, g x ∂P) = 0 := by
    dsimp [g]
    rw [integral_const_mul, integral_sub hi (integrable_const a)]
    simp [a]
  have hsquare : (∫ x, g x^2 ∂P) = 1 := by
    have he : (fun x => g x^2) = fun x => t^2*(f x-a)^2 := by funext x; dsimp [g]; ring
    rw [he, integral_const_mul, ← ProbabilityTheory.variance_eq_integral hf.continuous.measurable.aemeasurable]
    change (Real.sqrt v)⁻¹^2*v = 1
    rw [inv_pow, Real.sq_sqrt hv]
    exact inv_mul_cancel₀ hv0
  have hgradient : (∫ x, ‖EuclideanGradient g x‖^2 ∂P) =
      v⁻¹*(∫ x, ‖EuclideanGradient f x‖^2 ∂P) := by
    have he : (fun x => ‖EuclideanGradient g x‖^2) = fun x => v⁻¹*‖EuclideanGradient f x‖^2 := by
      funext x
      have hgc : gradient (fun y => t*(f y-a)) x = t • gradient (fun y => f y-a) x := by
        simp only [gradient, fderiv_const_mul ((hf.sub contDiff_const).differentiable (by norm_num) x), map_smul]
      have hgs : gradient (fun y => f y-a) x = gradient f x := by
        simp only [gradient, fderiv_sub_const]
      change ‖gradient (fun y => t*(f y-a)) x‖^2 = _
      rw [hgc, hgs, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      congr 1
      dsimp [t]; rw [inv_pow, Real.sq_sqrt hv]
    rw [he, integral_const_mul]
  have hn : min σ 1 ≤ v⁻¹*(∫ x, ‖EuclideanGradient f x‖^2 ∂P) := by
    by_cases he : (∫ x, ‖EuclideanGradient g x‖^2 ∂P) ≤ 1
    · exact (min_le_left _ _).trans (by simpa only [hgradient] using hgap g hg _ hcg hmean hsquare he)
    · rw [hgradient] at he
      exact (min_le_right _ _).trans (le_of_lt (lt_of_not_ge he))
  have hh := mul_le_mul_of_nonneg_right hn hv
  rw [mul_assoc, mul_comm (∫ x, ‖EuclideanGradient f x‖^2 ∂P) v,
    ← mul_assoc, inv_mul_cancel₀ hv0, one_mul] at hh
  exact hh

private theorem unweighted (d : ℕ) (hd : 3 ≤ d) (s A κ : ℝ)
    (hs : 0 < s) (hsd : s ≤ (d : ℝ)-2) (hA : 0 ≤ A) (hκ : 0 < κ)
    (Ca Mloc : ℝ → ℝ) :
    ∃ σ : ℝ, 0 < σ ∧
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
        σ*LawVariance P f ≤ (∫ x, ‖EuclideanGradient f x‖^2 ∂P) := by
  obtain ⟨H, G, C, pcap, hH, hG, hC, hpcap, hcontrols⟩ :=
    AtomicLawTestControls d hd s A κ (Mloc 1) hs hsd hA hκ Ca
  obtain ⟨χ, Dχ, hDχ, hχ, hlocal⟩ := AtomicLocalCutoffEnergy d hd s A hs hsd hA
  obtain ⟨clip, K, hK, hclip, hclipping⟩ := AtomicTestClipping d hd s A κ hs hsd hA hκ Ca Mloc
  obtain ⟨Cn, hCn, happ⟩ := CutoffCubeApproximation d
  have hdecay : Tendsto (fun R : ℝ => 2*C*(R^(-2 : ℝ)+R^(-(2/(s+1))))) atTop (nhds 0) := by
    have ha := tendsto_rpow_neg_atTop (show (0 : ℝ) < 2 by norm_num)
    have hb := tendsto_rpow_neg_atTop (show (0 : ℝ) < 2/(s+1) by positivity)
    convert (ha.add hb).const_mul (2*C) using 1 <;> simp
  obtain ⟨R, hR, hsmall⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (hdecay.eventually (eventually_lt_nhds (show (0 : ℝ) < 1/100 by norm_num)))).exists
  obtain ⟨m, hm, hclipM⟩ := hclipping (1/1200) (by norm_num)
  obtain ⟨VR, SR, hVR, hSR, hlocalR⟩ := hlocal R hR
  let Pcoef := H*Cn*(R-(-R))^2
  have hPcoef : 0 ≤ Pcoef := by dsimp [Pcoef]; positivity
  let W := H*(2*m)^2*VR+Pcoef*8*m^2*SR
  have hW : 0 ≤ W := by dsimp [W]; positivity
  let T := 1+1200*W
  have hT : 0 < T := by dsimp [T]; positivity
  have hWT : W/T ≤ 1/1200 := by
    rw [div_le_iff₀ hT]; dsimp [T]; nlinarith
  let radius := (d : ℝ)*R+1
  have hradius : 0 < radius := by dsimp [radius]; positivity
  let Zg := ∫ x : OneParticle d, Real.exp (-(κ/2)*‖x‖^2)
  have hZg : 0 < Zg := (GaussianConfinementIntegral (ι := Fin d) κ hκ).2.2
  let β := Real.exp (-Mloc radius-2*T)/Zg
  have hβ : 0 < β := div_pos (Real.exp_pos _) hZg
  let Ecoef := 2*K^2/β
  have hEcoef : 0 ≤ Ecoef := by dsimp [Ecoef]; positivity
  let σ := 1/(1200*(Pcoef*Ecoef+1))
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hσbound : Pcoef*Ecoef*σ ≤ 1/1200 := by
    dsimp [σ]
    rw [mul_one_div]
    apply (div_le_iff₀ (show 0 < 1200*(Pcoef*Ecoef+1) by positivity)).mpr
    nlinarith
  refine ⟨min σ 1, lt_min hσ (by norm_num), ?_⟩
  intro V hV hmin hM hgrowth ι J charges y ε ha hmass hε
  let U := fun x => ∑ j ∈ J, charges j*RieszKernel s ε (x-y j)
  let P := ReferenceLaw (fun x => V x+U x) (fun _ => 1)
  let r := (ReferencePartition (fun x => V x+U x) (fun _ => 1))⁻¹
  let p := fun x => r*Real.exp (-(V x+U x))
  let ρ := fun x => Real.toNNReal (p x)
  have hdata := hcontrols V hV hmin (hM 1 (by norm_num)) hgrowth J charges y ε ha hmass hε
  dsimp only at hdata
  rcases hdata with ⟨hZ, hr, hoffZ, hoffLaw, hpm, hpp, hprob, hP,
    hρ, hρeq, hPρ, hupper, hlower, hint, hptail, htest⟩
  letI : IsProbabilityMeasure P := hprob
  have hU : ContDiff ℝ 1 U :=
    (AtomicInteractionSource d s ε hs hsd hε J charges y ha).1.of_le (by norm_num)
  let Q := {x : OneParticle d | ∀ k : Fin d, -R ≤ x k ∧ x k ≤ R}
  have hQ : MeasurableSet Q := by
    change MeasurableSet {x : OneParticle d | ∀ k : Fin d, -R ≤ x k ∧ x k ≤ R}
    simp_rw [ofPred_forall]
    apply MeasurableSet.iInter
    intro k
    exact (measurableSet_le measurable_const (PiLp.continuous_apply 2 _ k).measurable).inter
      (measurableSet_le (PiLp.continuous_apply 2 _ k).measurable measurable_const)
  have hQabs : Q = {x : OneParticle d | ∀ k : Fin d, |x k| ≤ R} := by
    ext x; simp only [Q, Set.mem_setOf_eq, abs_le]
  have hOutside : P.real Qᶜ ≤ 1/100 := by
    have hp := hptail R hR
    rw [hQabs]
    change P.real {x | ¬ ∀ k : Fin d, |x k| ≤ R} ≤ _
    have hn : 0 ≤ C*(R^(-2 : ℝ)+R^(-(2/(s+1)))) := by positivity
    linarith
  have hMass : 1/2 ≤ P.real Q := by
    have hm' := measureReal_add_measureReal_compl (μ := P) hQ
    have hu : P.real Set.univ = 1 := by simp
    rw [hu] at hm'; linarith
  have hupper' : ∀ x ∈ Q, (ρ x : ℝ) ≤ H := by
    intro x _
    rw [hρeq]
    have he : Real.exp (-(κ/2)*‖x‖^2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖x‖])
    exact (hupper x).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left he hH.le)
  have hlower' : ∀ x ∈ Q, U x ≤ 2*T → β ≤ (ρ x : ℝ) := by
    intro x hx hu
    rw [hρeq]
    exact hlower radius (Mloc radius) (2*T) (hM radius hradius) x
      (AtomicOneSitePI.cube_norm d R hR x hx) hu
  have hloc := (hlocalR J charges y ε hε ha hmass).2 T hT
  have hχ1 : ContDiff ℝ 1 (χ T) := (hχ T hT).1.of_le (by simp : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  have hclip1 : ContDiff ℝ 1 (clip m) := (hclip m hm).1.of_le (by simp : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  have hgap : ∀ f : OneParticle d → ℝ, ContDiff ℝ 1 f → ∀ c : ℝ,
      HasCompactSupport (fun x => f x-c) → (∫ x, f x ∂P) = 0 →
      (∫ x, f x^2 ∂P) = 1 → (∫ x, ‖EuclideanGradient f x‖^2 ∂P) ≤ 1 →
      σ ≤ (∫ x, ‖EuclideanGradient f x‖^2 ∂P) := by
    intro f hf c hc hmean hunit henergy
    obtain ⟨hfsq, hfenergy, htrans⟩ := htest f hf c hc
    have hfi : Integrable f P := ((memLp_two_iff_integrable_sq hf.continuous.aestronglyMeasurable).mpr
      hfsq).integrable (by norm_num)
    have ht := (htrans hunit henergy).2.2.2.2.2.2.2 R hR
    have htail : (∫ x in Qᶜ, f x^2 ∂P) ≤ 1/100 := by
      rw [hQabs]
      exact ht.trans hsmall.le
    have herr := (hclipM V hV hmin hM hgrowth J charges y ε ha hmass hε f hf c hc hunit henergy).2.2
    have hfinite : IsFiniteMeasure (volume.withDensity (fun x => (ρ x : ℝ≥0∞))) := by rw [hPρ]; infer_instance
    have hsqi : Integrable (fun x => f x^2) (volume.withDensity (fun x => (ρ x : ℝ≥0∞))) := by rwa [hPρ]
    have hei : Integrable (fun x => ‖EuclideanGradient f x‖^2)
        (volume.withDensity (fun x => (ρ x : ℝ≥0∞))) := by rwa [hPρ]
    have happ' := happ (-R) R (by linarith) f U hf hU ρ hρ hfinite hsqi hei (χ T) (clip m)
      hχ1 hclip1 m T H β K VR SR hm hT hH.le hβ hK.le hVR hSR
      (fun u => ⟨(hχ T hT).2 u |>.1, (hχ T hT).2 u |>.2.1, (hχ T hT).2 u |>.2.2.2.1⟩)
      (fun u => ⟨((hclip m hm).2 u).1, ((hclip m hm).2 u).2.1⟩)
      hupper' hlower' hloc.2.2.2 hloc.2.2.1
    dsimp only at happ'
    rw [hPρ] at happ'
    let a := (∫ x in Q, χ T (U x)*clip m (f x))/(R-(-R))^d
    have happrox := happ'.2.2.2
    change (∫ x in Q, (f x-a)^2 ∂P) ≤
      3*((∫ x, (f x-clip m (f x))^2 ∂P)+H*(2*m)^2*(VR/T)+
        Pcoef*(Ecoef*(∫ x in Q, ‖EuclideanGradient f x‖^2 ∂P)+8*m^2*(SR/T))) at happrox
    by_contra hn
    have hEs : (∫ x, ‖EuclideanGradient f x‖^2 ∂P) ≤ σ := (lt_of_not_ge hn).le
    have hinner := setIntegral_le_integral hfenergy
      (Eventually.of_forall (fun x => sq_nonneg ‖EuclideanGradient f x‖)) (s := Q)
    have hEnergySmall : Pcoef*Ecoef*(∫ x in Q, ‖EuclideanGradient f x‖^2 ∂P) ≤ 1/1200 :=
      (mul_le_mul_of_nonneg_left (hinner.trans hEs) (mul_nonneg hPcoef hEcoef)).trans hσbound
    have hRest : H*(2*m)^2*(VR/T)+Pcoef*8*m^2*(SR/T) ≤ 1/1200 := by
      calc
        _ = W/T := by dsimp [W]; ring
        _ ≤ _ := hWT
    have hLocal : (∫ x in Q, (f x-a)^2 ∂P) ≤ 1/100 := by nlinarith [herr]
    exact AtomicOneSitePI.local_obstruction P f hfi hfsq hmean hunit Q hQ hMass a hLocal htail hOutside
  exact AtomicOneSitePI.rescale P σ hσ (fun f hf c hc => (htest f hf c hc).1) hgap

private theorem tilt_transfer {α : Type*} [MeasurableSpace α] [Nonempty α]
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

end AtomicOneSitePI

-- [TABLET NODE: AtomicOneSitePI]
theorem AtomicOneSitePI (d : ℕ) (hd : 3 ≤ d) (s A κ L : ℝ)
    (hs : 0 < s) (hsd : s ≤ (d : ℝ)-2) (hA : 0 ≤ A) (hκ : 0 < κ) (hL : 1 ≤ L)
    (Ca Mloc : ℝ → ℝ) :
    ∃ σ : ℝ, 0 < σ ∧
    ∀ V : OneParticle d → ℝ, PotentialBounds d κ V →
      (∀ x, V 0 ≤ V x) →
      (∀ R : ℝ, 0 < R → ∀ x, ‖x‖ ≤ R → V x-V 0 ≤ Mloc R) →
      (∀ a : ℝ, 0 < a → ∀ x, EuclideanLaplacian V x ≤
        a*‖EuclideanGradient V x‖^(2/(s+1))+Ca a) →
    ∀ {ι : Type*} (J : Finset ι) (charges : ι → ℝ) (y : ι → OneParticle d) (ε : ℝ),
      (∀ j ∈ J, 0 ≤ charges j) → (∑ j ∈ J, charges j ≤ A) → 0 < ε →
      let U := fun x => ∑ j ∈ J, charges j*RieszKernel s ε (x-y j)
      ∀ b : OneParticle d → ℝ, BoundedMultiplier d L b →
      let P := ReferenceLaw (fun x => V x+U x) b
      ∀ f : OneParticle d → ℝ, ContDiff ℝ 1 f → ∀ c : ℝ,
        HasCompactSupport (fun x => f x-c) →
        σ*LawVariance P f ≤ (∫ x, ‖EuclideanGradient f x‖^2 ∂P) := by
-- BODY
  obtain ⟨σ, hσ, hbase⟩ := AtomicOneSitePI.unweighted d hd s A κ hs hsd hA hκ Ca Mloc
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hL
  refine ⟨σ/L, div_pos hσ hLpos, ?_⟩
  intro V hV hmin hM hgrowth ι J charges y ε ha hmass hε
  dsimp only
  intro b hb f hf c hc
  let W := fun x => V x+∑ j ∈ J, charges j*RieszKernel s ε (x-y j)
  let P := ReferenceLaw W (fun _ => 1)
  obtain ⟨H, G, C, pcap, hH, hG, hC, hpcap, hcontrols⟩ :=
    AtomicLawTestControls d hd s A κ (Mloc 1) hs hsd hA hκ Ca
  have hdata := hcontrols V hV hmin (hM 1 (by norm_num)) hgrowth J charges y ε ha hmass hε
  dsimp only at hdata
  rcases hdata with ⟨hZ, hr, hoffZ, hoffLaw, hpm, hpp, hprob, hP,
    hρ, hρeq, hPρ, hupper, hlower, hint, hptail, htest⟩
  letI : IsProbabilityMeasure P := hprob
  obtain ⟨l, u, hl, hlu, hcontrast, hbound⟩ := hb.bounds
  have hu : 0 < u := hl.trans_le hlu
  have hi : Integrable b P := (integrable_const u).mono' hb.measurable.aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hl.le.trans (hbound x).1)]
      exact (hbound x).2)
  have hlo : l ≤ ∫ x, b x ∂P := by
    simpa using integral_mono (integrable_const l) hi (fun x => (hbound x).1)
  have hEb : 0 < ∫ x, b x ∂P := hl.trans_le hlo
  let Z := ReferencePartition W (fun _ => 1)
  let Zb := ReferencePartition W b
  have hratio : (∫ x, b x ∂P) = Zb/Z := by
    have hh := hint b Set.univ MeasurableSet.univ
    simpa only [Measure.restrict_univ, W, P, Z, Zb, ReferencePartition, one_mul,
      div_eq_mul_inv, mul_comm] using hh
  have hZb : 0 < Zb := (div_pos_iff_of_pos_right hZ).mp (hratio ▸ hEb)
  have hW : Measurable W := hV.regularity.continuous.measurable.add
    (AtomicInteractionSource d s ε hs hsd hε J charges y ha).1.continuous.measurable
  have hidentity : ReferenceLaw W b = P.withDensity
      (fun x => ENNReal.ofReal (b x/(∫ y, b y ∂P))) := by
    rw [hratio]
    dsimp only [P]
    unfold ReferenceLaw
    simp only [one_mul]
    have hm : Measurable (fun x => ENNReal.ofReal (Z⁻¹*Real.exp (-W x))) := by fun_prop
    rw [← withDensity_mul _ hm ((hb.measurable.div_const _).ennreal_ofReal)]
    congr 1
    funext x
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.mpr hZ.le) (Real.exp_pos _).le)]
    congr 1
    dsimp [Z, Zb] at *
    field_simp <;> rfl
  have hfsq := (htest f hf c hc).1
  have hei := (htest f hf c hc).2.1
  have hfLp : MemLp f 2 P := (memLp_two_iff_integrable_sq hf.continuous.aestronglyMeasurable).mpr hfsq
  have hPI := hbase V hV hmin hM hgrowth J charges y ε ha hmass hε f hf c hc
  have htilt := AtomicOneSitePI.tilt_transfer P b hb.measurable l u σ hl hσ hbound
    f (fun x => ‖EuclideanGradient f x‖^2) hfLp hei (fun _ => sq_nonneg _) hPI
  dsimp only at htilt
  rw [← hidentity] at htilt
  have hcoef : σ/L ≤ σ*l/u := by
    have huL : u ≤ L*l := (div_le_iff₀ hl).mp hcontrast
    apply (div_le_div_iff₀ hLpos hu).mpr
    calc
      σ*u ≤ σ*(L*l) := mul_le_mul_of_nonneg_left huL hσ.le
      _ = σ*l*L := by ring
  exact (mul_le_mul_of_nonneg_right hcoef (ProbabilityTheory.variance_nonneg f _)).trans htilt
