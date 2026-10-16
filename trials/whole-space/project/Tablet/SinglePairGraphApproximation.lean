import Tablet.RelativeCollisionCutoffs
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace SinglePairGraphApproximation
private abbrev Config (N d : ℕ) := ParticleConfig d N
private noncomputable abbrev particle {N d : ℕ} (x : Config N d) (i : Fin N) := ParticlePosition x i
private noncomputable def pairCollisionCutoff {N d : ℕ} (i j : Fin N) (hij : i ≠ j) :
    ℕ → Config N d → ℝ := Classical.choose (RelativeCollisionCutoffs (d := d) i j hij)
private lemma pairCollisionCutoff_smooth {N d : ℕ} (i j : Fin N) (hij : i ≠ j) (n : ℕ) :
    ContDiff ℝ ∞ (pairCollisionCutoff (d := d) i j hij n) := by
  obtain ⟨η, C, hC, hs, hu, hv, ho, hl, hb, hg, he⟩ :=
    Classical.choose_spec (RelativeCollisionCutoffs (d := d) i j hij)
  exact hs n
private lemma pairCutoff_unitBounds {N d : ℕ} (i j : Fin N) (hij : i ≠ j) (n : ℕ) (x : Config N d) :
    0 ≤ pairCollisionCutoff i j hij n x ∧ pairCollisionCutoff i j hij n x ≤ 1 := by
  obtain ⟨η, C, hC, hs, hu, hv, ho, hl, hb, hg, he⟩ :=
    Classical.choose_spec (RelativeCollisionCutoffs (d := d) i j hij)
  exact hu n x
private lemma pairCutoff_pointwiseLimit {N d : ℕ} (i j : Fin N) (hij : i ≠ j)
    (x : Config N d) (hx : particle x i - particle x j ≠ 0) :
    Tendsto (fun n => pairCollisionCutoff i j hij n x) atTop (𝓝 (1 : ℝ)) := by
  obtain ⟨η, C, hC, hs, hu, hv, ho, hl, hb, hg, he⟩ :=
    Classical.choose_spec (RelativeCollisionCutoffs (d := d) i j hij)
  exact hl x (sub_ne_zero.mp hx)
private lemma pairCollisionCutoff_gradient_pointwiseLimit {N d : ℕ} (i j : Fin N) (hij : i ≠ j)
    (x : Config N d) :
    Tendsto (fun n => EuclideanGradient (pairCollisionCutoff i j hij n) x) atTop (𝓝 0) := by
  obtain ⟨η, C, hC, hs, hu, hv, ho, hl, hb, hg, he⟩ :=
    Classical.choose_spec (RelativeCollisionCutoffs (d := d) i j hij)
  exact hg x
private lemma pairCollisionCutoff_errorBound {N d : ℕ} (i j : Fin N) (hij : i ≠ j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Config N d → ℝ) (n : ℕ) (x : Config N d),
      ‖f x • EuclideanGradient (pairCollisionCutoff i j hij n) x‖^2 ≤
        C * ((f x)^2 / ‖particle x i - particle x j‖^2) := by
  obtain ⟨η, C, hC, hs, hu, hv, ho, hl, hb, hg, he⟩ :=
    Classical.choose_spec (RelativeCollisionCutoffs (d := d) i j hij)
  refine ⟨C^2, sq_nonneg _, ?_⟩
  intro f n x
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hh := pow_le_pow_left₀ (norm_nonneg _) (hb n x) 2
  calc
    _ ≤ (f x)^2 * (C / ‖particle x i - particle x j‖)^2 :=
      mul_le_mul_of_nonneg_left hh (sq_nonneg _)
    _ = _ := by rw [div_pow]; ring
private lemma EuclideanGradient_continuous {ι : Type*} [Fintype ι]
    (f : EuclideanSpace ℝ ι → ℝ) (hs : ContDiff ℝ ∞ f) :
    Continuous (EuclideanGradient f) := by
  have he := funext (fun x => (EuclideanDerivativeCoordinates f x).1)
  rw [he]
  have hd := hs.continuous_fderiv (by simp)
  fun_prop
private lemma lpIntegral_normSquare {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (P : Measure Ω) (f : Lp E 2 P) :
    (∫ x, ‖f x‖^2 ∂P) = ‖f‖^2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]
private lemma pairCutoff_scalarError {N d : ℕ} (P : Measure (Config N d))
    (i j : Fin N) (hij : i ≠ j)
    (hpair : ∀ᵐ x ∂P, particle x i-particle x j ≠ 0)
    (f : Config N d → ℝ) (hfs : ContDiff ℝ ∞ f) (hf : MemLp f 2 P) :
    Tendsto (fun n : ℕ => ∫ x, (f x * pairCollisionCutoff i j hij n x - f x)^2 ∂P)
      atTop (𝓝 (0:ℝ)) := by
  have hI : Integrable (fun x => (f x)^2) P := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).1 hf
  have hm : ∀ᶠ n : ℕ in atTop, AEStronglyMeasurable
      (fun x => (f x * pairCollisionCutoff i j hij n x - f x)^2) P :=
    Eventually.of_forall (fun n => ((hfs.continuous.mul (pairCollisionCutoff_smooth i j hij n).continuous).sub hfs.continuous).pow 2 |>.aestronglyMeasurable)
  have hb : ∀ᶠ n : ℕ in atTop, ∀ᵐ x ∂P, ‖(f x * pairCollisionCutoff i j hij n x - f x)^2‖ ≤ (f x)^2 :=
    Eventually.of_forall (fun n => Eventually.of_forall (fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have hu := pairCutoff_unitBounds i j hij n x
      have hs : (pairCollisionCutoff i j hij n x-1)^2 ≤ 1 := by nlinarith
      calc
        _ = (f x)^2 * (pairCollisionCutoff i j hij n x-1)^2 := by ring
        _ ≤ (f x)^2 * 1 := mul_le_mul_of_nonneg_left hs (sq_nonneg _)
        _ = _ := mul_one _))
  have hl : ∀ᵐ x ∂P, Tendsto (fun n : ℕ => (f x * pairCollisionCutoff i j hij n x - f x)^2)
      atTop (𝓝 (0:ℝ)) := by
    filter_upwards [hpair] with x hx
    have hχ := pairCutoff_pointwiseLimit i j hij x hx
    simpa only [mul_one,sub_self,zero_pow (by norm_num : (2:ℕ)≠0)] using ((hχ.const_mul (f x)).sub_const (f x)).pow 2
  simpa only [integral_zero] using tendsto_integral_filter_of_dominated_convergence _ hm hb hI hl

private lemma pairCutoff_mul_memLp {N d : ℕ} (P : Measure (Config N d))
    (i j : Fin N) (hij : i ≠ j) (n : ℕ)
    (f : Config N d → ℝ) (hfs : ContDiff ℝ ∞ f) (hf : MemLp f 2 P) :
    MemLp (fun x => f x * pairCollisionCutoff i j hij n x) 2 P := by
  apply hf.of_le ((hfs.continuous.mul (pairCollisionCutoff_smooth i j hij n).continuous).aestronglyMeasurable)
  filter_upwards [] with x
  change ‖f x * pairCollisionCutoff i j hij n x‖ ≤ ‖f x‖
  rw [norm_mul,Real.norm_eq_abs (pairCollisionCutoff i j hij n x),
    abs_of_nonneg (pairCutoff_unitBounds i j hij n x).1]
  exact (mul_le_mul_of_nonneg_left (pairCutoff_unitBounds i j hij n x).2 (norm_nonneg _)).trans_eq (mul_one _)

private lemma ordinaryGradient_mul {ι : Type*} [Fintype ι] (f g : EuclideanSpace ℝ ι → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : EuclideanSpace ℝ ι) :
    EuclideanGradient (fun y => f y*g y) x =
      g x • EuclideanGradient f x + f x • EuclideanGradient g x := by
  have hdf : DifferentiableAt ℝ f x := (hf.differentiable (by simp)).differentiableAt
  have hdg : DifferentiableAt ℝ g x := (hg.differentiable (by simp)).differentiableAt
  rw [(EuclideanDerivativeCoordinates _ x).1, (EuclideanDerivativeCoordinates f x).1,
    (EuclideanDerivativeCoordinates g x).1]
  ext k
  change (fderiv ℝ (f*g) x) (EuclideanSpace.basisFun ι ℝ k) =
    g x * (fderiv ℝ f x) (EuclideanSpace.basisFun ι ℝ k) + f x * (fderiv ℝ g x) (EuclideanSpace.basisFun ι ℝ k)
  rw [fderiv_mul hdf hdg]
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

private lemma pairCutoff_gradientDifference {N d : ℕ} (i j : Fin N) (hij : i ≠ j) (n : ℕ)
    (f : Config N d → ℝ) (hfs : ContDiff ℝ ∞ f) (x : Config N d) :
    EuclideanGradient (fun y => f y*pairCollisionCutoff i j hij n y) x - EuclideanGradient f x =
      (pairCollisionCutoff i j hij n x-1) • EuclideanGradient f x +
        f x • EuclideanGradient (pairCollisionCutoff i j hij n) x := by
  rw [ordinaryGradient_mul f _ hfs (pairCollisionCutoff_smooth i j hij n) x]
  module

private lemma pairCutoff_gradientErrorBound {N d : ℕ} (i j : Fin N) (hij : i ≠ j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Config N d → ℝ), ContDiff ℝ ∞ f → ∀ (n : ℕ) (x : Config N d),
      ‖EuclideanGradient (fun y => f y*pairCollisionCutoff i j hij n y) x - EuclideanGradient f x‖^2 ≤
        2*‖EuclideanGradient f x‖^2 + 2*C*((f x)^2/‖particle x i-particle x j‖^2) := by
  obtain ⟨C,hC,herr⟩ := pairCollisionCutoff_errorBound (d := d) i j hij
  refine ⟨C,hC,?_⟩
  intro f hf n x
  rw [pairCutoff_gradientDifference i j hij n f hf x]
  let a := (pairCollisionCutoff i j hij n x-1) • EuclideanGradient f x
  let b := f x • EuclideanGradient (pairCollisionCutoff i j hij n) x
  have ha : ‖a‖^2 ≤ ‖EuclideanGradient f x‖^2 := by
    have hu := pairCutoff_unitBounds i j hij n x
    have hc : |pairCollisionCutoff i j hij n x-1| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    have hh : ‖a‖ ≤ ‖EuclideanGradient f x‖ := by
      change ‖(pairCollisionCutoff i j hij n x-1) • EuclideanGradient f x‖ ≤ _
      rw [norm_smul,Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans_eq (one_mul _)
    exact pow_le_pow_left₀ (norm_nonneg _) hh 2
  have hb : ‖b‖^2 ≤ C*((f x)^2/‖particle x i-particle x j‖^2) := herr f n x
  have hab : ‖a+b‖^2 ≤ 2*‖a‖^2 + 2*‖b‖^2 := by
    have hh := pow_le_pow_left₀ (norm_nonneg (a+b)) (norm_add_le a b) 2
    nlinarith [sq_nonneg (‖a‖-‖b‖)]
  exact hab.trans (by nlinarith [ha,hb])

private lemma pairCutoff_gradientError_pointwiseLimit {N d : ℕ} (i j : Fin N) (hij : i ≠ j)
    (f : Config N d → ℝ) (hfs : ContDiff ℝ ∞ f) (x : Config N d)
    (hx : particle x i-particle x j ≠ 0) :
    Tendsto (fun n : ℕ => EuclideanGradient (fun y => f y*pairCollisionCutoff i j hij n y) x -
      EuclideanGradient f x) atTop (𝓝 0) := by
  have hχ := pairCutoff_pointwiseLimit i j hij x hx
  have hh := (((hχ.sub_const 1).smul_const (EuclideanGradient f x)).add
    ((pairCollisionCutoff_gradient_pointwiseLimit i j hij x).const_smul (f x)))
  simpa only [← pairCutoff_gradientDifference i j hij _ f hfs x,sub_self,zero_smul,smul_zero,add_zero] using hh

private lemma pairCutoff_gradientGraphApproximation {N d : ℕ} (P : Measure (Config N d))
    (i j : Fin N) (hij : i ≠ j)
    (hpair : ∀ᵐ x ∂P, particle x i-particle x j ≠ 0)
    (f : Config N d → ℝ) (hfs : ContDiff ℝ ∞ f)
    (hD : MemLp (EuclideanGradient f) 2 P)
    (hinv : Integrable (fun x => (f x)^2/‖particle x i-particle x j‖^2) P) :
    (∀ n : ℕ, MemLp (EuclideanGradient (fun y => f y*pairCollisionCutoff i j hij n y)) 2 P) ∧
      Tendsto (fun n : ℕ => ∫ x,
        ‖EuclideanGradient (fun y => f y*pairCollisionCutoff i j hij n y) x - EuclideanGradient f x‖^2 ∂P)
        atTop (𝓝 (0:ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := pairCutoff_gradientErrorBound (d := d) i j hij
  have hDI : Integrable (fun x => ‖EuclideanGradient f x‖^2) P :=
    (memLp_two_iff_integrable_sq_norm hD.aestronglyMeasurable).1 hD
  let dom := fun x : Config N d => 2*‖EuclideanGradient f x‖^2 + 2*C*((f x)^2/‖particle x i-particle x j‖^2)
  have hI : Integrable dom P := (hDI.const_mul 2).add (hinv.const_mul (2*C))
  have hDm (n : ℕ) : Continuous (fun x => EuclideanGradient
      (fun y => f y*pairCollisionCutoff i j hij n y) x - EuclideanGradient f x) :=
    (EuclideanGradient_continuous _ (hfs.mul (pairCollisionCutoff_smooth i j hij n))).sub
      (EuclideanGradient_continuous f hfs)
  have hm : ∀ᶠ n : ℕ in atTop, AEStronglyMeasurable
      (fun x => ‖EuclideanGradient (fun y => f y*pairCollisionCutoff i j hij n y) x - EuclideanGradient f x‖^2) P :=
    Eventually.of_forall (fun n => ((hDm n).norm.pow 2).aestronglyMeasurable)
  have hb : ∀ᶠ n : ℕ in atTop, ∀ᵐ x ∂P,
      ‖‖EuclideanGradient (fun y => f y*pairCollisionCutoff i j hij n y) x - EuclideanGradient f x‖^2‖ ≤ dom x :=
    Eventually.of_forall (fun n => Eventually.of_forall (fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hbound f hfs n x))
  have hl : ∀ᵐ x ∂P, Tendsto (fun n : ℕ =>
      ‖EuclideanGradient (fun y => f y*pairCollisionCutoff i j hij n y) x - EuclideanGradient f x‖^2)
        atTop (𝓝 (0:ℝ)) := by
    filter_upwards [hpair] with x hx
    simpa only [norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)] using
      (pairCutoff_gradientError_pointwiseLimit i j hij f hfs x hx).norm.pow 2
  constructor
  · intro n
    have hInt : Integrable (fun x => ‖EuclideanGradient
        (fun y => f y*pairCollisionCutoff i j hij n y) x - EuclideanGradient f x‖^2) P := by
      apply hI.mono' ((hDm n).norm.pow 2).aestronglyMeasurable
      filter_upwards [] with x
      change ‖‖EuclideanGradient (fun y => f y*pairCollisionCutoff i j hij n y) x - EuclideanGradient f x‖^2‖ ≤ dom x
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hbound f hfs n x
    have hMem := (memLp_two_iff_integrable_sq_norm (hDm n).aestronglyMeasurable).2 hInt
    apply MemLp.ae_eq _ (hD.add hMem)
    filter_upwards [] with x
    change EuclideanGradient f x +
      (EuclideanGradient (fun y => f y*pairCollisionCutoff i j hij n y) x-EuclideanGradient f x) = _
    abel
  · simpa only [integral_zero] using tendsto_integral_filter_of_dominated_convergence dom hm hb hI hl

private lemma lpComponent_tendsto_of_energy {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (P : Measure Ω)
    (f : Ω → E) (fn : ℕ → Ω → E) (hf : MemLp f 2 P) (hfn : ∀ n, MemLp (fn n) 2 P)
    (ht : Tendsto (fun n : ℕ => ∫ x, ‖fn n x-f x‖^2 ∂P) atTop (𝓝 (0:ℝ))) :
    Tendsto (fun n : ℕ => (hfn n).toLp (fn n)) atTop (𝓝 (hf.toLp f)) := by
  have he (n : ℕ) : (∫ x, ‖fn n x-f x‖^2 ∂P) = ‖(hfn n).toLp (fn n)-hf.toLp f‖^2 := by
    rw [← lpIntegral_normSquare P ((hfn n).toLp (fn n)-hf.toLp f)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((hfn n).toLp (fn n)) (hf.toLp f), (hfn n).coeFn_toLp,hf.coeFn_toLp] with x hsub hn hx
    rw [hsub]
    change ‖fn n x-f x‖^2 = ‖(hfn n).toLp (fn n) x-hf.toLp f x‖^2
    rw [hn,hx]
  have hsq : Tendsto (fun n : ℕ => ‖(hfn n).toLp (fn n)-hf.toLp f‖^2) atTop (𝓝 (0:ℝ)) := by
    simpa only [he] using ht
  have hnorm : Tendsto (fun n : ℕ => ‖(hfn n).toLp (fn n)-hf.toLp f‖) atTop (𝓝 (0:ℝ)) := by
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm


end SinglePairGraphApproximation

-- [TABLET NODE: SinglePairGraphApproximation]
theorem SinglePairGraphApproximation {d N : ℕ} (P : Measure (ParticleConfig d N))
    (i j : Fin N) (hij : i ≠ j)
    (hpair : ∀ᵐ X ∂P, ParticlePosition X i ≠ ParticlePosition X j)
    (f : ParticleConfig d N → ℝ) (hs : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hf : MemLp f 2 P) (hg : MemLp (EuclideanGradient f) 2 P)
    (hinv : Integrable (fun X => (f X)^2 /
      ‖ParticlePosition X i - ParticlePosition X j‖^2) P) :
    ∃ fn : ℕ → ParticleConfig d N → ℝ,
      (∀ n, ContDiff ℝ ∞ (fn n) ∧ HasCompactSupport (fn n) ∧
        tsupport (fn n) ⊆ tsupport f ∧
        ∀ X ∈ tsupport (fn n), ParticlePosition X i ≠ ParticlePosition X j) ∧
      ∃ hfn : ∀ n, MemLp (fn n) 2 P,
      ∃ hgn : ∀ n, MemLp (EuclideanGradient (fn n)) 2 P,
        Tendsto (fun n => ((hfn n).toLp (fn n),
          (hgn n).toLp (EuclideanGradient (fn n)))) atTop
          (𝓝 (hf.toLp f, hg.toLp (EuclideanGradient f))) := by
-- BODY
  let χ := SinglePairGraphApproximation.pairCollisionCutoff (d := d) i j hij
  let fn := fun n X => f X * χ n X
  have hpair' : ∀ᵐ X ∂P, ParticlePosition X i - ParticlePosition X j ≠ 0 :=
    hpair.mono (fun _ hx => sub_ne_zero.mpr hx)
  have hfn := fun n => SinglePairGraphApproximation.pairCutoff_mul_memLp P i j hij n f hs hf
  obtain ⟨hgn, htG⟩ := SinglePairGraphApproximation.pairCutoff_gradientGraphApproximation
    P i j hij hpair' f hs hg hinv
  refine ⟨fn, ?_, hfn, hgn, ?_⟩
  · intro n
    refine ⟨hs.mul (SinglePairGraphApproximation.pairCollisionCutoff_smooth i j hij n),
      hc.mul_right, tsupport_mul_subset_left, ?_⟩
    intro X hX heq
    obtain ⟨η, C, hC, hχs, hu, hv, ho, hl, hb, hgg, he⟩ :=
      Classical.choose_spec (RelativeCollisionCutoffs (d := d) i j hij)
    have hclosed : IsClosed {Y : ParticleConfig d N |
        1 / ((n : ℝ) + 1) ≤ ‖ParticlePosition Y i - ParticlePosition Y j‖} := by
      apply isClosed_le continuous_const
      have hp : Continuous (fun Y : ParticleConfig d N => ParticlePosition Y i - ParticlePosition Y j) := by
        unfold ParticlePosition
        fun_prop
      exact hp.norm
    have hsub : tsupport (fn n) ⊆ {Y : ParticleConfig d N |
        1 / ((n : ℝ) + 1) ≤ ‖ParticlePosition Y i - ParticlePosition Y j‖} := by
      apply closure_minimal _ hclosed
      intro Y hY
      by_contra hnot
      have hz := hv n Y (le_of_not_ge hnot)
      change χ n Y = 0 at hz
      exact hY (by change f Y * χ n Y = 0; change f Y * _ = 0; rw [hz]; simp)
    have hgap := hsub hX
    simp only [Set.mem_setOf_eq, heq, sub_self, norm_zero] at hgap
    have hn : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  · have ht := SinglePairGraphApproximation.pairCutoff_scalarError P i j hij hpair' f hs hf
    have ht' : Tendsto (fun n : ℕ => ∫ X, ‖fn n X - f X‖^2 ∂P) atTop (𝓝 (0 : ℝ)) := by
      simpa only [Real.norm_eq_abs, sq_abs] using ht
    exact (SinglePairGraphApproximation.lpComponent_tendsto_of_energy P f fn hf hfn ht').prodMk_nhds
      (SinglePairGraphApproximation.lpComponent_tendsto_of_energy P (EuclideanGradient f)
        (fun n => EuclideanGradient (fn n)) hg hgn htG)
