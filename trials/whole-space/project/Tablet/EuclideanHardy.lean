module

public import Tablet.EuclideanGradient
public import Tablet.OneParticle
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntegrableOn

@[expose] public section
set_option maxHeartbeats 1600000
open MeasureTheory
namespace EuclideanHardy
private abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)
private noncomputable def R {d : ℕ} (ε : ℝ) (x : E d) : ℝ := ‖x‖^2+ε^2
private noncomputable def A {d : ℕ} (ε : ℝ) (k : Fin d) (x : E d) : ℝ := x k / R ε x
private noncomputable def D {d : ℕ} (f : E d → ℝ) (k : Fin d) (x : E d) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.basisFun (Fin d) ℝ k)

private theorem R_pos {d : ℕ} {ε : ℝ} (hε : 0 < ε) (x : E d) : 0 < R ε x := by
  unfold R
  positivity

private theorem A_contDiff {d : ℕ} {ε : ℝ} (hε : 0 < ε) (k : Fin d) : ContDiff ℝ 1 (A ε k) := by
  have hc : ContDiff ℝ 1 (fun x : E d => x k) := by
    have heq : (fun x : E d => x k) = innerSL ℝ (EuclideanSpace.basisFun (Fin d) ℝ k) := by
      funext x
      rw [innerSL_apply_apply, EuclideanSpace.basisFun_inner]
    rw [heq]
    exact (innerSL ℝ (EuclideanSpace.basisFun (Fin d) ℝ k)).contDiff
  exact hc.div ((contDiff_norm_sq ℝ).add contDiff_const) (fun x => (R_pos hε x).ne')

private theorem A_directional {d : ℕ} {ε : ℝ} (hε : 0 < ε) (k : Fin d) (x : E d) :
    D (A ε k) k x = (R ε x - 2*(x k)^2) / (R ε x)^2 := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ k
  have hn : 0 < R ε x := R_pos hε x
  have hcoord : HasFDerivAt (fun y : E d => y k) (innerSL ℝ b) x := by
    have heq : (fun y : E d => y k) = innerSL ℝ b := by
      funext y
      change y k = inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ k) y
      rw [EuclideanSpace.basisFun_inner]
    rw [heq]
    exact (innerSL ℝ b).hasFDerivAt
  have hi := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const (ε^2)).rpow_const
    (p := -1) (Or.inl hn.ne')
  have hd := hcoord.mul hi
  change HasFDerivAt (fun y : E d => y k * (‖y‖^2+ε^2)^(-1 : ℝ)) _ x at hd
  have heq : (fun y : E d => y k * (‖y‖^2+ε^2)^(-1 : ℝ)) = A ε k := by
    funext y
    simp only [A, R, Real.rpow_neg_one, div_eq_mul_inv]
  rw [heq] at hd
  unfold D
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, nsmul_eq_mul,
    innerSL_apply_apply, R, EuclideanSpace.basisFun_inner, EuclideanSpace.inner_basisFun_real]
  have hb : b k = 1 := by simp [b]
  rw [hb]
  change x k * ((-1*(R ε x)^(-1-1 : ℝ))*(2*x k)) + (R ε x)^(-1 : ℝ) * 1 = _
  rw [Real.rpow_neg_one]
  have hp : (R ε x)^(-1-1 : ℝ) = ((R ε x)^2)⁻¹ := by
    rw [show (-1-1 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hn.le, Real.rpow_two]
  rw [hp]
  unfold R
  field_simp
  ring

private theorem A_divergence {d : ℕ} {ε : ℝ} (hε : 0 < ε) (x : E d) :
    (∑ k, D (A ε k) k x) = ((d : ℝ)*R ε x - 2*‖x‖^2)/(R ε x)^2 := by
  simp_rw [A_directional hε]
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq]

private theorem A_square_sum {d : ℕ} (ε : ℝ) (x : E d) :
    (∑ k, (A ε k x)^2) = ‖x‖^2/(R ε x)^2 := by
  simp only [A, div_pow, ← Finset.sum_div, ← EuclideanSpace.real_norm_sq_eq]


private theorem continuous_D {d : ℕ} {f : E d → ℝ} (hf : ContDiff ℝ 1 f) (k : Fin d) :
    Continuous (D f k) := by
  exact (hf.continuous_fderiv_apply (by norm_num)).comp
    (continuous_id.prodMk continuous_const)

private theorem compact_D {d : ℕ} {f : E d → ℝ} (hf : HasCompactSupport f) (k : Fin d) :
    HasCompactSupport (D f k) := hf.fderiv_apply ℝ _

private theorem integrable_mul_compact {d : ℕ} (a b : E d → ℝ) (ha : Continuous a)
    (hb : Continuous b) (hcb : HasCompactSupport b) :
    Integrable (fun x => a x*b x) volume :=
  (ha.mul hb).integrable_of_hasCompactSupport hcb.mul_left

private theorem compact_vectorfield_ibp {d : ℕ} (a ψ : E d → ℝ)
    (ha : ContDiff ℝ 1 a) (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) (k : Fin d) :
    (∫ x, a x*ψ x*D ψ k x) = -(1/2 : ℝ)*(∫ x, D a k x*(ψ x)^2) := by
  have hcψ2 : HasCompactSupport (fun x => (ψ x)^2) := by
    simpa [Function.comp_def] using hcψ.comp_left (g:=fun z : ℝ => z^2) (by simp)
  have hdiffψ : ∀ x, DifferentiableAt ℝ ψ x := hψ.differentiable (by norm_num)
  have hdψ2 (x : E d) : D (fun y => (ψ y)^2) k x = 2*ψ x*D ψ k x := by
    simp [D, fderiv_fun_pow 2 (hdiffψ x), smul_eq_mul]
  have hA : Integrable (fun x => D a k x*(ψ x)^2) volume :=
    integrable_mul_compact _ _ (continuous_D ha k) (hψ.continuous.pow 2) hcψ2
  have hB : Integrable (fun x => a x*D (fun y => (ψ y)^2) k x) volume :=
    integrable_mul_compact _ _ ha.continuous (continuous_D (hψ.pow 2) k) (compact_D hcψ2 k)
  have hC : Integrable (fun x => a x*(ψ x)^2) volume :=
    integrable_mul_compact _ _ ha.continuous (hψ.continuous.pow 2) hcψ2
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ:=volume) (f:=a) (g:=fun y => (ψ y)^2) (v:=EuclideanSpace.basisFun (Fin d) ℝ k)
    hA hB hC (fun x _ => ha.differentiable (by norm_num) x)
    (fun x _ => (hψ.pow 2).differentiable (by norm_num) x)
  change (∫ x, a x*D (fun y => (ψ y)^2) k x) = -(∫ x, D a k x*(ψ x)^2) at h
  simp_rw [hdψ2] at h
  have heq : (∫ x, a x*(2*ψ x*D ψ k x)) = 2*(∫ x, a x*ψ x*D ψ k x) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by ring)
  rw [heq] at h
  linarith

private theorem compact_directional_hardy_bound {d : ℕ} (a ψ : E d → ℝ) (α : ℝ)
    (ha : ContDiff ℝ 1 a) (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) (k : Fin d) :
    α*(∫ x, D a k x*(ψ x)^2) - α^2*(∫ x, (a x)^2*(ψ x)^2) ≤
      ∫ x, (D ψ k x)^2 := by
  have hcψ2 : HasCompactSupport (fun x => (ψ x)^2) := by
    simpa [Function.comp_def] using hcψ.comp_left (g:=fun z : ℝ => z^2) (by simp)
  have hE : Integrable (fun x => (D ψ k x)^2) volume := by
    simpa only [pow_two] using integrable_mul_compact (D ψ k) (D ψ k)
      (continuous_D hψ k) (continuous_D hψ k) (compact_D hcψ k)
  have hP : Integrable (fun x => (a x)^2*(ψ x)^2) volume :=
    integrable_mul_compact _ _ (ha.continuous.pow 2) (hψ.continuous.pow 2) hcψ2
  have hC : Integrable (fun x => a x*ψ x*D ψ k x) volume :=
    integrable_mul_compact _ _ (ha.continuous.mul hψ.continuous)
      (continuous_D hψ k) (compact_D hcψ k)
  have hs : (∫ x, (D ψ k x+α*a x*ψ x)^2) =
      (∫ x, (D ψ k x)^2) + 2*α*(∫ x, a x*ψ x*D ψ k x) +
      α^2*(∫ x, (a x)^2*(ψ x)^2) := by
    calc
      _ = ∫ x, (D ψ k x)^2 + (2*α)*(a x*ψ x*D ψ k x) + α^2*((a x)^2*(ψ x)^2) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by ring)
      _ = _ := by
        rw [integral_add (f:=fun x => (D ψ k x)^2 + (2*α)*(a x*ψ x*D ψ k x))
          (g:=fun x => α^2*((a x)^2*(ψ x)^2))
          (hE.add (hC.const_mul (2*α))) (hP.const_mul (α^2)),
          integral_add hE (hC.const_mul (2*α)), integral_const_mul, integral_const_mul]
  have hn : 0 ≤ ∫ x, (D ψ k x+α*a x*ψ x)^2 := integral_nonneg (fun x => sq_nonneg _)
  rw [hs, compact_vectorfield_ibp a ψ ha hψ hcψ k] at hn
  nlinarith


private theorem sum_D_square {d : ℕ} (ψ : E d → ℝ) (x : E d) :
    (∑ k, (D ψ k x)^2) = ‖gradient ψ x‖^2 := by
  have hi (k : Fin d) : D ψ k x = inner ℝ (gradient ψ x) (EuclideanSpace.basisFun (Fin d) ℝ k) := by
    have h := congrArg (fun L : E d →L[ℝ] ℝ => L (EuclideanSpace.basisFun (Fin d) ℝ k))
      (toDual_gradient (𝕜:=ℝ) (f:=ψ) (x:=x))
    simpa [D, InnerProductSpace.toDual_apply_apply] using h.symm
  calc
    _ = ∑ k, ‖inner ℝ (gradient ψ x) (EuclideanSpace.basisFun (Fin d) ℝ k)‖^2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hi, Real.norm_eq_abs, sq_abs]
    _ = _ := (EuclideanSpace.basisFun (Fin d) ℝ).sum_sq_norm_inner_left (gradient ψ x)

private theorem regularized_complete_square_bound {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (ψ : E d → ℝ) (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) (α : ℝ) :
    α*(∫ x, (∑ k, D (A ε k) k x)*(ψ x)^2) -
      α^2*(∫ x, (∑ k, (A ε k x)^2)*(ψ x)^2) ≤ ∫ x, ‖gradient ψ x‖^2 := by
  have hcψ2 : HasCompactSupport (fun x => (ψ x)^2) := by
    simpa [Function.comp_def] using hcψ.comp_left (g:=fun z : ℝ => z^2) (by simp)
  have hDA (k : Fin d) : Integrable (fun x => D (A ε k) k x*(ψ x)^2) volume :=
    integrable_mul_compact _ _ (continuous_D (A_contDiff hε k) k) (hψ.continuous.pow 2) hcψ2
  have hP (k : Fin d) : Integrable (fun x => (A ε k x)^2*(ψ x)^2) volume :=
    integrable_mul_compact _ _ ((A_contDiff hε k).continuous.pow 2) (hψ.continuous.pow 2) hcψ2
  have hE (k : Fin d) : Integrable (fun x => (D ψ k x)^2) volume := by
    simpa only [pow_two] using integrable_mul_compact (D ψ k) (D ψ k)
      (continuous_D hψ k) (continuous_D hψ k) (compact_D hcψ k)
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun k _ =>
    compact_directional_hardy_bound (A ε k) ψ α (A_contDiff hε k) hψ hcψ k)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  rw [← integral_finsetSum Finset.univ (fun k _ => hDA k),
    ← integral_finsetSum Finset.univ (fun k _ => hP k),
    ← integral_finsetSum Finset.univ (fun k _ => hE k)] at hs
  simpa only [← Finset.sum_mul, sum_D_square] using hs

private theorem regularized_hardy_potential {d : ℕ} {ε : ℝ} (hε : 0 < ε) (x : E d) :
    let α := ((d : ℝ)-2)/2
    α*(∑ k, D (A ε k) k x) - α^2*(∑ k, (A ε k x)^2) =
      α^2/R ε x + α*(α+2)*ε^2/(R ε x)^2 := by
  dsimp only
  rw [A_divergence hε, A_square_sum]
  have hn : R ε x ≠ 0 := (R_pos hε x).ne'
  field_simp
  unfold R
  ring

private theorem euclidean_hardy_regularized {d : ℕ} (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (ψ : E d → ℝ) (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) :
    (((d : ℝ)-2)^2/4)*(∫ x, (ψ x)^2/(‖x‖^2+ε^2)) ≤ ∫ x, ‖gradient ψ x‖^2 := by
  let α := ((d : ℝ)-2)/2
  have hα : 0 ≤ α := by
    have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
    dsimp [α]
    linarith
  have hcψ2 : HasCompactSupport (fun x => (ψ x)^2) := by
    simpa [Function.comp_def] using hcψ.comp_left (g:=fun z : ℝ => z^2) (by simp)
  have hDA : Integrable (fun x => (∑ k, D (A ε k) k x)*(ψ x)^2) volume := by
    apply integrable_mul_compact _ _ _ (hψ.continuous.pow 2) hcψ2
    exact continuous_finset_sum _ (fun k _ => continuous_D (A_contDiff hε k) k)
  have hP : Integrable (fun x => (∑ k, (A ε k x)^2)*(ψ x)^2) volume := by
    apply integrable_mul_compact _ _ _ (hψ.continuous.pow 2) hcψ2
    exact continuous_finset_sum _ (fun k _ => (A_contDiff hε k).continuous.pow 2)
  have hR : Continuous (fun x : E d => (R ε x)⁻¹) :=
    ((continuous_norm.pow 2).add continuous_const).inv₀ (fun x => (R_pos hε x).ne')
  have hW : Integrable (fun x => α^2*(ψ x)^2/R ε x) volume := by
    have hh := (integrable_mul_compact (fun x => (R ε x)⁻¹) (fun x => (ψ x)^2) hR (hψ.continuous.pow 2) hcψ2).const_mul (α^2)
    convert hh using 1
    funext x
    ring
  have hPot : Integrable (fun x => (α*(∑ k, D (A ε k) k x)-α^2*(∑ k, (A ε k x)^2))*(ψ x)^2) volume := by
    convert (hDA.const_mul α).sub (hP.const_mul (α^2)) using 1
    funext x
    simp only [Pi.sub_apply]
    ring
  have hm : (∫ x, α^2*(ψ x)^2/R ε x) ≤
      ∫ x, (α*(∑ k, D (A ε k) k x)-α^2*(∑ k, (A ε k x)^2))*(ψ x)^2 := by
    apply integral_mono hW hPot
    intro x
    change α^2*(ψ x)^2/R ε x ≤ (α*(∑ k, D (A ε k) k x)-α^2*(∑ k, (A ε k x)^2))*(ψ x)^2
    dsimp only [α]
    rw [regularized_hardy_potential hε x]
    have hp : 0 ≤ α*(α+2)*ε^2/(R ε x)^2 := by positivity
    dsimp only [α] at hp
    convert mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hp) (sq_nonneg (ψ x)) using 1 <;> ring
  have hs := regularized_complete_square_bound hε ψ hψ hcψ α
  have heq : (∫ x, (α*(∑ k, D (A ε k) k x)-α^2*(∑ k, (A ε k x)^2))*(ψ x)^2) =
      α*(∫ x, (∑ k, D (A ε k) k x)*(ψ x)^2)-α^2*(∫ x, (∑ k, (A ε k x)^2)*(ψ x)^2) := by
    calc
      _ = ∫ x, α*((∑ k, D (A ε k) k x)*(ψ x)^2)-α^2*((∑ k, (A ε k x)^2)*(ψ x)^2) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by ring)
      _ = _ := by rw [integral_sub (hDA.const_mul α) (hP.const_mul (α^2)), integral_const_mul, integral_const_mul]
  rw [heq] at hm
  have hb := hm.trans hs
  have hc : (((d : ℝ)-2)^2/4) = α^2 := by dsimp [α]; ring
  rw [hc, ← integral_const_mul]
  simpa only [R, mul_div_assoc] using hb


private theorem compact_inverse_square_integrable {d : ℕ} (hd : 3 ≤ d)
    (ψ : E d → ℝ) (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) :
    Integrable (fun x => (ψ x)^2/‖x‖^2) volume := by
  have hcψ2 : HasCompactSupport (fun x => (ψ x)^2) := by
    simpa [Function.comp_def] using hcψ.comp_left (g:=fun z : ℝ => z^2) (by simp)
  obtain ⟨M,hM⟩ := hcψ2.exists_bound_of_continuous (hψ.pow 2)
  obtain ⟨r,hr,hrb⟩ := hcψ.isBounded.exists_pos_norm_lt
  have hdim : 1 ≤ Module.finrank ℝ (E d) := by simpa [E] using (show 1 ≤ d by omega)
  have hd' : (2 : ℝ) < Module.finrank ℝ (E d) := by
    simp only [E, finrank_euclideanSpace, Fintype.card_fin]
    exact_mod_cast (show 2 < d by omega)
  have hmeas : AEStronglyMeasurable (fun x => (ψ x)^2/‖x‖^2) volume :=
    ((hψ.measurable.pow_const 2).div (continuous_norm.measurable.pow_const 2)).aestronglyMeasurable
  have hlocal : IntegrableOn (fun x => (ψ x)^2/‖x‖^2) (Metric.ball 0 r) volume := by
    apply integrableOn_ball_of_norm_le_rpow (C:=M) (α:=2) hdim hd' _ hmeas
    exact Filter.Eventually.of_forall (fun x => by
      have hm := mul_le_mul_of_nonneg_right (hM x) (inv_nonneg.mpr (sq_nonneg ‖x‖))
      simpa only [div_eq_mul_inv, norm_mul, norm_pow, norm_inv, norm_norm,
        Real.rpow_neg (norm_nonneg x), Real.rpow_two] using hm)
  apply (integrableOn_iff_integrable_of_support_subset (s:=Metric.ball 0 r) ?_).mp hlocal
  intro x hx
  rw [Metric.mem_ball, dist_zero_right]
  apply hrb x
  apply subset_tsupport ψ
  intro hp
  simp only [Function.mem_support, hp, zero_pow (by norm_num : 2 ≠ 0), zero_div, ne_eq, not_true_eq_false] at hx

private theorem euclidean_hardy_compact {d : ℕ} (hd : 3 ≤ d)
    (ψ : E d → ℝ) (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) :
    (((d : ℝ)-2)^2/4)*(∫ x, (ψ x)^2/‖x‖^2) ≤ ∫ x, ‖gradient ψ x‖^2 := by
  haveI : NeZero d := ⟨by omega⟩
  let ε : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεlim : Filter.Tendsto ε Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hz : ∀ᵐ x ∂(volume : Measure (E d)), x ≠ 0 := by
    simp only [ae_iff, not_ne_iff]
    exact measure_singleton 0
  have hI := compact_inverse_square_integrable hd ψ hψ.continuous hcψ
  have hlim : Filter.Tendsto (fun n => ∫ x : E d, (ψ x)^2/(‖x‖^2+(ε n)^2))
      Filter.atTop (nhds (∫ x : E d, (ψ x)^2/‖x‖^2)) := by
    apply tendsto_integral_of_dominated_convergence (fun x : E d => (ψ x)^2/‖x‖^2)
    · intro n
      exact ((hψ.continuous.measurable.pow_const 2).div
        ((continuous_norm.measurable.pow_const 2).add measurable_const)).aestronglyMeasurable
    · exact hI
    · intro n
      filter_upwards [hz] with x hx
      have hn : 0 < ‖x‖^2 := by exact pow_pos (norm_pos_iff.mpr hx) _
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (ψ x)^2/(‖x‖^2+(ε n)^2))]
      exact div_le_div_of_nonneg_left (sq_nonneg _) hn (le_add_of_nonneg_right (sq_nonneg _))
    · filter_upwards [hz] with x hx
      have hn : ‖x‖^2 ≠ 0 := by positivity
      have ht : Filter.Tendsto (fun n => ‖x‖^2+(ε n)^2) Filter.atTop (nhds (‖x‖^2)) := by
        simpa using (tendsto_const_nhds (x:=‖x‖^2)).add (hεlim.pow 2)
      have hh := (tendsto_const_nhds (x:=(ψ x)^2)).div ht hn
      convert hh using 1
      funext n
      simp only [Pi.div_apply]
  have hbound (n : ℕ) := euclidean_hardy_regularized hd (hε n) ψ hψ hcψ
  exact le_of_tendsto (tendsto_const_nhds.mul hlim) (Filter.Eventually.of_forall hbound)

end EuclideanHardy

-- [TABLET NODE: EuclideanHardy]
theorem EuclideanHardy {d : ℕ} (hd : 3 ≤ d)
    (f : OneParticle d → ℝ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    Integrable (fun x => (f x)^2 / ‖x‖^2) volume ∧
      (((d : ℝ) - 2)^2 / 4) * (∫ x, (f x)^2 / ‖x‖^2) ≤
        ∫ x, ‖EuclideanGradient f x‖^2 := by
-- BODY
  exact ⟨EuclideanHardy.compact_inverse_square_integrable hd f hf.continuous hc,
    EuclideanHardy.euclidean_hardy_compact hd f hf hc⟩
