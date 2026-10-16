import TranslatedAnisotropicPI
import Collective140
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Mul
set_option autoImplicit false
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped ContDiff ENNReal
noncomputable section
namespace WholeSpaceAcceptedClassApplications

def quarticPotential (x : E) : ℝ := ‖x‖^2/2+(firstCoordinate x)^4

theorem quarticPotential_contDiff : ContDiff ℝ ∞ quarticPotential :=
  (QuadraticGaussianClass 3 (0:ℝ)).1.add (firstCoordinate.contDiff.pow 4)

theorem quarticTerm_fderiv : fderiv ℝ (fun x : E => (firstCoordinate x)^4) =
    fun x => (4*(firstCoordinate x)^3) • firstCoordinate := by
  funext x
  simpa using ((firstCoordinate.hasFDerivAt (x:=x)).pow 4).fderiv

theorem quarticTerm_hessian (x u v : E) :
    EuclideanHessian (fun y : E => (firstCoordinate y)^4) x u v =
      12*(firstCoordinate x)^2*firstCoordinate u*firstCoordinate v := by
  have hd := (((firstCoordinate.hasFDerivAt (x:=x)).pow 3).const_mul 4).smul_const firstCoordinate
  unfold EuclideanHessian
  rw [quarticTerm_fderiv, hd.fderiv]
  simp only [ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply,smul_eq_mul]
  ring

theorem quarticPotential_fderiv : fderiv ℝ quarticPotential =
    fun x => innerSL ℝ x+(4*(firstCoordinate x)^3) • firstCoordinate := by
  funext x
  have hg := (QuadraticGaussianClass 3 (0:ℝ)).1.differentiable (by norm_num) x
  have hq := ((firstCoordinate.hasFDerivAt (x:=x)).pow 4).differentiableAt
  change fderiv ℝ ((fun y : E => ‖y‖^2/2)+(fun y : E => (firstCoordinate y)^4)) x = _
  rw [fderiv_add hg hq,gaussian_fderiv,quarticTerm_fderiv]

theorem quarticPotential_hessian (x u v : E) :
    EuclideanHessian quarticPotential x u v = inner ℝ u v+
      12*(firstCoordinate x)^2*firstCoordinate u*firstCoordinate v := by
  unfold EuclideanHessian
  rw [quarticPotential_fderiv]
  have hs : DifferentiableAt ℝ (fun y : E => (4*(firstCoordinate y)^3) • firstCoordinate) x :=
    (((firstCoordinate.hasFDerivAt (x:=x)).pow 3).const_mul 4).smul_const firstCoordinate |>.differentiableAt
  rw [fderiv_fun_add (innerSL ℝ).differentiableAt hs]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.fderiv]
  have he : fderiv ℝ (fun y : E => (4*(firstCoordinate y)^3) • firstCoordinate) x =
      fderiv ℝ (fderiv ℝ (fun y : E => (firstCoordinate y)^4)) x := by rw [quarticTerm_fderiv]
  rw [he]
  change inner ℝ u v+EuclideanHessian (fun y : E => (firstCoordinate y)^4) x u v = _
  rw [quarticTerm_hessian]

theorem quarticPotential_lower (x u : E) :
    (1:ℝ)*‖u‖^2 ≤ EuclideanHessian quarticPotential x u u := by
  rw [quarticPotential_hessian,real_inner_self_eq_norm_sq]
  have hp : 0≤12*(firstCoordinate x)^2*(firstCoordinate u)^2 := by positivity
  nlinarith

theorem quarticPotential_laplacian (x : E) :
    EuclideanLaplacian quarticPotential x=3+12*(firstCoordinate x)^2 := by
  rw [(EuclideanDerivativeCoordinates quarticPotential x).2]
  simp [quarticPotential_hessian,firstCoordinate,Fin.sum_univ_succ,
    EuclideanSpace.basisFun_apply,EuclideanSpace.single_apply]
  ring

theorem quarticPotential_gradient_coordinate (x : E) :
    (EuclideanGradient quarticPotential x) 0=firstCoordinate x+4*(firstCoordinate x)^3 := by
  rw [(EuclideanDerivativeCoordinates quarticPotential x).1]
  change fderiv ℝ quarticPotential x (EuclideanSpace.basisFun (Fin 3) ℝ 0)=_
  rw [quarticPotential_fderiv]
  change inner ℝ x (EuclideanSpace.basisFun (Fin 3) ℝ 0)+
    (4*(firstCoordinate x)^3)*firstCoordinate (EuclideanSpace.basisFun (Fin 3) ℝ 0) = _
  rw [EuclideanSpace.inner_basisFun_real]
  simp [firstCoordinate,EuclideanSpace.basisFun_apply]

theorem quarticPotential_gradient_lower (x : E) :
    4*|firstCoordinate x|^3 ≤ ‖EuclideanGradient quarticPotential x‖ := by
  have hc : |firstCoordinate x+4*(firstCoordinate x)^3| ≤ ‖EuclideanGradient quarticPotential x‖ := by
    have hh := PiLp.norm_apply_le (EuclideanGradient quarticPotential x) 0
    simpa only [Real.norm_eq_abs,quarticPotential_gradient_coordinate] using hh
  have ha : 4*|firstCoordinate x|^3 ≤ |firstCoordinate x+4*(firstCoordinate x)^3| := by
    by_cases hx : 0≤firstCoordinate x
    · rw [abs_of_nonneg hx,abs_of_nonneg (by positivity : 0≤firstCoordinate x+4*(firstCoordinate x)^3)]
      linarith
    · have hx' := le_of_not_ge hx
      rw [abs_of_nonpos hx',abs_of_nonpos (by nlinarith [(by decide : Odd 3).pow_nonpos hx'] : firstCoordinate x+4*(firstCoordinate x)^3≤0)]
      nlinarith
  exact ha.trans hc

theorem quarticPotential_growth (a : ℝ) (ha : 0<a) :
    ∃ C : ℝ, ∀ x : E, EuclideanLaplacian quarticPotential x ≤
      a*‖EuclideanGradient quarticPotential x‖^(2/((1:ℝ)+1))+C := by
  refine ⟨3+12*(3/a)^2,?_⟩
  intro x
  rw [quarticPotential_laplacian]
  norm_num
  let r := |firstCoordinate x|
  have hr : 0≤r := abs_nonneg _
  have hr2 : r^2=(firstCoordinate x)^2 := sq_abs _
  by_cases hsmall : r≤3/a
  · have hsq := (sq_le_sq₀ hr (by positivity : 0≤3/a)).mpr hsmall
    rw [hr2] at hsq
    have hp : 0≤a*‖EuclideanGradient quarticPotential x‖ := mul_nonneg ha.le (norm_nonneg _)
    nlinarith
  · have har : 3≤a*r := by
      have hh : 3/a≤r := le_of_not_ge hsmall
      exact (div_le_iff₀ ha).mp hh |>.trans_eq (mul_comm _ _)
    have hh := mul_le_mul_of_nonneg_right har (sq_nonneg r)
    have hg := mul_le_mul_of_nonneg_left (quarticPotential_gradient_lower x) ha.le
    dsimp only [r] at hh
    rw [sq_abs] at hh
    nlinarith [sq_nonneg (3/a)]

theorem quarticPotential_hessian_unbounded :
    ∀ K : ℝ, ∃ x u : E, K*‖u‖^2 < EuclideanHessian quarticPotential x u u := by
  intro K
  let e := EuclideanSpace.basisFun (Fin 3) ℝ 0
  refine ⟨(|K|+1) • e,e,?_⟩
  rw [quarticPotential_hessian,real_inner_self_eq_norm_sq]
  have hn : ‖e‖=1 := by simp [e,EuclideanSpace.basisFun_apply]
  have he : firstCoordinate e=1 := by simp [e,firstCoordinate,EuclideanSpace.basisFun_apply]
  rw [hn,he]
  simp only [one_pow,mul_one]
  have hx : firstCoordinate ((|K|+1) • e)=|K|+1 := by simp [he]
  rw [hx]
  nlinarith [abs_nonneg K,le_abs_self K,sq_nonneg |K|]

/-- Concrete unbounded-Hessian potential, all-N actual Coulomb closed PI. -/
theorem actual_quartic_coulomb_closed_PI (B L : ℝ) (hB : 0≤B) (hL : 1≤L) :
    ∃ ρ : ℝ,0<ρ ∧ ∀ N : ℕ,2≤N → ∀ b : E→ℝ,BoundedMultiplier 3 L b →
      ∀ coupling ε : ℝ,0≤coupling → coupling≤B → 0≤ε →
      ∀ q∈ClosedGradientGraph (GibbsLaw (N:=N) (ReferenceLaw quarticPotential b) 1 coupling ε),
        ρ*LawVariance (GibbsLaw (N:=N) (ReferenceLaw quarticPotential b) 1 coupling ε) q.1
          ≤ ClosedPhysicalEnergy q := by
  exact (WholeSpaceCollective.allCutoffs 3 (by norm_num) 1 B (by norm_num) (by norm_num)
    hB).2.1 1 L zero_lt_one hL quarticPotential
    (quarticPotential_contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    quarticPotential_lower quarticPotential_growth

end WholeSpaceAcceptedClassApplications
