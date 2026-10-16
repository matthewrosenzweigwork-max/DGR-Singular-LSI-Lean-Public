module

public import RoughMultiplierPI
public import Tablet.QuadraticGaussianClass
public import Tablet.CenteredPotentialDerivatives
public import Collective140

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
open MeasureTheory Filter Set
open scoped ContDiff ENNReal
noncomputable section
namespace WholeSpaceAcceptedClassApplications

def firstCoordinate : E →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0

def coordinateQuadratic (x : E) : ℝ := (1/2:ℝ)*(firstCoordinate x*firstCoordinate x)

def anisotropicPotential (x : E) : ℝ := (fun z : E => ‖z‖^2/2) x+coordinateQuadratic x

theorem coordinateQuadratic_contDiff : ContDiff ℝ ∞ coordinateQuadratic := by
  exact contDiff_const.mul (firstCoordinate.contDiff.mul firstCoordinate.contDiff)

theorem coordinateQuadratic_fderiv :
    fderiv ℝ coordinateQuadratic = firstCoordinate.smulRight firstCoordinate := by
  funext x
  have hh := ((firstCoordinate.hasFDerivAt (x:=x)).mul (firstCoordinate.hasFDerivAt (x:=x))).const_mul (1/2:ℝ)
  have he : coordinateQuadratic = fun y : E => (1/2:ℝ)*(⇑firstCoordinate*⇑firstCoordinate) y := rfl
  rw [he,hh.fderiv]
  ext v
  simp only [ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply,smul_eq_mul]
  ring

theorem coordinateQuadratic_hessian (x u v : E) :
    EuclideanHessian coordinateQuadratic x u v = firstCoordinate u*firstCoordinate v := by
  unfold EuclideanHessian
  rw [coordinateQuadratic_fderiv,ContinuousLinearMap.fderiv]
  simp [ContinuousLinearMap.smulRight_apply,smul_eq_mul]

theorem anisotropicPotential_contDiff : ContDiff ℝ ∞ anisotropicPotential :=
  (QuadraticGaussianClass 3 (0:ℝ)).1.add coordinateQuadratic_contDiff

theorem gaussian_fderiv : fderiv ℝ (fun x : E => ‖x‖^2/2) = innerSL ℝ := by
  funext x
  have h := toDual_gradient (𝕜:=ℝ) (f:=fun x : E => ‖x‖^2/2) (x:=x)
  change (InnerProductSpace.toDual ℝ E) (EuclideanGradient (fun x : E => ‖x‖^2/2) x) = _ at h
  rw [(QuadraticGaussianClass 3 (0:ℝ)).2.1 x] at h
  exact h.symm

theorem anisotropicPotential_hessian (x u v : E) :
    EuclideanHessian anisotropicPotential x u v = inner ℝ u v+firstCoordinate u*firstCoordinate v := by
  have hQ := (QuadraticGaussianClass 3 (0:ℝ)).1.differentiable (by norm_num)
  have hC := coordinateQuadratic_contDiff.differentiable (by norm_num)
  have hf : fderiv ℝ anisotropicPotential =
      fun x => fderiv ℝ ((fun z : E => ‖z‖^2/2)) x+fderiv ℝ coordinateQuadratic x := by
    funext x
    exact fderiv_add (hQ x) (hC x)
  unfold EuclideanHessian
  rw [hf]
  change (fderiv ℝ (fun z : E => fderiv ℝ (fun y : E => (‖y‖^2/2 : ℝ)) z+fderiv ℝ coordinateQuadratic z) x) u v = _
  rw [fderiv_fun_add]
  · simp only [ContinuousLinearMap.add_apply]
    change EuclideanHessian ((fun z : E => ‖z‖^2/2)) x u v+EuclideanHessian coordinateQuadratic x u v = _
    rw [(QuadraticGaussianClass 3 (0:ℝ)).2.2.1,coordinateQuadratic_hessian]
  · rw [gaussian_fderiv]
    exact (innerSL ℝ).differentiableAt
  · rw [coordinateQuadratic_fderiv]
    exact (firstCoordinate.smulRight firstCoordinate).differentiableAt

theorem anisotropicPotential_twoSided : TwoSidedPotential 3 1 2 anisotropicPotential := by
  have hreg : ContDiff ℝ 2 anisotropicPotential :=
    (QuadraticGaussianClass 3 (0:ℝ)).2.2.2.2.1.regularity.add
      (contDiff_const.mul (firstCoordinate.contDiff.mul firstCoordinate.contDiff))
  refine ⟨⟨hreg,?_⟩,?_⟩
  · intro x u
    rw [anisotropicPotential_hessian,real_inner_self_eq_norm_sq]
    nlinarith [sq_nonneg (firstCoordinate u)]
  · intro x u
    rw [anisotropicPotential_hessian,real_inner_self_eq_norm_sq]
    have hn : |firstCoordinate u| ≤ ‖u‖ := by simpa [firstCoordinate,Real.norm_eq_abs] using PiLp.norm_apply_le u 0
    have hs := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg u)).mpr hn
    rw [sq_abs] at hs
    nlinarith

theorem anisotropicPotential_origin : anisotropicPotential 0 = 0 := by
  simp [anisotropicPotential,coordinateQuadratic]

theorem anisotropicPotential_minimum (x : E) : anisotropicPotential 0 ≤ anisotropicPotential x := by
  rw [anisotropicPotential_origin]
  unfold anisotropicPotential coordinateQuadratic
  nlinarith [sq_nonneg ‖x‖,sq_nonneg (firstCoordinate x)]

theorem anisotropicPotential_local (R : ℝ) (hR : 0 < R) (x : E) (hx : ‖x‖ ≤ R) :
    anisotropicPotential x-anisotropicPotential 0 ≤ R^2 := by
  rw [anisotropicPotential_origin,sub_zero]
  have hc : |firstCoordinate x| ≤ ‖x‖ := by simpa [firstCoordinate,Real.norm_eq_abs] using PiLp.norm_apply_le x 0
  have hc2 := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg x)).mpr hc
  rw [sq_abs] at hc2
  unfold anisotropicPotential coordinateQuadratic
  nlinarith [sq_nonneg ‖x‖,sq_nonneg R,norm_nonneg x]

theorem anisotropicPotential_laplacian_upper (x : E) : EuclideanLaplacian anisotropicPotential x ≤ 6 := by
  rw [(EuclideanDerivativeCoordinates anisotropicPotential x).2]
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun i hi =>
    anisotropicPotential_twoSided.upper x (EuclideanSpace.basisFun (Fin 3) ℝ i))
  norm_num at hh
  simpa only [EuclideanSpace.basisFun_apply] using hh

theorem anisotropicPotential_growth (s a : ℝ) (ha : 0 < a) (x : E) :
    EuclideanLaplacian anisotropicPotential x ≤
      a*‖EuclideanGradient anisotropicPotential x‖^(2/(s+1))+6 := by
  have hp : 0 ≤ a*‖EuclideanGradient anisotropicPotential x‖^(2/(s+1)) := by positivity
  linarith [anisotropicPotential_laplacian_upper x]

def translatedAnisotropicPotential (a : E) (c : ℝ) (x : E) : ℝ :=
  anisotropicPotential (x-a)+c

theorem translatedAnisotropicPotential_contDiff (a : E) (c : ℝ) :
    ContDiff ℝ ∞ (translatedAnisotropicPotential a c) :=
  (anisotropicPotential_contDiff.comp (contDiff_id.sub contDiff_const)).add contDiff_const

theorem translatedAnisotropicPotential_hessian (a : E) (c : ℝ) (x u v : E) :
    EuclideanHessian (translatedAnisotropicPotential a c) x u v =
      EuclideanHessian anisotropicPotential (x-a) u v := by
  have he : translatedAnisotropicPotential a c = fun z =>
      (ShiftedReference anisotropicPotential (fun _ => 1) (-a)).1 z+(anisotropicPotential (-a)+c) := by
    funext z
    unfold translatedAnisotropicPotential ShiftedReference
    simp only [sub_eq_add_neg]
    ring
  have hdf : fderiv ℝ (translatedAnisotropicPotential a c) =
      fderiv ℝ ((ShiftedReference anisotropicPotential (fun _ => 1) (-a)).1) := by
    funext z
    rw [he]
    change fderiv ℝ (((ShiftedReference anisotropicPotential (fun _ => 1) (-a)).1) +
      fun _ : E => anisotropicPotential (-a)+c) z = _
    exact fderiv_add_const (𝕜:=ℝ)
      (f:=(ShiftedReference anisotropicPotential (fun _ => 1) (-a)).1)
      (x:=z) (anisotropicPotential (-a)+c)
  unfold EuclideanHessian
  rw [hdf]
  change EuclideanHessian (ShiftedReference anisotropicPotential (fun _ => 1) (-a)).1 x u v = EuclideanHessian anisotropicPotential (x-a) u v
  rw [(CenteredPotentialDerivatives anisotropicPotential (fun _ => 1) (-a)).2.2.1]
  simp only [sub_eq_add_neg]

theorem translatedAnisotropicPotential_twoSided (a : E) (c : ℝ) :
    TwoSidedPotential 3 1 2 (translatedAnisotropicPotential a c) := by
  have hreg : ContDiff ℝ 2 (translatedAnisotropicPotential a c) :=
    (anisotropicPotential_twoSided.regularity.comp (contDiff_id.sub contDiff_const)).add contDiff_const
  refine ⟨⟨hreg,?_⟩,?_⟩
  · intro x u
    rw [translatedAnisotropicPotential_hessian]
    exact anisotropicPotential_twoSided.lower (x-a) u
  · intro x u
    rw [translatedAnisotropicPotential_hessian]
    exact anisotropicPotential_twoSided.upper (x-a) u

theorem translatedAnisotropicPotential_growthClass (s : ℝ) (a : E) (c : ℝ) :
    GrowthClassPotential 3 s 1 (fun R => R^2) (fun _ => 6) (translatedAnisotropicPotential a c) := by
  refine ⟨(translatedAnisotropicPotential_twoSided a c).toPotentialBounds,⟨a,?_,?_⟩,?_⟩
  · intro x
    simp only [translatedAnisotropicPotential,sub_self,anisotropicPotential_origin,zero_add]
    have hh := anisotropicPotential_minimum (x-a)
    rw [anisotropicPotential_origin] at hh
    linarith
  · intro R hR x hx
    simp only [ShiftedReference,translatedAnisotropicPotential,add_sub_cancel_right,sub_self,
      anisotropicPotential_origin,zero_add,add_sub_cancel_left]
    simpa only [anisotropicPotential_origin,sub_zero] using anisotropicPotential_local R hR x hx
  · intro δ hδ x
    have ht := Finset.sum_le_sum (s:=Finset.univ) (fun i hi =>
      (translatedAnisotropicPotential_twoSided a c).upper x (EuclideanSpace.basisFun (Fin 3) ℝ i))
    norm_num at ht
    have hu : EuclideanLaplacian (translatedAnisotropicPotential a c) x ≤ 6 := by
      rw [(EuclideanDerivativeCoordinates (translatedAnisotropicPotential a c) x).2]
      simpa only [EuclideanSpace.basisFun_apply] using ht
    have hp : 0 ≤ δ*‖EuclideanGradient (translatedAnisotropicPotential a c) x‖^ForceExponent s := by positivity
    linarith


theorem actual_translated_rough_allN_closed (s B L : ℝ)
    (hs : 0 < s) (hs1 : s ≤ 1) (hB : 0 ≤ B) (hL : 1 ≤ L) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ centers : ℕ → E, ∀ offsets : ℕ → ℝ,
      ∀ N : ℕ, 2 ≤ N → ∀ β : ℝ, 0 ≤ β → β ≤ B → ∀ ε : ℝ, 0 ≤ ε →
      ∀ q ∈ ClosedGradientGraph (GibbsLaw (N:=N)
        (ReferenceLaw (translatedAnisotropicPotential (centers N) (offsets N)) (roughHalfspaceMultiplier L)) s β ε),
      ρ*ProbabilityTheory.variance (q.1 : ParticleConfig 3 N → ℝ)
        (GibbsLaw (N:=N) (ReferenceLaw (translatedAnisotropicPotential (centers N) (offsets N))
          (roughHalfspaceMultiplier L)) s β ε) ≤ ‖q.2‖^2 := by
  obtain ⟨ρ,hρ,hPI⟩ := (WholeSpaceCollective.allCutoffs
    3 (by norm_num) s B hs (by norm_num; exact hs1) hB).1 1 L (by norm_num) hL
    (fun _ => 6) (fun R => R^2)
  refine ⟨ρ,hρ,?_⟩
  intro centers offsets N hN β hβ hβB ε hε q hq
  exact hPI (translatedAnisotropicPotential (centers N) (offsets N))
    (translatedAnisotropicPotential_growthClass s (centers N) (offsets N))
    (roughHalfspaceMultiplier L) (roughHalfspaceMultiplier_native L hL) N hN β ε hβ hβB hε q hq

end WholeSpaceAcceptedClassApplications
