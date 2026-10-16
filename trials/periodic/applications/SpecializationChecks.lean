import ActualFinalSpecializationBridge
import Tablet.UniformClosedGradientPoincare
import Tablet.UniformClosedGradientLogSobolev
import Tablet.CanonicalGradientCoreEquality
import Tablet.TorusCharacterCalculus
import Mathlib.MeasureTheory.Measure.OpenPos
open MeasureTheory ProbabilityTheory Set Filter
open scoped ContDiff
noncomputable section
local instance circle_probability : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  simp
  infer_instance

def firstMode : Fin 2 → ℤ := Pi.single 0 1

def cosineReferenceDensity (x : UnitAddTorus (Fin 2)) : ℝ :=
  1+(1/2:ℝ)*(UnitAddTorus.mFourier firstMode x).re

lemma firstMode_ne_zero : firstMode ≠ 0 := by
  intro h
  have := congrFun h 0
  norm_num [firstMode] at this

lemma firstMode_mean_zero : (∫ x : UnitAddTorus (Fin 2), UnitAddTorus.mFourier firstMode x) = 0 := by
  have h := (orthonormal_iff_ite.mp (UnitAddTorus.orthonormal_mFourier (d := Fin 2))) 0 firstMode
  simp only [UnitAddTorus.mFourierLp, ContinuousMap.inner_toLp,
    UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, map_one, mul_one] at h
  change (∫ x : UnitAddTorus (Fin 2), UnitAddTorus.mFourier firstMode x
      ∂Measure.pi (fun _ : Fin 2 => AddCircle.haarAddCircle)) = (if (0 : Fin 2 → ℤ) = firstMode then 1 else 0) at h
  have hzero : (∫ x : UnitAddTorus (Fin 2), UnitAddTorus.mFourier firstMode x
      ∂Measure.pi (fun _ : Fin 2 => AddCircle.haarAddCircle)) = 0 := by
    simpa [Ne.symm firstMode_ne_zero] using h
  have heq : (volume : Measure (UnitAddTorus (Fin 2))) =
      Measure.pi (fun _ : Fin 2 => AddCircle.haarAddCircle) := by
    change Measure.pi (fun _ : Fin 2 => (volume : Measure (AddCircle (1:ℝ)))) = _
    congr 1
    funext i
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
  rw [heq]
  exact hzero

lemma cosineReferenceDensity_continuous : Continuous cosineReferenceDensity := by
  exact continuous_const.add (continuous_const.mul (Complex.continuous_re.comp (UnitAddTorus.mFourier firstMode).continuous))

lemma cosineReferenceDensity_bounds (x : UnitAddTorus (Fin 2)) :
    (1/2:ℝ) ≤ cosineReferenceDensity x ∧ cosineReferenceDensity x ≤ 3/2 := by
  have hn : ‖UnitAddTorus.mFourier firstMode x‖ ≤ 1 := by
    simpa [UnitAddTorus.mFourier_norm] using (UnitAddTorus.mFourier firstMode).norm_coe_le_norm x
  have hr := Complex.abs_re_le_norm (UnitAddTorus.mFourier firstMode x)
  have h := abs_le.mp (hr.trans hn)
  dsimp [cosineReferenceDensity]
  constructor <;> linarith

lemma cosineReferenceDensity_mass : (∫ x : UnitAddTorus (Fin 2), cosineReferenceDensity x) = 1 := by
  have hi : Integrable (fun x : UnitAddTorus (Fin 2) => UnitAddTorus.mFourier firstMode x) volume :=
    (UnitAddTorus.mFourier firstMode).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hr : (∫ x : UnitAddTorus (Fin 2), (UnitAddTorus.mFourier firstMode x).re) = 0 := by
    have h := integral_re hi
    change (∫ x : UnitAddTorus (Fin 2), (UnitAddTorus.mFourier firstMode x).re) = (∫ x : UnitAddTorus (Fin 2), UnitAddTorus.mFourier firstMode x).re at h
    simpa only [firstMode_mean_zero, Complex.zero_re] using h
  change (∫ x : UnitAddTorus (Fin 2), 1+(1/2:ℝ)*(UnitAddTorus.mFourier firstMode x).re) = 1
  have hri : Integrable (fun x : UnitAddTorus (Fin 2) => (UnitAddTorus.mFourier firstMode x).re) volume := by
    exact Complex.reCLM.integrable_comp hi
  rw [integral_add (integrable_const _) (hri.const_mul _), integral_const_mul, hr]
  simp

def cosineReference : BoundedBackground 2 (1/2) (3/2) where
  density := cosineReferenceDensity
  measurable := cosineReferenceDensity_continuous.measurable
  lower_pos := by norm_num
  lower_le_one := by norm_num
  one_le_upper := by norm_num
  bounds := Eventually.of_forall cosineReferenceDensity_bounds
  mass := cosineReferenceDensity_mass

lemma cosineReference_at_zero : cosineReferenceDensity 0 = 3/2 := by
  simp [cosineReferenceDensity, UnitAddTorus.mFourier, fourier_eval_zero]
  norm_num

lemma cosineReference_at_half : cosineReferenceDensity (fun _ => ((1/2:ℝ) : AddCircle (1:ℝ))) = 1/2 := by
  have hc : UnitAddTorus.mFourier firstMode (fun _ => ((1/2:ℝ) : AddCircle (1:ℝ))) = (-1:ℂ) := by
    rw [show firstMode = Pi.single 0 1 from rfl, UnitAddTorus.mFourier_single]
    rw [fourier_coe_apply]
    convert Complex.exp_pi_mul_I using 1 <;> push_cast <;> ring
  change 1+(1/2:ℝ)*(UnitAddTorus.mFourier firstMode (fun _ => ((1/2:ℝ) : AddCircle (1:ℝ)))).re = 1/2
  rw [hc]
  norm_num

lemma cosineReference_not_ae_constant : ¬∃c:ℝ, cosineReferenceDensity =ᵐ[volume] (fun _=>c) := by
  rintro ⟨c,hc⟩
  have he := Measure.eq_of_ae_eq hc cosineReferenceDensity_continuous continuous_const
  have h0 := congrFun he 0
  have hhalf := congrFun he (fun _ => ((1/2:ℝ) : AddCircle (1:ℝ)))
  rw [cosineReference_at_zero] at h0
  rw [cosineReference_at_half] at hhalf
  linarith

theorem two_dimensional_logarithmic_poincare (a B l u : ℝ) (ha : 0<a) (hB : 0≤B) (hl : 0<l) (hl1 : l≤1) (hu : 1≤u) :
    ∃ rate : ℝ, 0 < rate ∧ ∀ (N : ℕ), 2 ≤ N →
      ∀ (β : ℝ), 0 ≤ β → β ≤ B → ∀ (q : BoundedBackground 2 l u),
      ∀ (ε : ℝ), 0 ≤ ε →
      let P := CanonicalLaw (N := N) (RieszKernel 2 0 a ε) q.density β
      ∀ (f : Lp ℝ 2 P) (v : Lp (EuclideanSpace ℝ (Fin N×Fin 2)) 2 P),
      (f,v)∈GradientGraphClosure P false →
      variance (f:Configuration 2 N→ℝ) P≤rate⁻¹*ClosedGradientEnergy v  := by
  exact ActualFinalPoincare 2 (by norm_num) 0 a B l u (by norm_num) (by norm_num) ha hB hl hl1 hu

theorem three_dimensional_coulomb_poincare (a B l u : ℝ) (ha : 0<a) (hB : 0≤B) (hl : 0<l) (hl1 : l≤1) (hu : 1≤u) :
    ∃ rate : ℝ, 0 < rate ∧ ∀ (N : ℕ), 2 ≤ N →
      ∀ (β : ℝ), 0 ≤ β → β ≤ B → ∀ (q : BoundedBackground 3 l u),
      ∀ (ε : ℝ), 0 ≤ ε →
      let P := CanonicalLaw (N := N) (RieszKernel 3 1 a ε) q.density β
      ∀ (f : Lp ℝ 2 P) (v : Lp (EuclideanSpace ℝ (Fin N×Fin 3)) 2 P),
      (f,v)∈GradientGraphClosure P false →
      variance (f:Configuration 3 N→ℝ) P≤rate⁻¹*ClosedGradientEnergy v  := by
  exact ActualFinalPoincare 3 (by norm_num) 1 a B l u (by norm_num) (by norm_num) ha hB hl hl1 hu

theorem four_dimensional_coulomb_poincare (a B l u : ℝ) (ha : 0<a) (hB : 0≤B) (hl : 0<l) (hl1 : l≤1) (hu : 1≤u) :
    ∃ rate : ℝ, 0 < rate ∧ ∀ (N : ℕ), 2 ≤ N →
      ∀ (β : ℝ), 0 ≤ β → β ≤ B → ∀ (q : BoundedBackground 4 l u),
      ∀ (ε : ℝ), 0 ≤ ε →
      let P := CanonicalLaw (N := N) (RieszKernel 4 2 a ε) q.density β
      ∀ (f : Lp ℝ 2 P) (v : Lp (EuclideanSpace ℝ (Fin N×Fin 4)) 2 P),
      (f,v)∈GradientGraphClosure P false →
      variance (f:Configuration 4 N→ℝ) P≤rate⁻¹*ClosedGradientEnergy v  := by
  exact ActualFinalPoincare 4 (by norm_num) 2 a B l u (by norm_num) (by norm_num) ha hB hl hl1 hu

theorem noninteger_subcoulomb_poincare (a B l u : ℝ) (ha : 0<a) (hB : 0≤B) (hl : 0<l) (hl1 : l≤1) (hu : 1≤u) :
    ∃ rate : ℝ, 0 < rate ∧ ∀ (N : ℕ), 2 ≤ N →
      ∀ (β : ℝ), 0 ≤ β → β ≤ B → ∀ (q : BoundedBackground 3 l u),
      ∀ (ε : ℝ), 0 ≤ ε →
      let P := CanonicalLaw (N := N) (RieszKernel 3 (1/2:ℝ) a ε) q.density β
      ∀ (f : Lp ℝ 2 P) (v : Lp (EuclideanSpace ℝ (Fin N×Fin 3)) 2 P),
      (f,v)∈GradientGraphClosure P false →
      variance (f:Configuration 3 N→ℝ) P≤rate⁻¹*ClosedGradientEnergy v  := by
  exact ActualFinalPoincare 3 (by norm_num) (1/2:ℝ) a B l u (by norm_num) (by norm_num) ha hB hl hl1 hu

theorem two_dimensional_logarithmic_log_sobolev (a B l u : ℝ) (ha : 0<a) (hB : 0≤B) (hl : 0<l) (hl1 : l≤1) (hu : 1≤u) :
    ∃rate:ℝ,0<rate ∧ ∀N:ℕ,2≤N→∀β:ℝ,0≤β→β≤B→
      ∀q:BoundedBackground 2 l u,∀ε:ℝ,0≤ε→
      let P:=CanonicalLaw (N:=N) (RieszKernel 2 0 a ε) q.density β
      ∀(f:Lp ℝ 2 P)(v:Lp (EuclideanSpace ℝ (Fin N×Fin 2)) 2 P),
        (f,v)∈GradientGraphClosure P false →
        ExtendedEntropy P (fun X=>f X^2)≤ENNReal.ofReal ((2/rate)*ClosedGradientEnergy v)  := by
  exact ActualFinalLogSobolev 2 (by norm_num) 0 a B l u (by norm_num) (by norm_num) (by norm_num) ha hB hl hl1 hu

theorem three_dimensional_coulomb_log_sobolev (a B l u : ℝ) (ha : 0<a) (hB : 0≤B) (hl : 0<l) (hl1 : l≤1) (hu : 1≤u) :
    ∃rate:ℝ,0<rate ∧ ∀N:ℕ,2≤N→∀β:ℝ,0≤β→β≤B→
      ∀q:BoundedBackground 3 l u,∀ε:ℝ,0≤ε→
      let P:=CanonicalLaw (N:=N) (RieszKernel 3 1 a ε) q.density β
      ∀(f:Lp ℝ 2 P)(v:Lp (EuclideanSpace ℝ (Fin N×Fin 3)) 2 P),
        (f,v)∈GradientGraphClosure P false →
        ExtendedEntropy P (fun X=>f X^2)≤ENNReal.ofReal ((2/rate)*ClosedGradientEnergy v)  := by
  exact ActualFinalLogSobolev 3 (by norm_num) 1 a B l u (by norm_num) (by norm_num) (by norm_num) ha hB hl hl1 hu

theorem noninteger_subcoulomb_log_sobolev (a B l u : ℝ) (ha : 0<a) (hB : 0≤B) (hl : 0<l) (hl1 : l≤1) (hu : 1≤u) :
    ∃rate:ℝ,0<rate ∧ ∀N:ℕ,2≤N→∀β:ℝ,0≤β→β≤B→
      ∀q:BoundedBackground 3 l u,∀ε:ℝ,0≤ε→
      let P:=CanonicalLaw (N:=N) (RieszKernel 3 (1/2:ℝ) a ε) q.density β
      ∀(f:Lp ℝ 2 P)(v:Lp (EuclideanSpace ℝ (Fin N×Fin 3)) 2 P),
        (f,v)∈GradientGraphClosure P false →
        ExtendedEntropy P (fun X=>f X^2)≤ENNReal.ofReal ((2/rate)*ClosedGradientEnergy v)  := by
  exact ActualFinalLogSobolev 3 (by norm_num) (1/2:ℝ) a B l u (by norm_num) (by norm_num) (by norm_num) ha hB hl hl1 hu

theorem four_dimensional_coulomb_excluded_from_HS : ¬(2:ℝ)<(4:ℝ)/2 := by norm_num

lemma configurationLift_quotient (d N : ℕ) :
    IsOpenQuotientMap (ConfigurationLift d N) := by
  have hc : IsOpenQuotientMap ((↑) : ℝ → AddCircle (1 : ℝ)) :=
    QuotientAddGroup.isOpenQuotientMap_mk
  have hp : IsOpenQuotientMap
      (Pi.map (fun _ : Fin N × Fin d => ((↑) : ℝ → AddCircle (1 : ℝ)))) :=
    IsOpenQuotientMap.piMap (fun _ => hc)
  have he := (PiLp.homeomorph 2 (fun _ : Fin N × Fin d => ℝ)).isOpenQuotientMap
  have hh := (Homeomorph.piCurry (X := Fin N) (Y := Fin d)
    (Z := AddCircle (1 : ℝ))).isOpenQuotientMap
  exact hh.comp (hp.comp he)

lemma smoothCore_continuous {d N : ℕ} {f : Configuration d N → ℝ}
    (hf : f ∈ SmoothCore d N) : Continuous f := by
  apply (configurationLift_quotient d N).continuous_comp_iff.mp
  exact (show ContDiff ℝ ∞ (fun y => f (ConfigurationLift d N y)) from hf).continuous

lemma smoothCore_bounded {d N : ℕ} {f : Configuration d N → ℝ}
    (hf : f ∈ SmoothCore d N) : ∃ C : ℝ, ∀ X, |f X| ≤ C := by
  have hc := (smoothCore_continuous hf).abs
  rcases isCompact_univ.exists_isMaxOn Set.univ_nonempty hc.continuousOn with ⟨X0,hX0,hmax⟩
  exact ⟨|f X0|, fun X => hmax (Set.mem_univ X)⟩

-- Derivative descent is the only remaining topological step.
lemma lift_translation_eq {d N : ℕ} (y z : EuclideanSpace ℝ (Fin N × Fin d))
    (h : ConfigurationLift d N y = ConfigurationLift d N z)
    (x : EuclideanSpace ℝ (Fin N × Fin d)) :
    ConfigurationLift d N (x + (z-y)) = ConfigurationLift d N x := by
  funext i j
  have hj := congrFun (congrFun h i) j
  change (y (i,j) : AddCircle (1 : ℝ)) = (z (i,j) : AddCircle (1 : ℝ)) at hj
  simp only [ConfigurationLift, PiLp.add_apply, PiLp.sub_apply]
  rw [AddCircle.coe_add, AddCircle.coe_sub, ← hj, sub_self, add_zero]

lemma lift_fderiv_eq {d N : ℕ} (f : Configuration d N → ℝ)
    (y z : EuclideanSpace ℝ (Fin N × Fin d))
    (h : ConfigurationLift d N y = ConfigurationLift d N z) :
    fderiv ℝ (fun x => f (ConfigurationLift d N x)) y =
      fderiv ℝ (fun x => f (ConfigurationLift d N x)) z := by
  let q := fun x => f (ConfigurationLift d N x)
  have hfun : (fun x => q (x+(z-y))) = q := by
    funext x
    exact congrArg f (lift_translation_eq y z h x)
  have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := q) (x := y) (z-y)
  rw [hfun] at hd
  simpa using hd

lemma coordinateGradient_on_lift {d N : ℕ} (f : Configuration d N → ℝ)
    (y : EuclideanSpace ℝ (Fin N × Fin d)) (ij : Fin N × Fin d) :
    CoordinateGradient f (ConfigurationLift d N y) ij =
      fderiv ℝ (fun x => f (ConfigurationLift d N x)) y
        (EuclideanSpace.single ij 1) := by
  let z : EuclideanSpace ℝ (Fin N × Fin d) := WithLp.toLp 2
    (fun ij => (AddCircle.equivIco (1 : ℝ) 0 (ConfigurationLift d N y ij.1 ij.2) : ℝ))
  have hz : ConfigurationLift d N z = ConfigurationLift d N y := by
    funext i j
    simp [ConfigurationLift, z, AddCircle.coe_equivIco]
  change fderiv ℝ (fun x => f (ConfigurationLift d N x)) z (EuclideanSpace.single ij 1) = _
  rw [lift_fderiv_eq f z y hz]

lemma coordinateGradient_continuous {d N : ℕ} {f : Configuration d N → ℝ}
    (hf : f ∈ SmoothCore d N) : Continuous (CoordinateGradient f) := by
  apply (configurationLift_quotient d N).continuous_comp_iff.mp
  have hF : ContDiff ℝ ∞ (fun y => f (ConfigurationLift d N y)) := hf
  have hc : Continuous (fun y : EuclideanSpace ℝ (Fin N × Fin d) =>
      WithLp.toLp 2 (fun ij => fderiv ℝ (fun x => f (ConfigurationLift d N x)) y
        (EuclideanSpace.single ij 1))) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin N × Fin d => ℝ)).comp
    apply continuous_pi
    intro ij
    exact (hF.continuous_fderiv_apply (by simp)).comp
      (continuous_id.prodMk continuous_const)
  have he : (fun y => CoordinateGradient f (ConfigurationLift d N y)) =
      (fun y : EuclideanSpace ℝ (Fin N × Fin d) =>
        WithLp.toLp 2 (fun ij => fderiv ℝ (fun x => f (ConfigurationLift d N x)) y
          (EuclideanSpace.single ij 1))) := by
    funext y
    ext ij
    exact coordinateGradient_on_lift f y ij
  have hg : Continuous (fun y => CoordinateGradient f (ConfigurationLift d N y)) := by
    rw [he]
    exact hc
  exact hg

lemma smooth_memLp {d N:ℕ}(P:Measure (Configuration d N))[IsProbabilityMeasure P]
    {f:Configuration d N→ℝ}(hf:f∈SmoothCore d N) :
    MemLp f 2 P ∧ MemLp (CoordinateGradient f) 2 P := by
  exact ⟨(smoothCore_continuous hf).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _),
    (coordinateGradient_continuous hf).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)⟩

def labeledCosine (X : Configuration 2 2) : ℝ := (fourier 1 (X 0 0)).re

def phase : EuclideanSpace ℝ (Fin 2×Fin 2) →L[ℝ] ℝ :=
  (2*Real.pi) • EuclideanSpace.proj (0,0)

lemma labeledCosine_lift (y : EuclideanSpace ℝ (Fin 2×Fin 2)) :
    labeledCosine (ConfigurationLift 2 2 y) = Real.cos (phase y) := by
  unfold labeledCosine ConfigurationLift
  rw [fourier_coe_apply,Complex.exp_re]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    Complex.one_re,Complex.one_im,mul_zero,zero_mul,sub_zero,mul_one,zero_add,add_zero,
    Complex.div_re,Complex.normSq_one,div_one,Real.exp_zero,one_mul]
  simp [phase,smul_eq_mul,mul_assoc,mul_comm,mul_left_comm]

lemma labeledCosine_smooth : labeledCosine ∈ SmoothCore 2 2 := by
  change ContDiff ℝ ∞ (fun y => labeledCosine (ConfigurationLift 2 2 y))
  simp_rw [labeledCosine_lift]
  exact phase.contDiff.cos

lemma labeledCosine_not_symmetric :
    ¬∀X:Configuration 2 2,labeledCosine (fun i=>X (Equiv.swap (0:Fin 2) 1 i))=labeledCosine X := by
  intro h
  let X : Configuration 2 2 := fun i _ => if i=0 then 0 else ((1/2:ℝ):AddCircle (1:ℝ))
  have hx:=h X
  have he : fourier 1 (((1/2:ℝ)):AddCircle (1:ℝ)) = (-1:ℂ) := by
    rw [fourier_coe_apply]
    convert Complex.exp_pi_mul_I using 1 <;> push_cast <;> ring
  have h10 : (1:Fin 2) ≠ 0 := by decide
  simp only [labeledCosine,Equiv.swap_apply_left,X,h10,if_false,if_true,fourier_eval_zero,Complex.one_re] at hx
  rw [he] at hx
  norm_num at hx

lemma labeledCosine_memLp (a ε : ℝ) (ha : 0<a) (hε : 0≤ε) :
    let P := CanonicalLaw (N:=2) (RieszKernel 2 0 a ε) cosineReference.density 0
    MemLp labeledCosine 2 P ∧ MemLp (CoordinateGradient labeledCosine) 2 P := by
  let P := CanonicalLaw (N:=2) (RieszKernel 2 0 a ε) cosineReference.density 0
  letI : IsProbabilityMeasure P :=
    (CanonicalCutoffConvergence 2 2 (by norm_num) (by norm_num) 0 a (1/2) (3/2) 0
      (by norm_num) (by norm_num) ha cosineReference (by norm_num)).1 ε hε
  exact smooth_memLp P labeledCosine_smooth

lemma labeledCosine_in_full_graph (a ε : ℝ) (ha : 0<a) (hε : 0≤ε) :
    let P := CanonicalLaw (N:=2) (RieszKernel 2 0 a ε) cosineReference.density 0
    ∃(hf:MemLp labeledCosine 2 P)(hv:MemLp (CoordinateGradient labeledCosine) 2 P),
      (hf.toLp labeledCosine,hv.toLp (CoordinateGradient labeledCosine)) ∈ GradientGraphClosure P false := by
  obtain ⟨hf,hv⟩ := labeledCosine_memLp a ε ha hε
  refine ⟨hf,hv,subset_closure ?_⟩
  exact ⟨labeledCosine,hf,hv,labeledCosine_smooth,rfl⟩

theorem zero_coupling_nonconstant_reference (a : ℝ) (ha : 0<a) :
    ∃ piRate lsiRate : ℝ, 0<piRate ∧ 0<lsiRate ∧
      (¬∃c:ℝ, cosineReference.density =ᵐ[volume] (fun _=>c)) ∧
      ∀N:ℕ,2≤N→∀ε:ℝ,0≤ε→
      let P := CanonicalLaw (N:=N) (RieszKernel 2 0 a ε) cosineReference.density 0
      ∀(f:Lp ℝ 2 P)(v:Lp (EuclideanSpace ℝ (Fin N×Fin 2)) 2 P),
        (f,v)∈GradientGraphClosure P false →
        variance (f:Configuration 2 N→ℝ) P ≤ piRate⁻¹*ClosedGradientEnergy v ∧
        ExtendedEntropy P (fun X=>f X^2) ≤ ENNReal.ofReal ((2/lsiRate)*ClosedGradientEnergy v) := by
  obtain ⟨piRate,hpi,hPI⟩ := two_dimensional_logarithmic_poincare a 0 (1/2) (3/2)
    ha (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨lsiRate,hlsi,hLSI⟩ := two_dimensional_logarithmic_log_sobolev a 0 (1/2) (3/2)
    ha (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨piRate,lsiRate,hpi,hlsi,cosineReference_not_ae_constant,?_⟩
  intro N hN ε hε
  dsimp only
  intro f v hfv
  exact ⟨hPI N hN 0 (by norm_num) (by norm_num) cosineReference ε hε f v hfv,
    hLSI N hN 0 (by norm_num) (by norm_num) cosineReference ε hε f v hfv⟩

lemma zeroCoupling_ae_eq_iff (a ε : ℝ) (f g : Configuration 2 2 → ℝ) :
    f =ᵐ[CanonicalLaw (N:=2) (RieszKernel 2 0 a ε) cosineReference.density 0] g ↔
      f =ᵐ[volume] g := by
  have hw := ProductBackgroundFacts 2 2 (1/2) (3/2) cosineReference
  have heq : CanonicalLaw (N:=2) (RieszKernel 2 0 a ε) cosineReference.density 0 =
      (volume : Measure (Configuration 2 2)).withDensity
        (fun X => ENNReal.ofReal (ProductDensity cosineReference.density X)) := by
    unfold CanonicalLaw NormalizedTilt GibbsWeight
    simp only [zero_mul,neg_zero,Real.exp_zero,one_mul,hw.2.2.1,div_one]
  rw [heq]
  apply withDensity_ae_eq hw.1.ennreal_ofReal.aemeasurable
  filter_upwards [hw.2.2.2] with X hX
  have hp : 0 < ProductDensity cosineReference.density X :=
    (by norm_num : (0:ℝ)<(1/2:ℝ)^2).trans_le hX.1
  simpa only [ne_eq,ENNReal.ofReal_eq_zero] using not_le.mpr hp

lemma labeledCosine_not_ae_symmetric (a ε : ℝ) :
    ¬(fun X:Configuration 2 2 => labeledCosine (fun i=>X (Equiv.swap (0:Fin 2) 1 i)))
      =ᵐ[CanonicalLaw (N:=2) (RieszKernel 2 0 a ε) cosineReference.density 0] labeledCosine := by
  intro hae
  have hh := (zeroCoupling_ae_eq_iff a ε _ _).mp hae
  have hc : Continuous labeledCosine := smoothCore_continuous labeledCosine_smooth
  have hs : Continuous (fun X:Configuration 2 2 => (fun i=>X (Equiv.swap (0:Fin 2) 1 i))) := by
    exact continuous_pi (fun i=>continuous_apply _)
  have he := Measure.eq_of_ae_eq hh (hc.comp hs) hc
  exact labeledCosine_not_symmetric (fun X=>congrFun he X)

theorem nonsymmetric_labeled_cutoff_removal (a : ℝ) (ha : 0<a) :
    ∃ piRate lsiRate : ℝ, 0<piRate ∧ 0<lsiRate ∧
      (¬∀X:Configuration 2 2,labeledCosine (fun i=>X (Equiv.swap (0:Fin 2) 1 i))=labeledCosine X) ∧
      ∀ε:ℝ,0≤ε→
      let P := CanonicalLaw (N:=2) (RieszKernel 2 0 a ε) cosineReference.density 0
      (¬(fun X:Configuration 2 2 => labeledCosine (fun i=>X (Equiv.swap (0:Fin 2) 1 i))) =ᵐ[P] labeledCosine) ∧
      ∃(hf:MemLp labeledCosine 2 P)(hv:MemLp (CoordinateGradient labeledCosine) 2 P),
        (hf.toLp labeledCosine,hv.toLp (CoordinateGradient labeledCosine))∈GradientGraphClosure P false ∧
        (hf.toLp labeledCosine,hv.toLp (CoordinateGradient labeledCosine))∈GradientGraphClosure P true ∧
        variance (hf.toLp labeledCosine : Configuration 2 2→ℝ) P ≤ piRate⁻¹*ClosedGradientEnergy (hv.toLp (CoordinateGradient labeledCosine)) ∧
        ExtendedEntropy P (fun X=>(hf.toLp labeledCosine) X^2) ≤
          ENNReal.ofReal ((2/lsiRate)*ClosedGradientEnergy (hv.toLp (CoordinateGradient labeledCosine))) := by
  obtain ⟨piRate,lsiRate,hpi,hlsi,hq,hbounds⟩ := zero_coupling_nonconstant_reference a ha
  refine ⟨piRate,lsiRate,hpi,hlsi,labeledCosine_not_symmetric,?_⟩
  intro ε hε
  refine ⟨labeledCosine_not_ae_symmetric a ε,?_⟩
  obtain ⟨hf,hv,hgraph⟩ := labeledCosine_in_full_graph a ε ha hε
  have heq := ActualFinalGraphEquality a ε ha hε cosineReference
  refine ⟨hf,hv,hgraph,?_,?_⟩
  · rw [←heq]
    exact hgraph
  · exact hbounds 2 (by norm_num) ε hε (hf.toLp labeledCosine) (hv.toLp (CoordinateGradient labeledCosine)) hgraph

lemma half_exponent_is_not_integer : ¬∃n:ℤ,(n:ℝ)=(1/2:ℝ) := by
  rintro ⟨n,hn⟩
  have he : ((2*n:ℤ):ℝ)=(1:ℝ) := by push_cast; linarith
  have hi : (2*n:ℤ)=1 := by exact_mod_cast he
  omega
