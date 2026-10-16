module

public import Tablet.CenteredKernelBounds

@[expose] public section
open MeasureTheory
-- [TABLET NODE: CenteredKernelSquareBounds]
theorem CenteredKernelSquareBounds (d : ℕ) (g r : UnitAddTorus (Fin d) → ℝ)
    (hg : Measurable g) (hgi : Integrable g volume)
    (hg2i : Integrable (fun x => (g x)^2) volume)
    (hr : Measurable r) (M c : ℝ) (hM : 1 ≤ M) (hc : 0 ≤ c)
    (hrb : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), 0 ≤ r x ∧ r x ≤ M)
    (hrmass : ∫ x, r x ∂volume = 1) (hgl : ∀ x, -c ≤ g x) :
    let V := M * ∫ x, (g x)^2 ∂volume
    (∀ x, (BackgroundPotential g r x)^2 ≤ V) ∧
    (BackgroundPairMean g r)^2 ≤ V ∧
    (∀ x, Integrable (fun y => (CenteredKernel g r x y)^2*r y) volume ∧
      (∫ y, (CenteredKernel g r x y)^2*r y ∂volume) ≤ 16*V) := by
-- BODY
  have hpot_integral (v w : UnitAddTorus (Fin d)→ℝ) :
      BackgroundPotential v w = fun x => ∫y,v (x-y)*w y := by
    funext x
    unfold BackgroundPotential convolution
    change (∫y,w y*v (x-y)) = ∫y,v (x-y)*w y
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => mul_comm _ _)
  haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
    infer_instance
  haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := by infer_instance
  obtain ⟨hpm,hpf,hpri,hJ,hcm,hcf,hcl⟩ :=
    CenteredKernelBounds d g r hg hgi hr M c hM hc hrb hrmass hgl
  let H := M*∫ x, |g x| ∂volume
  let V := M*∫ x, (g x)^2 ∂volume
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hH : 0 ≤ H := mul_nonneg hM0 (integral_nonneg (fun _ => abs_nonneg _))
  have hrnorm : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), ‖r x‖ ≤ M := by
    filter_upwards [hrb] with x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2
  have hri : Integrable r volume := Integrable.of_bound hr.aestronglyMeasurable M hrnorm
  have square_mean (f : UnitAddTorus (Fin d) → ℝ)
      (hfr : Integrable (fun x => f x*r x) volume)
      (hf2r : Integrable (fun x => (f x)^2*r x) volume) :
      (∫ x, f x*r x ∂volume)^2 ≤ ∫ x, (f x)^2*r x ∂volume := by
    let b := ∫ x, f x*r x ∂volume
    have hid (x : UnitAddTorus (Fin d)) : (f x-b)^2*r x =
      (f x)^2*r x-(2*b)*(f x*r x)+b^2*r x := by ring
    have hsub : Integrable (fun x => (f x)^2*r x-(2*b)*(f x*r x)) volume :=
      hf2r.sub (hfr.const_mul (2*b))
    have hvar : Integrable (fun x => (f x-b)^2*r x) volume := by
      simp_rw [hid]
      exact hsub.add (hri.const_mul (b^2))
    have hvnon : 0 ≤ ∫ x, (f x-b)^2*r x ∂volume :=
      integral_nonneg_of_ae (hrb.mono fun x hx => mul_nonneg (sq_nonneg _) hx.1)
    have heq : (∫ x, (f x-b)^2*r x ∂volume) =
        (∫ x, (f x)^2*r x ∂volume)-b^2 := by
      simp_rw [hid]
      rw [integral_add hsub (hri.const_mul _),
        integral_sub hf2r (hfr.const_mul (2*b)),integral_const_mul,integral_const_mul,hrmass]
      change (∫ x, (f x)^2*r x ∂volume)-(2*b)*b+b^2*1 = _
      ring
    rw [heq] at hvnon
    exact sub_nonneg.mp hvnon
  have hqint (x : UnitAddTorus (Fin d)) : Integrable (fun y => (g (x-y))^2*r y) volume :=
    (hg2i.comp_sub_left x).mul_bdd hr.aestronglyMeasurable hrnorm
  have hqbound (x : UnitAddTorus (Fin d)) : (∫ y, (g (x-y))^2*r y ∂volume) ≤ V := by
    calc
      _ ≤ ∫ y, M*(g (x-y))^2 ∂volume := by
        apply integral_mono_ae (hqint x) ((hg2i.comp_sub_left x).const_mul M)
        exact hrb.mono fun y hy => by nlinarith [sq_nonneg (g (x-y))]
      _ = V := by rw [integral_const_mul,integral_sub_left_eq_self
        (fun y : UnitAddTorus (Fin d) => (g y)^2) volume x]
  have hpot2 (x : UnitAddTorus (Fin d)) : (BackgroundPotential g r x)^2 ≤ V := by
    rw [hpot_integral]
    exact (square_mean (fun y => g (x-y)) (hpf x).1 (hqint x)).trans (hqbound x)
  have hpot2i : Integrable (fun x => (BackgroundPotential g r x)^2) volume := by
    refine Integrable.of_bound (hpm.pow_const 2).aestronglyMeasurable (H^2) ?_
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have hs := (sq_le_sq₀ (abs_nonneg _) hH).mpr (hpf x).2
      simpa only [sq_abs] using hs
  have hpot2ri : Integrable (fun x => (BackgroundPotential g r x)^2*r x) volume :=
    hpot2i.mul_bdd hr.aestronglyMeasurable hrnorm
  have hpot2mean : (∫ x, (BackgroundPotential g r x)^2*r x ∂volume) ≤ V := by
    calc
      _ ≤ ∫ x, V*r x ∂volume := integral_mono_ae hpot2ri (hri.const_mul V)
        (hrb.mono fun x hx => mul_le_mul_of_nonneg_right (hpot2 x) hx.1)
      _ = V := by rw [integral_const_mul,hrmass,mul_one]
  have hJ2 : (BackgroundPairMean g r)^2 ≤ V :=
    (square_mean (BackgroundPotential g r) hpri hpot2ri).trans hpot2mean
  refine ⟨hpot2,hJ2,?_⟩
  intro x
  have hfour (y : UnitAddTorus (Fin d)) : (CenteredKernel g r x y)^2 ≤
      4*((g (x-y))^2+(BackgroundPotential g r x)^2+
        (BackgroundPotential g r y)^2+(BackgroundPairMean g r)^2) := by
    unfold CenteredKernel
    nlinarith [sq_nonneg (g (x-y)+BackgroundPotential g r x),
      sq_nonneg (g (x-y)+BackgroundPotential g r y),
      sq_nonneg (g (x-y)-BackgroundPairMean g r),
      sq_nonneg (BackgroundPotential g r x-BackgroundPotential g r y),
      sq_nonneg (BackgroundPotential g r x+BackgroundPairMean g r),
      sq_nonneg (BackgroundPotential g r y+BackgroundPairMean g r)]
  let major := fun y : UnitAddTorus (Fin d) =>
    4*((g (x-y))^2*r y+(BackgroundPotential g r x)^2*r y+
      (BackgroundPotential g r y)^2*r y+(BackgroundPairMean g r)^2*r y)
  have hmajori : Integrable major volume :=
    (((hqint x).add (hri.const_mul ((BackgroundPotential g r x)^2))).add hpot2ri).add
      (hri.const_mul ((BackgroundPairMean g r)^2)) |>.const_mul 4
  have hpoint : ∀ᵐ y ∂(volume : Measure (UnitAddTorus (Fin d))),
      (CenteredKernel g r x y)^2*r y ≤ major y := by
    filter_upwards [hrb] with y hy
    have h := mul_le_mul_of_nonneg_right (hfour y) hy.1
    dsimp [major]
    nlinarith
  have hkm : Measurable (fun y : UnitAddTorus (Fin d) => CenteredKernel g r x y) :=
    hcm.comp (measurable_const.prodMk measurable_id)
  have hk2i : Integrable (fun y => (CenteredKernel g r x y)^2*r y) volume := by
    apply hmajori.mono' ((hkm.pow_const 2).mul hr).aestronglyMeasurable
    filter_upwards [hrb,hpoint] with y hy hp
    simpa only [Pi.mul_apply,Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (sq_nonneg _) hy.1)] using hp
  refine ⟨hk2i,?_⟩
  calc
    _ ≤ ∫ y, major y ∂volume := integral_mono_ae hk2i hmajori hpoint
    _ ≤ 16*V := by
      have hsum1 : Integrable (fun y => (g (x-y))^2*r y+(BackgroundPotential g r x)^2*r y) volume :=
        (hqint x).add (hri.const_mul _)
      have hsum2 : Integrable (fun y => (g (x-y))^2*r y+(BackgroundPotential g r x)^2*r y+
          (BackgroundPotential g r y)^2*r y) volume := hsum1.add hpot2ri
      dsimp [major]
      rw [integral_const_mul,integral_add hsum2 (hri.const_mul _),
        integral_add hsum1 hpot2ri,integral_add (hqint x) (hri.const_mul _),
        integral_const_mul,integral_const_mul,hrmass]
      nlinarith [hqbound x,hpot2 x,hpot2mean,hJ2]
