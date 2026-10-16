import Tablet.MayerConvolutionBounds
open MeasureTheory Filter Set UnitAddTorus
open scoped Topology ComplexConjugate
set_option maxHeartbeats 1600000

-- [TABLET NODE: PositiveFourierConvolution]
theorem PositiveFourierConvolution (d : ℕ) (K : UnitAddTorus (Fin d) → ℝ)
    (hKm : Measurable K)
    (hK : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), ‖K x‖ ≤ 1)
    (he : ∀ x, K (-x) = K x)
    (hF : ∀ k : Fin d → ℤ, 0 ≤ ∫ x, K x * (mFourier k x).re) :
    ∃! T : Lp ℝ 2 (volume : Measure (UnitAddTorus (Fin d))) →L[ℝ]
        Lp ℝ 2 (volume : Measure (UnitAddTorus (Fin d))),
      ‖T‖ ≤ 1 ∧
      (∀ v w, inner ℝ v (T w) = inner ℝ (T v) w) ∧
      (∀ v, 0 ≤ inner ℝ v (T v)) ∧
      (∀ (f : UnitAddTorus (Fin d) → ℝ) (hf : MemLp f 2 volume),
        MemLp (fun x => ∫ y, K (x-y) * f y) 2 volume ∧
        ⇑(T (hf.toLp f)) =ᵐ[volume] fun x => ∫ y, K (x-y) * f y) := by
-- BODY

  let conv {d : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (K : UnitAddTorus (Fin d) → ℝ) (f : UnitAddTorus (Fin d) → E) :
      UnitAddTorus (Fin d) → E := convolution K f (ContinuousLinearMap.lsmul ℝ ℝ) volume

  have conv_formula {d : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (K : UnitAddTorus (Fin d) → ℝ) (f : UnitAddTorus (Fin d) → E) (x) :
      conv K f x = ∫ y, K (x-y) • f y := by
    dsimp only [conv]
    rw [← convolution_flip]
    rfl

  have integral_norm_le {d : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (f : Lp E 2 (volume : Measure (UnitAddTorus (Fin d)))) :
      (∫ x, ‖f x‖) ≤ ‖f‖ := by
    letI : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
      ⟨by rw [AddCircle.volume_eq_smul_haarAddCircle]; simp⟩
    rw [integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable f),
      ← eLpNorm_one_eq_lintegral_enorm, Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
      (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) (Lp.aestronglyMeasurable f))

  have conv_point_integrable {d : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (K : UnitAddTorus (Fin d) → ℝ) (hKm : Measurable K)
      (hK : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), ‖K x‖ ≤ 1)
      (f : UnitAddTorus (Fin d) → E) (hfi : Integrable f volume) (x) :
      Integrable (fun y => K (x-y) • f y) volume := by
    have hKs : ∀ᵐ y ∂(volume : Measure (UnitAddTorus (Fin d))), ‖K (x-y)‖ ≤ 1 :=
      (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae hK
    exact hfi.smul_of_top_right
      (MemLp.of_bound (hKm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable 1 hKs)

  have conv_bound {d : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (K : UnitAddTorus (Fin d) → ℝ) (hKm : Measurable K)
      (hK : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), ‖K x‖ ≤ 1)
      (f : UnitAddTorus (Fin d) → E) (hfi : Integrable f volume) (x) :
      ‖conv K f x‖ ≤ ∫ y, ‖f y‖ := by
    rw [conv_formula]
    apply (norm_integral_le_integral_norm _).trans
    apply integral_mono_ae (conv_point_integrable K hKm hK f hfi x).norm hfi.norm
    have hKs := (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae hK
    filter_upwards [hKs] with y hy
    exact (norm_smul_le _ _).trans (by simpa using mul_le_mul_of_nonneg_right hy (norm_nonneg (f y)))

  have conv_memLp {d : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (K : UnitAddTorus (Fin d) → ℝ) (hKm : Measurable K)
      (hK : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), ‖K x‖ ≤ 1)
      (f : UnitAddTorus (Fin d) → E) (hf : MemLp f 2 volume) : MemLp (conv K f) 2 volume := by
    have hKi : Integrable K volume := Integrable.of_bound hKm.aestronglyMeasurable 1 hK
    have hfi := hf.integrable (by norm_num : (1 : ENNReal) ≤ 2)
    exact MemLp.of_bound (hKi.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hfi).aestronglyMeasurable
      (∫ y, ‖f y‖) (Eventually.of_forall fun x => conv_bound K hKm hK f hfi x)

  have conv_norm_le {d : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (K : UnitAddTorus (Fin d) → ℝ) (hKm : Measurable K)
      (hK : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), ‖K x‖ ≤ 1)
      (f : Lp E 2 (volume : Measure (UnitAddTorus (Fin d)))) :
      ‖(conv_memLp K hKm hK f (Lp.memLp f)).toLp (conv K f)‖ ≤ ‖f‖ := by
    letI : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
      ⟨by rw [AddCircle.volume_eq_smul_haarAddCircle]; simp⟩
    rw [Lp.norm_toLp]
    apply (ENNReal.toReal_mono (by simp) (eLpNorm_le_of_ae_bound
      (Eventually.of_forall fun x => (conv_bound K hKm hK f ((Lp.memLp f).integrable (by norm_num)) x).trans
        (integral_norm_le f)))).trans
    simp

  have conv_congr {d : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (K : UnitAddTorus (Fin d) → ℝ)
      {f g : UnitAddTorus (Fin d) → E} (hfg : f =ᵐ[volume] g) : conv K f = conv K g := by
    funext x
    rw [conv_formula, conv_formula]
    exact integral_congr_ae (hfg.mono fun y hy => by simpa only [hy])

  have conv_add {d : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (K : UnitAddTorus (Fin d) → ℝ) (hKm : Measurable K)
      (hK : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), ‖K x‖ ≤ 1)
      (f g : UnitAddTorus (Fin d) → E) (hf : Integrable f volume) (hg : Integrable g volume) :
      conv K (f+g) = conv K f + conv K g := by
    funext x
    simp only [conv_formula, Pi.add_apply, smul_add]
    exact integral_add (conv_point_integrable K hKm hK f hf x) (conv_point_integrable K hKm hK g hg x)

  have conv_smul {d : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (K : UnitAddTorus (Fin d) → ℝ) (a : ℝ) (f : UnitAddTorus (Fin d) → E) :
      conv K (a • f) = a • conv K f := by
    funext x
    simp only [conv_formula, Pi.smul_apply, smul_comm (K (x-_)) a]
    exact integral_smul a _

  let convLinear {d : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (K : UnitAddTorus (Fin d) → ℝ) (hKm : Measurable K)
      (hK : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), ‖K x‖ ≤ 1) :
      Lp E 2 (volume : Measure (UnitAddTorus (Fin d))) →ₗ[ℝ] Lp E 2 (volume : Measure (UnitAddTorus (Fin d))) := by
    refine { toFun := fun f => (conv_memLp K hKm hK f (Lp.memLp f)).toLp (conv K f), map_add' := ?_, map_smul' := ?_ }
    · intro f g
      apply Lp.ext
      have hc := conv_congr K (Lp.coeFn_add f g)
      have hadd := conv_add K hKm hK f g
        ((Lp.memLp f).integrable (by norm_num)) ((Lp.memLp g).integrable (by norm_num))
      filter_upwards [MemLp.coeFn_toLp (conv_memLp K hKm hK (f+g) (Lp.memLp (f+g))),
        Lp.coeFn_add ((conv_memLp K hKm hK f (Lp.memLp f)).toLp (conv K f))
          ((conv_memLp K hKm hK g (Lp.memLp g)).toLp (conv K g)),
        MemLp.coeFn_toLp (conv_memLp K hKm hK f (Lp.memLp f)),
        MemLp.coeFn_toLp (conv_memLp K hKm hK g (Lp.memLp g))] with x hx ha hf hg
      calc
        _ = conv K (↑↑(f+g)) x := hx
        _ = conv K f x + conv K g x := by rw [hc, hadd]; rfl
        _ = _ := by rw [ha]; simp only [Pi.add_apply, hf, hg]
    · intro a f
      apply Lp.ext
      have hc := conv_congr K (Lp.coeFn_smul a f)
      have hs := conv_smul K a f
      filter_upwards [MemLp.coeFn_toLp (conv_memLp K hKm hK (a • f) (Lp.memLp (a • f))),
        Lp.coeFn_smul a ((conv_memLp K hKm hK f (Lp.memLp f)).toLp (conv K f)),
        MemLp.coeFn_toLp (conv_memLp K hKm hK f (Lp.memLp f))] with x hx ha hf
      calc
        _ = conv K (↑↑(a • f)) x := hx
        _ = a • conv K f x := by rw [hc, hs]; rfl
        _ = _ := by simp only [RingHom.id_apply]; rw [ha]; simp only [Pi.smul_apply, hf]

  let convCLM {d : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (K : UnitAddTorus (Fin d) → ℝ) (hKm : Measurable K)
      (hK : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), ‖K x‖ ≤ 1) :
      Lp E 2 (volume : Measure (UnitAddTorus (Fin d))) →L[ℝ] Lp E 2 (volume : Measure (UnitAddTorus (Fin d))) :=
    (convLinear K hKm hK).mkContinuous 1 (by
      intro f
      change ‖(conv_memLp K hKm hK f (Lp.memLp f)).toLp (conv K f)‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using conv_norm_le K hKm hK f)

  have convCLM_formula {d : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (K : UnitAddTorus (Fin d) → ℝ) (hKm : Measurable K)
      (hK : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), ‖K x‖ ≤ 1)
      (f : UnitAddTorus (Fin d) → E) (hf : MemLp f 2 volume) :
      ⇑(convCLM K hKm hK (hf.toLp f)) =ᵐ[volume] conv K f := by
    have h := MemLp.coeFn_toLp (conv_memLp K hKm hK (hf.toLp f) (Lp.memLp (hf.toLp f)))
    have hc := conv_congr K (MemLp.coeFn_toLp hf)
    exact h.trans (Eventually.of_forall fun x => congrFun hc x)

  have volume_eq_haar (d : ℕ) : (volume : Measure (UnitAddTorus (Fin d))) =
      Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle) := by
    change Measure.pi _ = _
    congr 1
    funext i
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp

  have char_add {d : ℕ} (k : Fin d → ℤ) (x y : UnitAddTorus (Fin d)) :
      mFourier k (x+y) = mFourier k x * mFourier k y := by
    simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply, smul_add,
      AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

  have char_inv {d : ℕ} (k : Fin d → ℤ) (x : UnitAddTorus (Fin d)) :
      mFourier k (-x) = conj (mFourier k x) := by
    simp only [mFourier, ContinuousMap.coe_mk, Pi.neg_apply, fourier_apply, smul_neg,
      fourier_neg', map_prod]

  have char_norm {d : ℕ} (k : Fin d → ℤ) (x : UnitAddTorus (Fin d)) : ‖mFourier k x‖ = 1 := by
    simp only [mFourier, ContinuousMap.coe_mk, norm_prod, fourier_apply, Circle.norm_coe,
      Finset.prod_const_one]

  let coef {d : ℕ} (f : UnitAddTorus (Fin d) → ℂ) (k : Fin d → ℤ) :=
    ∫ x, mFourier (-k) x * f x

  have coef_integrable {d : ℕ} (f : UnitAddTorus (Fin d) → ℂ) (hi : Integrable f volume) (k : Fin d → ℤ) :
      Integrable (fun x => mFourier (-k) x * f x) volume := by
    exact hi.bdd_mul (mFourier (-k)).continuous.measurable.aestronglyMeasurable
      (Eventually.of_forall fun x => (char_norm (-k) x).le)

  have coef_eq {d : ℕ} (f : UnitAddTorus (Fin d) → ℂ) (k : Fin d → ℤ) : coef f k = mFourierCoeff f k := by
    unfold coef mFourierCoeff
    simp only [smul_eq_mul]
    change (∫ x, mFourier (-k) x * f x ∂(volume : Measure (UnitAddTorus (Fin d)))) =
      ∫ x, mFourier (-k) x * f x ∂Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle)
    rw [volume_eq_haar]

  have coef_congr {d : ℕ} {f g : UnitAddTorus (Fin d) → ℂ} (h : f =ᵐ[volume] g) (k : Fin d → ℤ) :
      coef f k = coef g k := by
    exact integral_congr_ae (h.mono fun x hx => by simp only [hx])

  have coef_conv {d : ℕ} (K : UnitAddTorus (Fin d) → ℝ) (hKm : Measurable K)
      (hK : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), ‖K x‖ ≤ 1)
      (f : UnitAddTorus (Fin d) → ℂ) (hfi : Integrable f volume) (k : Fin d → ℤ) :
      coef (conv K f) k = coef (fun x => (K x : ℂ)) k * coef f k := by
    have hKi : Integrable K volume := Integrable.of_bound hKm.aestronglyMeasurable 1 hK
    have hci : Integrable (fun v : UnitAddTorus (Fin d) × UnitAddTorus (Fin d) =>
        (mFourier (-k) v.1) * (K v.2 • f (v.1-v.2))) (volume.prod volume) :=
      (hKi.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hfi).bdd_mul
        ((mFourier (-k)).continuous.measurable.comp measurable_fst).aestronglyMeasurable
        (Eventually.of_forall fun v => (char_norm (-k) v.1).le)
    have htrans (y : UnitAddTorus (Fin d)) :
        (∫ x, mFourier (-k) x * (K y • f (x-y))) =
          mFourier (-k) y * (K y : ℂ) * coef f k := by
      calc
        _ = ∫ z, mFourier (-k) (z+y) * (K y • f ((z+y)-y)) :=
          (integral_add_right_eq_self _ y).symm
        _ = ∫ z, (mFourier (-k) y * (K y : ℂ)) * (mFourier (-k) z * f z) := by
          apply integral_congr_ae
          exact Eventually.of_forall fun z => by
            dsimp only
            rw [char_add, add_sub_cancel_right]
            simp only [Complex.real_smul]
            ring
        _ = _ := integral_const_mul _ _
    change (∫ x, mFourier (-k) x * conv K f x) = _
    calc
      _ = ∫ x, ∫ y, mFourier (-k) x * (K y • f (x-y)) := by
        congr 1
        funext x
        change mFourier (-k) x * (∫ y, K y • f (x-y)) = _
        exact (integral_const_mul _ _).symm
      _ = ∫ y, ∫ x, mFourier (-k) x * (K y • f (x-y)) := integral_integral_swap hci
      _ = ∫ y, (mFourier (-k) y * (K y : ℂ)) * coef f k := by
        congr 1
        funext y
        exact htrans y
      _ = _ := integral_mul_const _ _

  have coef_real {d : ℕ} (K : UnitAddTorus (Fin d) → ℝ) (hi : Integrable K volume)
      (he : ∀ x, K (-x) = K x) (k : Fin d → ℤ) :
      coef (fun x => (K x : ℂ)) k = (∫ x, K x * (mFourier (-k) x).re : ℝ) := by
    have hic : Integrable (fun x => (K x : ℂ)) volume := Complex.ofRealCLM.integrable_comp hi
    have hreal : conj (coef (fun x => (K x : ℂ)) k) = coef (fun x => (K x : ℂ)) k := by
      unfold coef
      rw [← integral_conj]
      calc
        _ = ∫ x, mFourier (-k) (-x) * (K (-x) : ℂ) := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by dsimp; simp only [map_mul, char_inv, he, Complex.conj_ofReal]
        _ = _ := integral_neg_eq_self (fun x => mFourier (-k) x * (K x : ℂ)) volume
    have hre : (coef (fun x => (K x : ℂ)) k).re = ∫ x, K x * (mFourier (-k) x).re := by
      unfold coef
      change RCLike.re (∫ x, mFourier (-k) x * (K x : ℂ)) = _
      rw [← integral_re (coef_integrable _ hic k)]
      congr 1
      funext x
      change (mFourier (-k) x * (K x : ℂ)).re = K x * (mFourier (-k) x).re
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      ring
    apply Complex.ext
    · simpa using hre
    · simpa using Complex.conj_eq_iff_im.mp hreal

  have norm_sq_integral {d : ℕ} (f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d)))) :
      (∫ x, ‖f x‖ ^ 2) = ‖f‖ ^ 2 := by
    have hi := congrArg Complex.re (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) f)
    rw [L2.inner_def] at hi
    have hri := integral_re (L2.integrable_inner (𝕜 := ℂ) f f)
    change (∫ x, RCLike.re (inner ℂ (f x) (f x))) = _ at hri
    change RCLike.re (∫ x, inner ℂ (f x) (f x)) = RCLike.re ((‖f‖ : ℂ) ^ 2) at hi
    rw [← hri] at hi
    simp only [inner_self_eq_norm_sq_to_K] at hi
    change (∫ x, (((‖f x‖ : ℂ) ^ 2).re)) = ((‖f‖ : ℂ) ^ 2).re at hi
    simpa only [← Complex.ofReal_pow, Complex.ofReal_re] using hi

  have square_sum_function {d : ℕ} (f : UnitAddTorus (Fin d) → ℂ) (hf : MemLp f 2 volume) :
      HasSum (fun k => ‖coef f k‖ ^ 2) (∫ x, ‖f x‖ ^ 2) := by
    let mh : Measure (UnitAddTorus (Fin d)) := Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle)
    have hfh : MemLp f 2 mh := by dsimp [mh]; rw [← volume_eq_haar]; exact hf
    let fh := hfh.toLp f
    have heq := MemLp.coeFn_toLp hfh
    have hs := hasSum_sq_mFourierCoeff fh
    have hc (k : Fin d → ℤ) : mFourierCoeff fh k = coef f k := by
      rw [coef_eq]
      unfold mFourierCoeff
      exact integral_congr_ae (heq.mono fun x hx => by simp only [fh, hx])
    simp_rw [hc] at hs
    convert hs using 1
    dsimp only [mh] at heq
    rw [volume_eq_haar]
    exact integral_congr_ae (heq.symm.mono fun x hx => by simp only [fh, hx])

  have square_sum {d : ℕ} (f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d)))) :
      HasSum (fun k => ‖coef f k‖ ^ 2) (‖f‖ ^ 2) := by
    rw [← norm_sq_integral]
    exact square_sum_function f (Lp.memLp f)

  have pairing_sum_function {d : ℕ} (f g : UnitAddTorus (Fin d) → ℂ) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
      HasSum (fun k => conj (coef f k) * coef g k) (∫ x, conj (f x) * g x) := by
    let mh : Measure (UnitAddTorus (Fin d)) := Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle)
    have hfh : MemLp f 2 mh := by dsimp [mh]; rw [← volume_eq_haar]; exact hf
    have hgh : MemLp g 2 mh := by dsimp [mh]; rw [← volume_eq_haar]; exact hg
    let fh := hfh.toLp f
    let gh := hgh.toLp g
    have hfq := MemLp.coeFn_toLp hfh
    have hgq := MemLp.coeFn_toLp hgh
    have hs := hasSum_prod_mFourierCoeff fh gh
    have hc (k : Fin d → ℤ) : mFourierCoeff fh k = coef f k := by
      rw [coef_eq]
      unfold mFourierCoeff
      exact integral_congr_ae (hfq.mono fun x hx => by simp only [fh, gh, hx])
    have hd (k : Fin d → ℤ) : mFourierCoeff gh k = coef g k := by
      rw [coef_eq]
      unfold mFourierCoeff
      exact integral_congr_ae (hgq.mono fun x hx => by simp only [fh, gh, hx])
    simp_rw [hc, hd] at hs
    convert hs using 1
    rw [volume_eq_haar]
    apply integral_congr_ae
    filter_upwards [hfq, hgq] with x hx hy
    simp only [fh, gh, hx, hy]

  have pairing_sum {d : ℕ} (f g : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d)))) :
      HasSum (fun k => conj (coef f k) * coef g k) (∫ x, conj (f x) * g x) :=
    pairing_sum_function f g (Lp.memLp f) (Lp.memLp g)

  have clm_coef {d : ℕ} (K : UnitAddTorus (Fin d) → ℝ) (hKm : Measurable K)
      (hK : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), ‖K x‖ ≤ 1)
      (f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d)))) (k : Fin d → ℤ) :
      coef (convCLM K hKm hK f) k = coef (fun x => (K x : ℂ)) k * coef f k := by
    change coef (↑↑((conv_memLp K hKm hK f (Lp.memLp f)).toLp (conv K f))) k = _
    rw [coef_congr (MemLp.coeFn_toLp (conv_memLp K hKm hK f (Lp.memLp f))) k]
    exact coef_conv K hKm hK f ((Lp.memLp f).integrable (by norm_num)) k

  have spectral_lower {d : ℕ} (K : UnitAddTorus (Fin d) → ℝ) (hKm : Measurable K)
      (hK : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), ‖K x‖ ≤ 1)
      (R : ℝ) (hcoef : ∀ k : Fin d → ℤ,
        (coef (fun x => (K x : ℂ)) k).im = 0 ∧ -R ≤ (coef (fun x => (K x : ℂ)) k).re)
      (f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d)))) :
      -R * ‖f‖ ^ 2 ≤ (∫ x, conj (f x) * convCLM K hKm hK f x).re := by
    have hlo := (square_sum f).mul_left (-R)
    have hhi := RCLike.hasSum_re ℂ (pairing_sum f (convCLM K hKm hK f))
    apply hasSum_le _ hlo hhi
    intro k
    rw [clm_coef K hKm hK f k]
    let z := coef (fun x => (K x : ℂ)) k
    have hz : z = (z.re : ℂ) := by apply Complex.ext <;> simp [z, (hcoef k).1]
    change -R * ‖coef f k‖ ^ 2 ≤ (conj (coef f k) * (z * coef f k)).re
    rw [hz]
    have hid : conj (coef f k) * ((z.re : ℂ) * coef f k) = (z.re : ℂ) * (‖coef f k‖ ^ 2 : ℝ) := by
      rw [mul_left_comm, mul_comm (conj (coef f k)), Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hid]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_le_mul_of_nonneg_right (hcoef k).2 (sq_nonneg _)

  let complexify {d : ℕ} (f : Lp ℝ 2 (volume : Measure (UnitAddTorus (Fin d)))) :
      Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d))) := Complex.ofRealCLM.compLp f

  have complexify_ae {d : ℕ} (f : Lp ℝ 2 (volume : Measure (UnitAddTorus (Fin d)))) :
      ⇑(complexify f) =ᵐ[volume] fun x => (f x : ℂ) := Complex.ofRealCLM.coeFn_compLp f

  have complexify_norm {d : ℕ} (f : Lp ℝ 2 (volume : Measure (UnitAddTorus (Fin d)))) :
      ‖complexify f‖ = ‖f‖ := by
    rw [Lp.norm_def, Lp.norm_def]
    congr 1
    apply eLpNorm_congr_norm_ae
    exact (complexify_ae f).mono fun x hx => by rw [hx, Complex.norm_real]

  have conv_ofReal {d : ℕ} (K : UnitAddTorus (Fin d) → ℝ) (hKm : Measurable K)
      (hK : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), ‖K x‖ ≤ 1)
      (f : UnitAddTorus (Fin d) → ℝ) (hf : Integrable f volume) :
      conv K (fun x => (f x : ℂ)) = fun x => (conv (E := ℝ) K f x : ℂ) := by
    funext x
    rw [conv_formula, conv_formula]
    simpa only [Complex.ofRealCLM_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul] using
      Complex.ofRealCLM.integral_comp_comm (conv_point_integrable K hKm hK f hf x)

  have complexify_conv {d : ℕ} (K : UnitAddTorus (Fin d) → ℝ) (hKm : Measurable K)
      (hK : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), ‖K x‖ ≤ 1)
      (f : Lp ℝ 2 (volume : Measure (UnitAddTorus (Fin d)))) :
      complexify (convCLM K hKm hK f) = convCLM K hKm hK (complexify f) := by
    apply Lp.ext
    have hc := conv_congr K (complexify_ae f)
    have ho := conv_ofReal K hKm hK f ((Lp.memLp f).integrable (by norm_num))
    filter_upwards [complexify_ae (convCLM K hKm hK f),
      MemLp.coeFn_toLp (conv_memLp K hKm hK f (Lp.memLp f)),
      MemLp.coeFn_toLp (conv_memLp K hKm hK (complexify f) (Lp.memLp (complexify f)))] with x hx hy hz
    change (complexify (convCLM K hKm hK f)) x = _
    rw [hx]
    change ((conv_memLp K hKm hK f (Lp.memLp f)).toLp (conv K f) x : ℂ) = _
    rw [hy]
    change _ = (conv_memLp K hKm hK (complexify f) (Lp.memLp (complexify f))).toLp (conv K (complexify f)) x
    rw [hz, hc, ho]

  have real_pairing {d : ℕ} (f g : Lp ℝ 2 (volume : Measure (UnitAddTorus (Fin d)))) :
      inner ℝ f g = (∫ x, conj (complexify f x) * complexify g x).re := by
    rw [L2.inner_def]
    have hi : Integrable (fun x => conj (complexify f x) * complexify g x) volume := by
      simpa only [RCLike.inner_apply, RCLike.star_def, mul_comm] using
        L2.integrable_inner (𝕜 := ℂ) (complexify f) (complexify g)
    have hre := integral_re hi
    change (∫ x, (conj (complexify f x) * complexify g x).re) =
      (∫ x, conj (complexify f x) * complexify g x).re at hre
    rw [← hre]
    apply integral_congr_ae
    filter_upwards [complexify_ae f, complexify_ae g] with x hx hy
    rw [hx, hy]
    simp only [Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    simp [RCLike.inner_apply, mul_comm]

  have spectral_symmetric {d : ℕ} (K : UnitAddTorus (Fin d) → ℝ) (hKm : Measurable K)
      (hK : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), ‖K x‖ ≤ 1)
      (hcoef : ∀ k : Fin d → ℤ, (coef (fun x => (K x : ℂ)) k).im = 0)
      (f g : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d)))) :
      (∫ x, conj (f x) * convCLM K hKm hK g x).re =
        (∫ x, conj (g x) * convCLM K hKm hK f x).re := by
    have hf := RCLike.hasSum_re ℂ (pairing_sum f (convCLM K hKm hK g))
    have hg := RCLike.hasSum_re ℂ (pairing_sum g (convCLM K hKm hK f))
    have hc : (fun k => RCLike.re (conj (coef f k) * coef (convCLM K hKm hK g) k)) =
        (fun k => RCLike.re (conj (coef g k) * coef (convCLM K hKm hK f) k)) := by
      funext k
      rw [clm_coef K hKm hK g k, clm_coef K hKm hK f k]
      change (conj (coef f k) * (coef (fun x => (K x : ℂ)) k * coef g k)).re =
        (conj (coef g k) * (coef (fun x => (K x : ℂ)) k * coef f k)).re
      simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, hcoef k,
        zero_mul, mul_zero, sub_zero, zero_add]
      ring
    change RCLike.re (∫ x, conj (f x) * convCLM K hKm hK g x) =
      RCLike.re (∫ x, conj (g x) * convCLM K hKm hK f x)
    exact (hc ▸ hf).unique hg
  classical
  have hKi : Integrable K volume := Integrable.of_bound hKm.aestronglyMeasurable 1 hK
  let T := convCLM (E := ℝ) K hKm hK
  have hcoef (k : Fin d → ℤ) :
      (coef (fun x => (K x : ℂ)) k).im = 0 ∧ 0 ≤ (coef (fun x => (K x : ℂ)) k).re := by
    rw [coef_real K hKi he k]
    simp only [Complex.ofReal_im, Complex.ofReal_re]
    exact ⟨trivial, hF (-k)⟩
  have hnorm : ‖T‖ ≤ 1 := T.opNorm_le_bound zero_le_one fun v => by
    change ‖(conv_memLp K hKm hK v (Lp.memLp v)).toLp (conv K v)‖ ≤ 1 * ‖v‖
    simpa only [one_mul] using conv_norm_le K hKm hK v
  have hself (v w : Lp ℝ 2 (volume : Measure (UnitAddTorus (Fin d)))) :
      inner ℝ v (T w) = inner ℝ (T v) w := by
    rw [← real_inner_comm (T v) w, real_pairing, real_pairing,
      complexify_conv K hKm hK w, complexify_conv K hKm hK v]
    exact spectral_symmetric K hKm hK (fun k => (hcoef k).1) _ _
  have hpos (v : Lp ℝ 2 (volume : Measure (UnitAddTorus (Fin d)))) :
      0 ≤ inner ℝ v (T v) := by
    rw [real_pairing, complexify_conv K hKm hK v]
    simpa using spectral_lower K hKm hK 0 (fun k => by simpa using hcoef k) (complexify v)
  have hrep (f : UnitAddTorus (Fin d) → ℝ) (hf : MemLp f 2 volume) :
      MemLp (fun x => ∫ y, K (x-y) * f y) 2 volume ∧
      ⇑(T (hf.toLp f)) =ᵐ[volume] fun x => ∫ y, K (x-y) * f y := by
    have heq : conv K f = fun x => ∫ y, K (x-y) * f y := by
      funext x
      simpa only [smul_eq_mul] using conv_formula K f x
    rw [← heq]
    exact ⟨conv_memLp K hKm hK f hf, convCLM_formula K hKm hK f hf⟩
  refine ⟨T, ⟨hnorm, hself, hpos, hrep⟩, ?_⟩
  intro S hS
  apply ContinuousLinearMap.ext
  intro v
  have hf := Lp.memLp v
  have hSv := (hS.2.2.2 v hf).2
  have hTv := (hrep v hf).2
  rw [Lp.toLp_coeFn v hf] at hSv hTv
  exact Lp.ext (hSv.trans hTv.symm)
