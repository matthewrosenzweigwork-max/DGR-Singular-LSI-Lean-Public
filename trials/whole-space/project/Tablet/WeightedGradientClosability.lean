module

public import Tablet.WeightedLocalRestriction
public import Tablet.EuclideanDerivativeCoordinates
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section
open MeasureTheory Filter Set
open scoped Topology ContDiff

-- [TABLET NODE: WeightedGradientClosability]
theorem WeightedGradientClosability {ι : Type*} [Fintype ι]
    (r : EuclideanSpace ℝ ι → ℝ) (U : Set (EuclideanSpace ℝ ι)) (hU : IsOpen U)
    (hfull : ∀ᵐ x ∂(volume.withDensity (fun y => ENNReal.ofReal (r y))), x ∈ U)
    (hlocal : ∀ K : Set (EuclideanSpace ℝ ι), IsCompact K → K ⊆ U →
      ∃ m : ℝ, 0 < m ∧ ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)), x ∈ K → m ≤ r x)
    (g : ℕ → EuclideanSpace ℝ ι → ℝ) (hgs : ∀ n, ContDiff ℝ ∞ (g n))
    (hg : ∀ n, MemLp (g n) 2 (volume.withDensity (fun x => ENNReal.ofReal (r x))))
    (hD : ∀ n, MemLp (EuclideanGradient (g n)) 2
      (volume.withDensity (fun x => ENNReal.ofReal (r x))))
    (v : Lp (EuclideanSpace ℝ ι) 2 (volume.withDensity (fun x => ENNReal.ofReal (r x))))
    (hzero : Tendsto (fun n => (hg n).toLp (g n)) atTop (𝓝 0))
    (hv : Tendsto (fun n => (hD n).toLp (EuclideanGradient (g n))) atTop (𝓝 v)) : v = 0 := by
-- BODY
  have lpTestIntegral_tendsto (P : Measure (EuclideanSpace ℝ ι))
      (f : ℕ → Lp ℝ 2 P) (g : Lp ℝ 2 P) (hf : Tendsto f atTop (𝓝 g))
      (φ : EuclideanSpace ℝ ι → ℝ) (hφ : MemLp φ 2 P) :
      Tendsto (fun n => ∫ x, φ x * f n x ∂P) atTop (𝓝 (∫ x, φ x * g x ∂P)) := by
    have he (v : Lp ℝ 2 P) : inner ℝ (hφ.toLp φ) v = ∫ x, φ x * v x ∂P := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hφ.coeFn_toLp] with x hx
      rw [hx]
      simp only [Real.inner_apply]
    have hc : Continuous (fun v : Lp ℝ 2 P => inner ℝ (hφ.toLp φ) v) :=
      continuous_const.inner continuous_id
    simpa only [Function.comp_def, he] using hc.continuousAt.tendsto.comp hf
  have weightedGradient_testZero
      (r : EuclideanSpace ℝ ι → ℝ) (U : Set (EuclideanSpace ℝ ι))
      (hlocal : ∀ K : Set (EuclideanSpace ℝ ι), IsCompact K → K ⊆ U →
        ∃ m : ℝ, 0 < m ∧ ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)), x ∈ K → m ≤ r x)
      (g : ℕ → EuclideanSpace ℝ ι → ℝ) (hgs : ∀ n, ContDiff ℝ ∞ (g n))
      (hg : ∀ n, MemLp (g n) 2 (volume.withDensity (fun x => ENNReal.ofReal (r x))))
      (hD : ∀ n, MemLp (EuclideanGradient (g n)) 2
        (volume.withDensity (fun x => ENNReal.ofReal (r x))))
      (v : Lp (EuclideanSpace ℝ ι) 2 (volume.withDensity (fun x => ENNReal.ofReal (r x))))
      (hzero : Tendsto (fun n => (hg n).toLp (g n)) atTop (𝓝 0))
      (hv : Tendsto (fun n => (hD n).toLp (EuclideanGradient (g n))) atTop (𝓝 v))
      (φ : EuclideanSpace ℝ ι → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφs : HasCompactSupport φ)
      (hφU : tsupport φ ⊆ U) (k : ι) : (∫ x, φ x * (v x) k) = 0 := by
    let K := tsupport φ
    let μ : Measure (EuclideanSpace ℝ ι) := volume.restrict K
    have hK : IsCompact K := hφs
    let := (show IsFiniteMeasure μ from ⟨by simpa [μ] using hK.measure_lt_top⟩)
    obtain ⟨m,hm,hmb⟩ := hlocal K hK hφU
    obtain ⟨hAC,Ts,hTs⟩ := WeightedLocalRestriction (E := ℝ) volume r K hK.measurableSet m hm hmb
    obtain ⟨_,Tv,hTv⟩ := WeightedLocalRestriction (E := EuclideanSpace ℝ ι) volume r K hK.measurableSet m hm hmb
    let F := fun n => (hg n).toLp (g n)
    let D := fun n => (hD n).toLp (EuclideanGradient (g n))
    let π : EuclideanSpace ℝ ι →L[ℝ] ℝ := PiLp.proj 2 (fun _ : ι => ℝ) k
    let R := π.compLpL 2 μ
    let ψ := fun x => fderiv ℝ φ x (EuclideanSpace.basisFun ι ℝ k)
    have hψc : Continuous ψ := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hψs : HasCompactSupport ψ := hφs.fderiv_apply ℝ _
    have htest (f : EuclideanSpace ℝ ι → ℝ) (hf : Continuous f) (hfs : HasCompactSupport f) : MemLp f 2 μ := by
      obtain ⟨C,hC⟩ := hfs.exists_bound_of_continuous hf
      exact MemLp.of_bound hf.aestronglyMeasurable C (Eventually.of_forall hC)
    have hφlp := htest φ hφ.continuous hφs
    have hψlp := htest ψ hψc hψs
    have hscoef (n : ℕ) : (Ts (F n) : _ → ℝ) =ᵐ[μ] (g n) :=
      (hTs _).trans (hAC.ae_eq (hg n).coeFn_toLp)
    have hdcoef (n : ℕ) : (R (Tv (D n)) : _ → ℝ) =ᵐ[μ]
        (fun x => fderiv ℝ (g n) x (EuclideanSpace.basisFun ι ℝ k)) := by
      filter_upwards [π.coeFn_compLpL (Tv (D n)), hTv (D n), hAC.ae_eq (hD n).coeFn_toLp] with x hx hxt hraw
      dsimp only [R] at hx ⊢
      rw [hx,hxt]
      dsimp only [D]
      rw [hraw, (EuclideanDerivativeCoordinates (g n) x).1]
      rfl
    have hvcoef : (R (Tv v) : _ → ℝ) =ᵐ[μ] (fun x => (v x) k) := by
      filter_upwards [π.coeFn_compLpL (Tv v), hTv v] with x hx hxt
      dsimp only [R] at hx ⊢
      rw [hx,hxt]
      rfl
    have hsconv : Tendsto (fun n => ∫ x, ψ x * g n x ∂μ) atTop (𝓝 (0:ℝ)) := by
      have ht := lpTestIntegral_tendsto μ (fun n => Ts (F n)) 0
        (by simpa only [F,μ,Function.comp_def,map_zero] using Ts.continuous.continuousAt.tendsto.comp hzero) ψ hψlp
      have hzint : (∫ x, ψ x * (0 : Lp ℝ 2 μ) x ∂μ) = 0 := by
        calc
          _ = ∫ _, (0:ℝ) ∂μ := integral_congr_ae ((Lp.coeFn_zero ℝ 2 μ).mono fun x hx => by rw [hx]; simp)
          _ = 0 := by simp
      rw [hzint] at ht
      apply ht.congr'
      exact Eventually.of_forall (fun n => integral_congr_ae ((hscoef n).mono fun x hx => by dsimp only; rw [hx]))
    have hdconv : Tendsto (fun n => ∫ x, φ x * fderiv ℝ (g n) x (EuclideanSpace.basisFun ι ℝ k) ∂μ)
        atTop (𝓝 (∫ x, φ x * (v x) k ∂μ)) := by
      have ht := lpTestIntegral_tendsto μ (fun n => R (Tv (D n))) (R (Tv v))
        ((R.continuous.comp Tv.continuous).continuousAt.tendsto.comp hv) φ hφlp
      have heq : (∫ x, φ x * (R (Tv v)) x ∂μ) = (∫ x, φ x * (v x) k ∂μ) :=
        integral_congr_ae (hvcoef.mono fun x hx => by dsimp only; rw [hx])
      rw [heq] at ht
      apply ht.congr'
      exact Eventually.of_forall (fun n => integral_congr_ae ((hdcoef n).mono fun x hx => by dsimp only; rw [hx]))
    have hibp (n : ℕ) : (∫ x, φ x * fderiv ℝ (g n) x (EuclideanSpace.basisFun ι ℝ k) ∂μ) =
        -(∫ x, ψ x * g n x ∂μ) := by
      have hdc : Continuous (fun x => fderiv ℝ (g n) x (EuclideanSpace.basisFun ι ℝ k)) :=
        ((hgs n).continuous_fderiv (by simp)).clm_apply continuous_const
      have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (μ := (volume : Measure (EuclideanSpace ℝ ι)))
        (f := g n) (g := φ) (v := EuclideanSpace.basisFun ι ℝ k)
        ((hdc.mul hφ.continuous).integrable_of_hasCompactSupport hφs.mul_left)
        (((hgs n).continuous.mul hψc).integrable_of_hasCompactSupport hψs.mul_left)
        (((hgs n).continuous.mul hφ.continuous).integrable_of_hasCompactSupport hφs.mul_left)
        (fun _ _ => (hgs n).differentiable (by simp) _)
        (fun _ _ => hφ.differentiable (by simp) _)
      have hsi : (∫ x, ψ x * g n x ∂μ) = ∫ x, g n x * ψ x := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
        · simp_rw [mul_comm]
        · intro x hx
          change x ∉ tsupport φ at hx
          simp [ψ, fderiv_of_notMem_tsupport ℝ hx]
      have hdi : (∫ x, φ x * fderiv ℝ (g n) x (EuclideanSpace.basisFun ι ℝ k) ∂μ) =
          ∫ x, fderiv ℝ (g n) x (EuclideanSpace.basisFun ι ℝ k) * φ x := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
        · simp_rw [mul_comm]
        · intro x hx
          have hz : φ x = 0 := by
            by_contra hz
            exact hx ((subset_tsupport φ) hz)
          rw [hz,zero_mul]
      rw [hsi,hdi]
      dsimp only [ψ]
      linarith
    have hlim0 : Tendsto (fun n => ∫ x, φ x * fderiv ℝ (g n) x (EuclideanSpace.basisFun ι ℝ k) ∂μ)
        atTop (𝓝 (0:ℝ)) := by simpa only [hibp,neg_zero] using hsconv.neg
    have hresult := tendsto_nhds_unique hdconv hlim0
    have hout (x : EuclideanSpace ℝ ι) (hx : x ∉ K) : φ x * (v x) k = 0 := by
      have hz : φ x = 0 := by
        by_contra hz
        exact hx ((subset_tsupport φ) hz)
      rw [hz,zero_mul]
    calc
      _ = ∫ x, φ x * (v x) k ∂μ := (setIntegral_eq_integral_of_forall_compl_eq_zero hout).symm
      _ = 0 := hresult
  have hpart (k : ι) : ∀ᵐ x : EuclideanSpace ℝ ι ∂volume, x ∈ U → (v x) k = 0 := by
    have hli : LocallyIntegrableOn (fun x => (v x) k) U volume := by
      rw [locallyIntegrableOn_iff hU.isLocallyClosed]
      intro K hKU hK
      let μ : Measure (EuclideanSpace ℝ ι) := volume.restrict K
      let := (show IsFiniteMeasure μ from ⟨by simpa [μ] using hK.measure_lt_top⟩)
      obtain ⟨m,hm,hmb⟩ := hlocal K hK hKU
      obtain ⟨_,T,hT⟩ := WeightedLocalRestriction (E := EuclideanSpace ℝ ι) volume r K hK.measurableSet m hm hmb
      let π : EuclideanSpace ℝ ι →L[ℝ] ℝ := PiLp.proj 2 (fun _ : ι => ℝ) k
      have he : (π.compLp (T v) : _ → ℝ) =ᵐ[μ] (fun x => (v x) k) := by
        filter_upwards [π.coeFn_compLp (T v), hT v] with x hx hxt
        rw [hx,hxt]
        rfl
      exact ((Lp.memLp (π.compLp (T v))).integrable (by norm_num)).congr he
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hli
    intro φ hφ hφs hφU
    simpa only [smul_eq_mul] using weightedGradient_testZero r U hlocal g hgs hg hD v hzero hv φ hφ hφs hφU k
  have hparts : ∀ᵐ x : EuclideanSpace ℝ ι ∂volume, ∀ k, x ∈ U → (v x) k = 0 := ae_all_iff.2 hpart
  have hzeroU : ∀ᵐ x : EuclideanSpace ℝ ι ∂volume, x ∈ U → v x = 0 := by
    filter_upwards [hparts] with x hx
    intro hX
    ext k
    exact hx k hX
  have hAC : volume.withDensity (fun x => ENNReal.ofReal (r x)) ≪ (volume : Measure (EuclideanSpace ℝ ι)) :=
    withDensity_absolutelyContinuous _ _
  have hzeroP : ∀ᵐ x ∂(volume.withDensity (fun y => ENNReal.ofReal (r y))), v x = 0 := by
    filter_upwards [hzeroU.filter_mono hAC.ae_le,hfull] with x hx hX
    exact hx hX
  exact Lp.eq_zero_iff_ae_eq_zero.mpr hzeroP
