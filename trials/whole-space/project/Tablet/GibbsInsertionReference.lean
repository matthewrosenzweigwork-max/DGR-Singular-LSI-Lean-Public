module

public import Tablet.ReferenceOffsetDensity
public import Tablet.ParticlePosition
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Tactic

@[expose] public section
open MeasureTheory Filter Set
open scoped ENNReal
set_option maxHeartbeats 1500000

-- [TABLET NODE: GibbsInsertionReference]
theorem GibbsInsertionReference (d : ℕ) (hd : 3 ≤ d) (s B κ L M1 : ℝ)
    (hs : 0 < s) (hsd : s ≤ (d : ℝ) - 2) (_hB : 0 ≤ B)
    (hκ : 0 < κ) (hL : 1 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V b : OneParticle d → ℝ), Continuous V →
      BoundedMultiplier d L b →
      (∀ x, κ / 2 * ‖x‖ ^ 2 ≤ V x - V 0) →
      (∀ x, ‖x‖ ≤ 1 → V x - V 0 ≤ M1) →
    ∀ N : ℕ, 2 ≤ N → ∀ coupling ε : ℝ, 0 ≤ coupling → coupling ≤ B → 0 < ε →
    ∀ (X : ParticleConfig d N) (i : Fin N),
      let a := coupling / (N : ℝ)
      let U := fun z => ∑ j ∈ Finset.univ.erase i,
        a * RieszKernel s ε (z - ParticlePosition X j)
      let μ := ReferenceLaw V b
      let Z := ∫ z, Real.exp (-U z) ∂μ
      let W := fun z => V z + U z
      0 ≤ a * (N - 1 : ℕ) ∧ a * (N - 1 : ℕ) ≤ B ∧
      Integrable U μ ∧ (∫ z, U z ∂μ) ≤ B * C ∧
      Real.exp (-(B * C)) ≤ Z ∧ Z ≤ 1 ∧
      ReferencePartition W b = ReferencePartition V b * Z ∧
      ReferenceLaw W b = μ.withDensity (fun z => ENNReal.ofReal (Z⁻¹ * Real.exp (-U z))) ∧
      IsProbabilityMeasure (ReferenceLaw W b) := by
-- BODY
  obtain ⟨C, hC, href⟩ := ReferenceOffsetDensity d (by omega) s κ L M1
    hs (by linarith) hκ hL
  refine ⟨C, hC, ?_⟩
  intro V b hV hb hquad hlocal N hN coupling ε hc hcB hε X i
  dsimp only
  let a := coupling / (N : ℝ)
  let J := Finset.univ.erase i
  let U := fun z => ∑ j ∈ J, a * RieszKernel s ε (z - ParticlePosition X j)
  let μ := ReferenceLaw V b
  let Z := ∫ z, Real.exp (-U z) ∂μ
  let W := fun z => V z + U z
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have ha : 0 ≤ a := div_nonneg hc hNp.le
  have hmass : 0 ≤ a * (N - 1 : ℕ) ∧ a * (N - 1 : ℕ) ≤ B := by
    constructor
    · positivity
    · have hn : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N 1
      calc
        a * (N - 1 : ℕ) ≤ a * (N : ℝ) := mul_le_mul_of_nonneg_left hn ha
        _ = coupling := by dsimp [a]; field_simp
        _ ≤ B := hcB
  have hre := href V b hV hb hquad hlocal
  let : IsProbabilityMeasure μ := hre.2.2.1
  have hrows (j : Fin N) := hre.2.2.2.2 ε hε.le (ParticlePosition X j)
  have hUn (z) : 0 ≤ U z := Finset.sum_nonneg fun j hj =>
    mul_nonneg ha ((RieszKernelBounds s ε hs hε.le).1 _)
  have hUm : Measurable U := by
    apply Finset.measurable_sum
    intro j hj
    have hm : Measurable (fun z : OneParticle d => RieszKernel s ε (z - ParticlePosition X j)) := by
      unfold RieszKernel; split_ifs <;> fun_prop
    exact hm.const_mul _
  have hiU : Integrable U μ := integrable_finsetSum J (fun j hj => (hrows j).1.const_mul a)
  have hmean : (∫ z, U z ∂μ) ≤ B * C := by
    rw [integral_finsetSum J (fun j hj => (hrows j).1.const_mul a)]
    simp_rw [integral_const_mul]
    calc
      _ ≤ ∑ j ∈ J, a * C := Finset.sum_le_sum
        (fun j hj => mul_le_mul_of_nonneg_left (hrows j).2 ha)
      _ = (a * (N - 1 : ℕ)) * C := by simp [J, Finset.card_erase_of_mem]; ring
      _ ≤ B * C := mul_le_mul_of_nonneg_right hmass.2 hC
  have hiZ : Integrable (fun z => Real.exp (-U z)) μ :=
    (integrable_const (1 : ℝ)).mono' hUm.neg.exp.aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hUn z)))
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Eventually.of_forall fun _ => Set.mem_univ _) hiU.neg hiZ
  simp only [Pi.neg_apply] at hj
  rw [integral_neg] at hj
  have hZlower : Real.exp (-(B * C)) ≤ Z :=
    (Real.exp_le_exp.mpr (neg_le_neg hmean)).trans hj
  have hZone : Z ≤ 1 := by
    simpa [Z] using integral_mono hiZ (integrable_const (1 : ℝ))
      (fun z => Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hUn z)))
  have hZ : 0 < Z := (Real.exp_pos _).trans_le hZlower
  have hnorm := ReferenceQuadraticNormalization V b κ (V 0) L hκ hV hb
    (fun z => by linarith [hquad z])
  have hbn (z) : 0 ≤ b z := by
    obtain ⟨m, M, hm, _, _, hbound⟩ := hb.bounds
    exact hm.le.trans (hbound z).1
  have he (z) : Real.exp (-W z) = Real.exp (-V z) * Real.exp (-U z) := by
    rw [← Real.exp_add]; congr 1; dsimp [W]; ring
  have hident : Z = (ReferencePartition V b)⁻¹ * ReferencePartition W b := by
    dsimp [Z, μ]
    unfold ReferenceLaw
    have hm : Measurable (fun z => ENNReal.ofReal
        ((ReferencePartition V b)⁻¹ * (b z * Real.exp (-V z)))) := by
      exact (measurable_const.mul (hb.measurable.mul hV.measurable.neg.exp)).ennreal_ofReal
    rw [integral_withDensity_eq_integral_toReal_smul hm
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp_rw [ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.mpr hnorm.2.le)
      (mul_nonneg (hbn _) (Real.exp_pos _).le)), smul_eq_mul]
    have he' : (fun z => (ReferencePartition V b)⁻¹ * (b z * Real.exp (-V z)) * Real.exp (-U z)) =
        fun z => (ReferencePartition V b)⁻¹ * (b z * Real.exp (-W z)) := by
      funext z; rw [he]; ring
    rw [he', integral_const_mul]
    rfl
  have hpart : ReferencePartition W b = ReferencePartition V b * Z := by
    rw [hident]
    field_simp [ne_of_gt hnorm.2]
  have hZW : 0 < ReferencePartition W b := by rw [hpart]; exact mul_pos hnorm.2 hZ
  have hiW : Integrable (fun z => b z * Real.exp (-W z)) := hnorm.1.mono'
    (hb.measurable.mul (hV.measurable.add hUm).neg.exp).aestronglyMeasurable
    (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hbn z) (Real.exp_pos _).le)]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by dsimp [W]; linarith [hUn z])) (hbn z))
  refine ⟨hmass.1, hmass.2, hiU, hmean, hZlower, hZone, hpart, ?_,
    ReferenceLawProbability W b hiW hbn hZW⟩
  change volume.withDensity (fun z => ENNReal.ofReal
    ((ReferencePartition W b)⁻¹ * (b z * Real.exp (-W z)))) =
    (volume.withDensity (fun z => ENNReal.ofReal
      ((ReferencePartition V b)⁻¹ * (b z * Real.exp (-V z))))).withDensity
      (fun z => ENNReal.ofReal (Z⁻¹ * Real.exp (-U z)))
  have hm1 : Measurable (fun z => ENNReal.ofReal
      ((ReferencePartition V b)⁻¹ * (b z * Real.exp (-V z)))) :=
    (measurable_const.mul (hb.measurable.mul hV.measurable.neg.exp)).ennreal_ofReal
  have hm2 : Measurable (fun z => ENNReal.ofReal (Z⁻¹ * Real.exp (-U z))) :=
    (measurable_const.mul hUm.neg.exp).ennreal_ofReal
  rw [← withDensity_mul volume hm1 hm2]
  congr 1
  funext z
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.mpr hnorm.2.le)
    (mul_nonneg (hbn z) (Real.exp_pos _).le))]
  congr 1
  rw [hpart, he, mul_inv_rev]
  ring
