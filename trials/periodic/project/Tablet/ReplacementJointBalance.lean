import Tablet.ReplacementHaarSwap
import Tablet.ReplacementEdgeWeight
import Tablet.GibbsNormalizerBounds
import Tablet.ProductBackgroundFacts
-- [TABLET NODE: ReplacementJointBalance]
theorem ReplacementJointBalance (d N : ℕ) (hN : 2 ≤ N) (l u β : ℝ)
    (q : BoundedBackground d l u) (hβ : 0 ≤ β)
    (G : UnitAddTorus (Fin d) → ℝ) (hG : Measurable G)
    (hGi : MeasureTheory.Integrable G MeasureTheory.volume)
    (hGn : ∀ x, 0 ≤ G x) (hGe : ∀ x, G (-x) = G x) (i : Fin N) :
    let P := CanonicalLaw (N := N) G q.density β
    let J := (P.prod MeasureTheory.volume).withDensity
      (fun v : Configuration d N × UnitAddTorus (Fin d) => ENNReal.ofReal
        (Real.exp (-ConditionalPotential G β v.1 i v.2) * q.density v.2))
    let S := fun v : Configuration d N × UnitAddTorus (Fin d) =>
      (Replacement v.1 i v.2, v.1 i)
    MeasureTheory.MeasurePreserving S J J ∧
    J.map Prod.fst ≤ P ∧
    J.map (fun v => Replacement v.1 i v.2) ≤ P := by
-- BODY
  classical
  haveI : MeasureTheory.IsProbabilityMeasure (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
    infer_instance
  let T := UnitAddTorus (Fin d)
  let M : MeasureTheory.Measure (Configuration d N) := MeasureTheory.volume
  let m : MeasureTheory.Measure T := MeasureTheory.volume
  haveI : MeasureTheory.IsProbabilityMeasure m := by dsimp [m, T]; infer_instance
  let μ := M.prod m
  let P := CanonicalLaw (N := N) G q.density β
  let W := GibbsWeight (N := N) G q.density β
  let Z := ∫ X, W X ∂M
  let r : Configuration d N × T → ℝ := fun v => Real.exp (-ConditionalPotential G β v.1 i v.2) * q.density v.2
  let S : Configuration d N × T → Configuration d N × T := fun v => (Replacement v.1 i v.2, v.1 i)
  let J := (P.prod m).withDensity (fun v => ENNReal.ofReal (r v))
  have hAm : Measurable (PairEnergy (N := N) G) := by
    unfold PairEnergy
    refine measurable_const.mul (Finset.measurable_fun_sum _ fun j _ => ?_)
    refine Finset.measurable_fun_sum _ fun k _ => ?_
    split_ifs
    · exact hG.comp ((measurable_pi_apply j).sub (measurable_pi_apply k))
    · exact measurable_const
  have hWm : Measurable W := ((hAm.const_mul (-β)).exp).mul (ProductBackgroundFacts d N l u q).1
  have hUm : Measurable (fun v : Configuration d N × T => ConditionalPotential G β v.1 i v.2) := by
    unfold ConditionalPotential
    refine measurable_const.mul (Finset.measurable_fun_sum _ fun j _ => ?_)
    split_ifs
    · exact measurable_const
    · exact hG.comp (measurable_snd.sub ((measurable_pi_apply j).comp measurable_fst))
  have hrm : Measurable r := (hUm.neg.exp).mul (q.measurable.comp measurable_snd)
  have hUn (X : Configuration d N) (z : T) : 0 ≤ ConditionalPotential G β X i z := by
    unfold ConditionalPotential
    exact mul_nonneg (div_nonneg hβ (Nat.cast_nonneg N)) (Finset.sum_nonneg fun j _ => by split_ifs; exact le_rfl; exact hGn _)
  have hre (v : Configuration d N × T) : 0 ≤ Real.exp (-ConditionalPotential G β v.1 i v.2) ∧ Real.exp (-ConditionalPotential G β v.1 i v.2) ≤ 1 :=
    ⟨(Real.exp_pos _).le, (Real.exp_le_one_iff).mpr (neg_nonpos.mpr (hUn _ _))⟩
  have hgibbs := GibbsNormalizerBounds d N hN l u q G hG hGi 0 β (le_refl 0) hβ (Filter.Eventually.of_forall fun x => by simpa using hGn x)
  have hZ : 0 < Z := lt_of_lt_of_le (Real.exp_pos _) hgibbs.2.1
  have hWn : ∀ᵐ X ∂M, 0 ≤ W X := by
    filter_upwards [(ProductBackgroundFacts d N l u q).2.2.2] with X hX
    exact mul_nonneg (Real.exp_pos _).le ((pow_nonneg q.lower_pos.le N).trans hX.1)
  have hS := (ReplacementHaarSwap d N i).1
  have hSμ : MeasureTheory.MeasurePreserving S μ μ := hS
  have hwd : ∀ ρ : Configuration d N × T → ENNReal, Measurable ρ →
      (∀ v, ρ (S v) = ρ v) → MeasureTheory.MeasurePreserving S (μ.withDensity ρ) (μ.withDensity ρ) := by
    intro ρ hρ hρS
    refine ⟨hSμ.measurable, ?_⟩
    apply MeasureTheory.Measure.ext
    intro A hA
    rw [MeasureTheory.Measure.map_apply hSμ.measurable hA,
      MeasureTheory.withDensity_apply _ (hA.preimage hSμ.measurable), MeasureTheory.withDensity_apply _ hA]
    rw [← MeasureTheory.lintegral_indicator (hA.preimage hSμ.measurable), ← MeasureTheory.lintegral_indicator hA]
    calc
      _ = ∫⁻ v, A.indicator ρ (S v) ∂μ := by
        apply MeasureTheory.lintegral_congr_ae
        exact Filter.Eventually.of_forall fun v => by
          by_cases hv : S v ∈ A <;> simp [Set.indicator, hv, hρS]
      _ = _ := hSμ.lintegral_comp (hρ.indicator hA)
  let ρ : Configuration d N × T → ENNReal := fun v => ENNReal.ofReal (W v.1 * r v / Z)
  have hρm : Measurable ρ := (((hWm.comp measurable_fst).mul hrm).div_const Z).ennreal_ofReal
  have hρS : ∀ v, ρ (S v) = ρ v := by
    intro v
    have hw := (ReplacementEdgeWeight G q.density hGe β v.1 i v.2).1
    dsimp only [ρ, r, S]
    congr 1
    congr 1
    calc
      _ = GibbsWeight G q.density β (Replacement v.1 i v.2) * Real.exp (-ConditionalPotential G β (Replacement v.1 i v.2) i (v.1 i)) * q.density (v.1 i) := by ring
      _ = GibbsWeight G q.density β v.1 * Real.exp (-ConditionalPotential G β v.1 i v.2) * q.density v.2 := hw.symm
      _ = _ := by ring
  have hprod : P.prod m = μ.withDensity (fun v => ENNReal.ofReal (W v.1 / Z)) := by
    have hh := MeasureTheory.prod_withDensity (hWm.div_const Z).ennreal_ofReal (measurable_const (a := (1 : ENNReal))) (μ := M) (ν := m)
    have hht := hh
    simp only [MeasureTheory.withDensity_const, one_smul, mul_one] at hht
    convert hht using 1 <;> rfl
  have hJ : J = μ.withDensity ρ := by
    dsimp only [J]
    have hd : Measurable (fun v : Configuration d N × T => ENNReal.ofReal (W v.1 / Z)) := ((hWm.comp measurable_fst).div_const Z).ennreal_ofReal
    rw [hprod, ← MeasureTheory.withDensity_mul μ hd hrm.ennreal_ofReal]
    apply MeasureTheory.withDensity_congr_ae
    have hn : ∀ᵐ v ∂μ, 0 ≤ W v.1 := (MeasureTheory.measurePreserving_fst (μ := M) (ν := m)).quasiMeasurePreserving.tendsto_ae hWn
    filter_upwards [hn] with v hv
    change ENNReal.ofReal (W v.1 / Z) * ENNReal.ofReal (r v) = ENNReal.ofReal (W v.1 * r v / Z)
    rw [← ENNReal.ofReal_mul (div_nonneg hv hZ.le)]
    congr 1
    ring
  have hJS : MeasureTheory.MeasurePreserving S J J := by rw [hJ]; exact hwd ρ hρm hρS
  have hqi : MeasureTheory.Integrable q.density m :=
    MeasureTheory.Integrable.of_bound q.measurable.aestronglyMeasurable u
      (q.bounds.mono fun z hz => by rw [Real.norm_eq_abs, abs_of_nonneg (q.lower_pos.le.trans hz.1)]; exact hz.2)
  have hqn : ∀ᵐ z ∂m, 0 ≤ q.density z := q.bounds.mono fun z hz => q.lower_pos.le.trans hz.1
  have hqm : (∫ z, q.density z ∂m) = 1 := q.mass
  let Q := m.withDensity (fun z => ENNReal.ofReal (q.density z))
  have hQ : MeasureTheory.IsProbabilityMeasure Q := by
    have hh := (TiltNormalization m q.density q.measurable hqn hqi (by simpa only [hqm] using (zero_lt_one : (0:ℝ)<1))).1
    simpa only [NormalizedTilt, hqm, div_one] using hh
  letI := hQ
  have hJle : J ≤ P.prod Q := by
    have hh := MeasureTheory.prod_withDensity (μ := P) (ν := m) (measurable_const (a := (1 : ENNReal))) q.measurable.ennreal_ofReal
    have hPQ : P.prod Q = (P.prod m).withDensity (fun v => ENNReal.ofReal (q.density v.2)) := by
      simpa only [MeasureTheory.withDensity_const, one_smul, one_mul, Q] using hh
    rw [hPQ]
    apply MeasureTheory.withDensity_mono
    apply Filter.Eventually.of_forall
    intro v
    change ENNReal.ofReal (Real.exp (-ConditionalPotential G β v.1 i v.2) * q.density v.2) ≤ ENNReal.ofReal (q.density v.2)
    rw [ENNReal.ofReal_mul (hre v).1]
    exact mul_le_of_le_one_left zero_le (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hre v).2)
  have hfst : J.map Prod.fst ≤ P := by
    have hh := MeasureTheory.Measure.map_mono hJle measurable_fst
    simpa only [(MeasureTheory.measurePreserving_fst (μ := P) (ν := Q)).map_eq] using hh
  have hrepl : J.map (fun v => Replacement v.1 i v.2) ≤ P := by
    have hh := MeasureTheory.Measure.map_map measurable_fst hJS.measurable (μ := J)
    rw [hJS.map_eq] at hh
    change J.map Prod.fst = J.map (fun v => Replacement v.1 i v.2) at hh
    rw [← hh]
    exact hfst
  exact ⟨hJS, hfst, hrepl⟩
