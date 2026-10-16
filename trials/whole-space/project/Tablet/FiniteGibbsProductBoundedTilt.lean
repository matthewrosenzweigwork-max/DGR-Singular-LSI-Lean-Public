import Tablet.GibbsRawDensity
import Tablet.InteractionWeightBounds
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MeasureTheory Filter Set
open scoped ENNReal NNReal
noncomputable section

-- [TABLET NODE: FiniteGibbsProductBoundedTilt]
theorem FiniteGibbsProductBoundedTilt (N d : ℕ) (hd : 0 < d)
    (V b : OneParticle d → ℝ) (κ L : ℝ) (hκ : 0 < κ) (hL : 1 ≤ L)
    (hV : PotentialBounds d κ V) (hb : BoundedMultiplier d L b)
    (s coupling ε : ℝ) (hs : 0 < s) (ha : 0 ≤ coupling) (hε : 0 < ε) :
    let P := GibbsLaw (N:=N) (ReferenceLaw V (fun _ => 1)) s coupling ε
    let Q := GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε
    let w := fun X : ParticleConfig d N => ∏ i : Fin N, b (ParticlePosition X i)
    IsProbabilityMeasure P ∧ IsProbabilityMeasure Q ∧ Measurable w ∧
    Integrable w P ∧ 0 < ∫ X, w X ∂P ∧
    Q=P.withDensity (fun X => ENNReal.ofReal (w X/(∫ Y, w Y ∂P))) ∧
    ∃ m : ℝ, 0 < m ∧ ∀ X, m^N ≤ w X ∧ w X ≤ L^N*m^N := by
-- BODY
  classical
  let P := GibbsLaw (N:=N) (ReferenceLaw V (fun _ => 1)) s coupling ε
  let Q := GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε
  let w := fun X : ParticleConfig d N => ∏ i : Fin N, b (ParticlePosition X i)
  have hb1 : BoundedMultiplier d 1 (fun _ => 1) :=
    ⟨measurable_const,1,1,by norm_num,le_rfl,by norm_num,fun _ => ⟨le_rfl,le_rfl⟩⟩
  have hnorm0 := ConvexReferenceNormalization V (fun _ => 1) κ 1 hκ hV hb1
  have hnormb := ConvexReferenceNormalization V b κ L hκ hV hb
  have hgas0 := @SoftGibbsNormalization d N (ReferenceLaw V (fun _ => 1)) hnorm0.2.2 s coupling ε hs ha hε
  have hgasb := @SoftGibbsNormalization d N (ReferenceLaw V b) hnormb.2.2 s coupling ε hs ha hε
  letI : IsProbabilityMeasure P := hgas0.2.2
  letI : IsProbabilityMeasure Q := hgasb.2.2
  obtain ⟨m,M,hm,_,hcontrast,hbounds⟩ := hb.bounds
  have hbound (x) : m ≤ b x ∧ b x ≤ L*m :=
    ⟨(hbounds x).1,(hbounds x).2.trans ((div_le_iff₀ hm).mp hcontrast)⟩
  have hprod (X : ParticleConfig d N) : m^N ≤ w X ∧ w X ≤ L^N*m^N := by
    constructor
    · have h := Finset.prod_le_prod (s:=Finset.univ) (fun i _ => hm.le)
        (fun i _ => (hbound (ParticlePosition X i)).1)
      simpa [w] using h
    · have h := Finset.prod_le_prod (s:=Finset.univ)
        (fun i _ => hm.le.trans (hbound (ParticlePosition X i)).1)
        (fun i _ => (hbound (ParticlePosition X i)).2)
      simpa only [w,Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_pow] using h
  have hwn (X) : 0 ≤ w X := (pow_pos hm N).le.trans (hprod X).1
  have hpm (i : Fin N) : Measurable (fun X : ParticleConfig d N => ParticlePosition X i) := by
    unfold ParticlePosition; fun_prop
  have hwm : Measurable w := Finset.measurable_prod _ (fun i _ => hb.measurable.comp (hpm i))
  have hwi : Integrable w P :=
    (integrable_const (L^N*m^N)).mono' hwm.aestronglyMeasurable
      (Eventually.of_forall fun X => by rw [Real.norm_eq_abs,abs_of_nonneg (hwn X)]; exact (hprod X).2)
  have hE : 0 < ∫ X, w X ∂P := by
    have hlo := integral_mono (integrable_const (m^N)) hwi (fun X => (hprod X).1)
    have h := (pow_pos hm N).trans_le (by simpa using hlo)
    exact h
  let Z0 := (ReferencePartition V (fun _ => 1))^N * GibbsPartition (N:=N) (ReferenceLaw V (fun _ => 1)) s coupling ε
  let Zb := (ReferencePartition V b)^N * GibbsPartition (N:=N) (ReferenceLaw V b) s coupling ε
  have hZ0 : 0 < Z0 := mul_pos (pow_pos hnorm0.2.1 N) hgas0.2.1.1
  have hZb : 0 < Zb := mul_pos (pow_pos hnormb.2.1 N) hgasb.2.1.1
  let k := Z0/Zb
  have hk : 0 < k := div_pos hZ0 hZb
  have hp0n (X : ParticleConfig d N) : 0 ≤ GibbsLebesgueDensity V (fun _ => 1) s coupling ε X := by
    change 0 ≤ Z0⁻¹*(∏ i : Fin N, (1:ℝ))*Real.exp (-(∑ i : Fin N, V (ParticlePosition X i)))*InteractionWeight s coupling ε X
    exact mul_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.mpr hZ0.le) (by positivity)) (Real.exp_pos _).le)
      ((InteractionWeightBounds s coupling ε hs ha hε.le).1 X).1
  have hdm : Measurable (fun X : ParticleConfig d N => ENNReal.ofReal (GibbsLebesgueDensity V (fun _ => 1) s coupling ε X)) := by
    have hm : Measurable (fun X : ParticleConfig d N => ∑ i : Fin N, V (ParticlePosition X i)) :=
      Finset.measurable_sum _ (fun i _ => hV.regularity.continuous.measurable.comp (hpm i))
    unfold GibbsLebesgueDensity
    simp only [Finset.prod_const_one,mul_one]
    exact ((measurable_const.mul hm.neg.exp).mul (InteractionWeightMeasurable s coupling ε)).ennreal_ofReal
  have hscaled : Q=P.withDensity (fun X => ENNReal.ofReal (k*w X)) := by
    have hP := GibbsRawDensity (N:=N) hd V (fun _ => 1) κ 1 hκ hV hb1 s coupling ε hs ha hε.le
    have hQ := GibbsRawDensity (N:=N) hd V b κ L hκ hV hb s coupling ε hs ha hε.le
    dsimp only [P,Q]
    rw [hP,hQ,← withDensity_mul volume hdm ((hwm.const_mul k).ennreal_ofReal)]
    apply withDensity_congr_ae
    exact Eventually.of_forall fun X => by
      simp only [Pi.mul_apply]
      rw [← ENNReal.ofReal_mul (hp0n X)]
      congr 1
      change Zb⁻¹*w X*Real.exp (-(∑ i : Fin N, V (ParticlePosition X i)))*InteractionWeight s coupling ε X =
        (Z0⁻¹*(∏ i : Fin N, (1:ℝ))*Real.exp (-(∑ i : Fin N, V (ParticlePosition X i)))*InteractionWeight s coupling ε X)*(k*w X)
      simp only [Finset.prod_const_one,mul_one]
      dsimp [k]
      field_simp [hZ0.ne',hZb.ne']
  have hkE : k*(∫ X, w X ∂P)=1 := by
    have he := measure_univ (μ:=Q)
    rw [hscaled,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (hwi.const_mul k)
        (Eventually.of_forall fun X => mul_nonneg hk.le (hwn X)),integral_const_mul] at he
    have ht := congrArg ENNReal.toReal he
    simpa only [ENNReal.toReal_ofReal (mul_nonneg hk.le hE.le),ENNReal.toReal_one] using ht
  have hkeq : k=(∫ X, w X ∂P)⁻¹ := by
    have h := (eq_div_iff hE.ne').mpr hkE
    simpa only [one_div] using h
  have htilt : Q=P.withDensity (fun X => ENNReal.ofReal (w X/(∫ Y, w Y ∂P))) := by
    rw [hscaled,hkeq]
    congr 1
    funext X
    simp [div_eq_mul_inv,mul_comm]
  dsimp only
  exact ⟨inferInstance,inferInstance,hwm,hwi,hE,htilt,m,hm,hprod⟩

#print axioms FiniteGibbsProductBoundedTilt
