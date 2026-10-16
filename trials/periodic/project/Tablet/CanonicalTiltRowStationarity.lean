import Tablet.CanonicalTiltRowIdentity
import Tablet.ProductGibbsRowStationarity
import Tablet.ProductBackgroundFacts
open MeasureTheory
-- [TABLET NODE: CanonicalTiltRowStationarity]
theorem CanonicalTiltRowStationarity (d N : ℕ) (hN : 2 ≤ N) (l u β K H : ℝ)
    (q : BoundedBackground d l u) (hβ : 0 ≤ β) (hK : 0 ≤ K) (hH : 0 ≤ H)
    (g h : UnitAddTorus (Fin d) → ℝ) (hgm : Measurable g) (hhm : Measurable h)
    (hGe : ∀ x, g (-x) = g x) (hgb : ∀ x, |g x| ≤ K) (hhb : ∀ᵐ x ∂volume, |h x| ≤ H) :
    let W : Configuration d N → ℝ := fun X =>
      Real.exp (-β / (N : ℝ) * ∑ j : Fin N, h (X j)) * GibbsWeight g q.density β X
    let P := NormalizedTilt volume W
    let ν := fun (i : Fin N) (X : Configuration d N) => NormalizedTilt volume
      (fun z => q.density z * Real.exp (-β * h z / (N : ℝ)) * Real.exp (-ConditionalPotential g β X i z))
    (∀ i X, IsProbabilityMeasure (ν i X)) ∧
    ∀ i : Fin N, ∀ F : Configuration d N → ℝ, Measurable F → (∃ C : ℝ, ∀ X, |F X| ≤ C) →
      Integrable (fun X => ∫ z, F (Replacement X i z) ∂ν i X) P ∧
      (∫ X, ∫ z, F (Replacement X i z) ∂ν i X ∂P) = ∫ X, F X ∂P := by
-- BODY
  classical
  dsimp only
  haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp; infer_instance
  haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := inferInstance
  haveI : IsProbabilityMeasure (volume : Measure (Configuration d N)) := inferInstance
  let M := (volume : Measure (Configuration d N))
  let m := (volume : Measure (UnitAddTorus (Fin d)))
  let b : Configuration d N → ℝ := fun X => Real.exp (-β / (N : ℝ) * ∑ j : Fin N, h (X j))
  let W : Configuration d N → ℝ := fun X => b X * GibbsWeight g q.density β X
  let P := NormalizedTilt M W
  let ν := fun (i : Fin N) (X : Configuration d N) => NormalizedTilt m
    (fun z => q.density z * Real.exp (-β * h z / (N : ℝ)) * Real.exp (-ConditionalPotential g β X i z))
  have hnp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hbcoord : ∀ᵐ X ∂M, ∀ j : Fin N, |h (X j)| ≤ H := by
    rw [Filter.eventually_all]
    intro j
    exact (measurePreserving_eval (fun _ : Fin N => m) j).quasiMeasurePreserving.tendsto_ae hhb
  have hbm : Measurable b :=
    (measurable_const.mul (Finset.measurable_fun_sum _ fun j _ => hhm.comp (measurable_pi_apply j))).exp
  have hpairm : Measurable (PairEnergy (N := N) g) := by
    unfold PairEnergy
    refine measurable_const.mul (Finset.measurable_fun_sum _ fun j _ => ?_)
    refine Finset.measurable_fun_sum _ fun k _ => ?_
    split_ifs
    · exact hgm.comp ((measurable_pi_apply j).sub (measurable_pi_apply k))
    · exact measurable_const
  have hWm : Measurable W := hbm.mul ((measurable_const.mul hpairm).exp.mul (ProductBackgroundFacts d N l u q).1)
  have hPE (X : Configuration d N) : |PairEnergy g X| ≤ (N : ℝ) * K := by
    have hh : |∑ j : Fin N, ∑ k : Fin N, if j < k then g (X j-X k) else 0| ≤ (N : ℝ)*((N : ℝ)*K) := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply (Finset.sum_le_sum fun j _ => (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun k _ => show |if j<k then g (X j-X k) else 0| ≤ K from by
          split_ifs; exact hgb _; simpa using hK)).trans
      simp
    unfold PairEnergy
    rw [abs_mul,abs_inv,abs_of_nonneg (Nat.cast_nonneg N)]
    exact (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (Nat.cast_nonneg N))).trans_eq (by field_simp)
  have hb : ∀ᵐ X ∂M, Real.exp (-β*H) ≤ b X ∧ b X ≤ Real.exp (β*H) := by
    filter_upwards [hbcoord] with X hX
    have hlo : -(N : ℝ)*H ≤ ∑ j : Fin N, h (X j) := by
      have hh := Finset.sum_le_sum (s:=Finset.univ) fun j _ => (abs_le.mp (hX j)).1
      simpa using hh
    have hhi : (∑ j : Fin N, h (X j)) ≤ (N : ℝ)*H := by
      have hh := Finset.sum_le_sum (s:=Finset.univ) fun j _ => (abs_le.mp (hX j)).2
      simpa using hh
    have hdiv := div_nonneg hβ hnp.le
    have hlo' := mul_le_mul_of_nonneg_left hlo hdiv
    have hhi' := mul_le_mul_of_nonneg_left hhi hdiv
    have hid : β/(N : ℝ)*((N : ℝ)*H)=β*H := by field_simp
    have hnid : β/(N : ℝ)*(-(N : ℝ)*H)=-(β*H) := by field_simp
    rw [hid] at hhi'; rw [hnid] at hlo'
    change Real.exp (-β*H) ≤ Real.exp _ ∧ Real.exp _ ≤ Real.exp (β*H)
    constructor <;> apply Real.exp_le_exp.mpr
    · simpa only [neg_div,neg_mul] using neg_le_neg hhi'
    · simpa only [neg_div,neg_mul,neg_neg] using neg_le_neg hlo'
  let L := Real.exp (-β * ((N : ℝ)*K)) * Real.exp (-β*H) * l^N
  let U := Real.exp (β * ((N : ℝ)*K)) * Real.exp (β*H) * u^N
  have hL : 0 < L := mul_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _)) (pow_pos q.lower_pos _)
  have hWb : ∀ᵐ X ∂M, L ≤ W X ∧ W X ≤ U := by
    filter_upwards [hb,(ProductBackgroundFacts d N l u q).2.2.2] with X hbX hqX
    have hglo : Real.exp (-β * ((N : ℝ)*K)) ≤ Real.exp (-β*PairEnergy g X) :=
      Real.exp_le_exp.mpr (by simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_left (abs_le.mp (hPE X)).2 hβ))
    have hghi : Real.exp (-β*PairEnergy g X) ≤ Real.exp (β * ((N : ℝ)*K)) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left (abs_le.mp (hPE X)).1 hβ
      nlinarith
    have hq0 : 0 ≤ ProductDensity q.density X := (pow_nonneg q.lower_pos.le N).trans hqX.1
    dsimp [L,U,W,GibbsWeight]
    constructor
    · have hh := mul_le_mul hglo hbX.1 (Real.exp_pos _).le (Real.exp_pos _).le
      have hh' := mul_le_mul hh hqX.1 (pow_nonneg q.lower_pos.le N) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      simpa only [mul_assoc,mul_left_comm (b X)] using hh'
    · have hh := mul_le_mul hghi hbX.2 (Real.exp_pos _).le (Real.exp_pos _).le
      have hh' := mul_le_mul hh hqX.2 hq0 (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      simpa only [mul_assoc,mul_left_comm (b X)] using hh'
  have rowprob (i : Fin N) (X : Configuration d N) : IsProbabilityMeasure (ν i X) := by
    let V := fun z => q.density z * Real.exp (-β*h z/(N : ℝ)) * Real.exp (-ConditionalPotential g β X i z)
    have hVm : Measurable V := by
      have hcm : Measurable (ConditionalPotential g β X i) := by
        unfold ConditionalPotential
        refine measurable_const.mul (Finset.measurable_fun_sum _ fun j _ => ?_)
        split_ifs; exact measurable_const; exact hgm.comp (measurable_id.sub measurable_const)
      exact (q.measurable.mul ((hhm.const_mul (-β)).div_const _).exp).mul hcm.neg.exp
    have hUb (z : UnitAddTorus (Fin d)) : |ConditionalPotential g β X i z| ≤ β*K := by
      have hh : |∑ j : Fin N, if j=i then 0 else g (z-X j)| ≤ (N : ℝ)*K := by
        exact (Finset.abs_sum_le_sum_abs _ _).trans (by
          have hh := Finset.sum_le_sum (s:=Finset.univ) fun j _ =>
            show |if j=i then (0:ℝ) else g (z-X j)| ≤ K from by split_ifs; simpa using hK; exact hgb _
          simpa using hh)
      unfold ConditionalPotential
      rw [abs_mul,abs_of_nonneg (div_nonneg hβ hnp.le)]
      exact (mul_le_mul_of_nonneg_left hh (div_nonneg hβ hnp.le)).trans_eq (by field_simp)
    have hβN : 0 ≤ β/(N : ℝ) := div_nonneg hβ hnp.le
    let Lr := l*Real.exp (-(β/(N : ℝ)*H))*Real.exp (-β*K)
    let Ur := u*Real.exp (β/(N : ℝ)*H)*Real.exp (β*K)
    have hLr : 0 < Lr := mul_pos (mul_pos q.lower_pos (Real.exp_pos _)) (Real.exp_pos _)
    have hVb : ∀ᵐ z ∂m, Lr ≤ V z ∧ V z ≤ Ur := by
      filter_upwards [q.bounds,hhb] with z hqz hhz
      have helo : Real.exp (-(β/(N : ℝ)*H)) ≤ Real.exp (-β*h z/(N : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_left (abs_le.mp hhz).2 hβN
        have heq : -(β/(N : ℝ)*h z) = -β*h z/(N : ℝ) := by ring
        have he := neg_le_neg hh
        rwa [heq] at he
      have hehi : Real.exp (-β*h z/(N : ℝ)) ≤ Real.exp (β/(N : ℝ)*H) := by
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_left (abs_le.mp hhz).1 hβN
        have heq : -(β/(N : ℝ)*h z) = -β*h z/(N : ℝ) := by ring
        have he := neg_le_neg hh
        simpa only [heq,mul_neg,neg_neg] using he
      have hulo : Real.exp (-β*K) ≤ Real.exp (-ConditionalPotential g β X i z) :=
        Real.exp_le_exp.mpr (by simpa only [neg_mul] using neg_le_neg (abs_le.mp (hUb z)).2)
      have huhi : Real.exp (-ConditionalPotential g β X i z) ≤ Real.exp (β*K) :=
        Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hUb z)).1])
      dsimp [Lr,Ur,V]
      exact ⟨mul_le_mul (mul_le_mul hqz.1 helo (Real.exp_pos _).le (q.lower_pos.le.trans hqz.1))
          hulo (Real.exp_pos _).le (mul_nonneg (q.lower_pos.le.trans hqz.1) (Real.exp_pos _).le),
        mul_le_mul (mul_le_mul hqz.2 hehi (Real.exp_pos _).le (zero_le_one.trans q.one_le_upper))
          huhi (Real.exp_pos _).le (mul_nonneg (zero_le_one.trans q.one_le_upper) (Real.exp_pos _).le)⟩
    have ht := BoundedTiltBounds m V Lr Ur hLr hVm hVb
    exact (TiltNormalization m V hVm (hVb.mono fun z hz => hLr.le.trans hz.1) ht.1 (hLr.trans_le ht.2.1)).1
  refine ⟨rowprob, ?_⟩
  intro i F hF hFb
  have ht := ProductGibbsRowStationarity d N W L U hL hWm hWb i F hF hFb
  have hrows := CanonicalTiltRowIdentity d N l u β q g h hGe i
  have hrowsP : ∀ᵐ X ∂P,
      NormalizedTilt m (fun z => W (Replacement X i z)) = ν i X :=
    hrows.filter_mono (withDensity_absolutelyContinuous _ _).ae_le
  have heq : (fun X => ∫ z, F (Replacement X i z) ∂NormalizedTilt m (fun z => W (Replacement X i z))) =ᵐ[P]
      (fun X => ∫ z, F (Replacement X i z) ∂ν i X) := hrowsP.mono fun X hx => by dsimp only; rw [hx]
  exact ⟨ht.1.congr heq, (integral_congr_ae heq).symm.trans ht.2⟩
