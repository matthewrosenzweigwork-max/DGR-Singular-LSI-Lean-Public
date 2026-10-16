module

public import Tablet.EntropyLpBound
public import Tablet.TorusSobolev
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Analysis.Calculus.ContDiff.WithLp

@[expose] public section
open MeasureTheory
open scoped ContDiff

-- [TABLET NODE: TorusDefectiveLogSobolev]
theorem TorusDefectiveLogSobolev (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : UnitAddTorus (Fin d) → ℝ, TorusSmooth f →
      Entropy (volume : Measure (UnitAddTorus (Fin d))) (fun x => f x ^ 2) ≤
        C * ((∫ x, f x ^ 2) + ∫ x, ‖TorusGradient f x‖ ^ 2) := by
-- BODY
  haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simpa using (inferInstance : IsProbabilityMeasure AddCircle.haarAddCircle)
  haveI : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin d =>
      (volume : Measure (AddCircle (1 : ℝ))))))
  let p : ℝ := if d ≤ 2 then 4 else 2*(d:ℝ)/((d:ℝ)-2)
  obtain ⟨hp, C, hC, hsob⟩ := TorusSobolev d hd
  change 2 < p at hp
  change ∀ f, TorusSmooth f → Real.rpow (∫ x, Real.rpow |f x| p) (2/p) ≤
    C*((∫ x,f x^2)+∫ x, ‖TorusGradient f x‖^2) at hsob
  let q := p/2
  have hq : 1 < q := by dsimp [q]; linarith
  have hratio : 0 < q/(q-1) := div_pos (by linarith) (by linarith)
  refine ⟨q/(q-1)*C, mul_pos hratio hC, ?_⟩
  intro f hf
  have quotient : IsOpenQuotientMap (TorusLift d) := by
    have hc : IsOpenQuotientMap ((↑) : ℝ → AddCircle (1 : ℝ)) :=
      QuotientAddGroup.isOpenQuotientMap_mk
    have hpi := IsOpenQuotientMap.piMap (fun _ : Fin d => hc)
    exact hpi.comp (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isOpenQuotientMap
  have hfc : Continuous f := quotient.continuous_comp_iff.mp hf.continuous
  have hfs : Continuous (fun x => f x^2) := hfc.pow 2
  have hflog : Continuous (fun x => (f x^2)*Real.log (f x^2)) :=
    Real.continuous_mul_log.comp hfs
  have hfp : Continuous (fun x => Real.rpow (f x^2) q) :=
    hfs.rpow_const (fun _ => Or.inr (le_of_lt (by linarith : 0 < q)))
  have hb := EntropyLpBound volume (fun x => f x^2) hfs.measurable
    (Filter.Eventually.of_forall fun x => sq_nonneg (f x))
    (hfs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hflog.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    q hq (hfp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have hid (x : UnitAddTorus (Fin d)) : Real.rpow (f x^2) q = Real.rpow |f x| p := by
    have hpow : f x^2 = Real.rpow |f x| (2:ℝ) := by simp
    rw [hpow]
    change (|f x|^(2:ℝ))^q=|f x|^p
    rw [← Real.rpow_mul (abs_nonneg _)]
    congr 1
    dsimp [q]; ring
  have hexp : 1/q=2/p := by dsimp [q]; field_simp
  simp_rw [hid] at hb
  rw [hexp] at hb
  calc
    Entropy volume (fun x => f x^2) ≤ q/(q-1)*Real.rpow (∫ x, Real.rpow |f x| p) (2/p) := hb
    _ ≤ q/(q-1)*(C*((∫ x,f x^2)+∫ x, ‖TorusGradient f x‖^2)) :=
      mul_le_mul_of_nonneg_left (hsob f hf) hratio.le
    _ = (q/(q-1)*C)*((∫ x,f x^2)+∫ x, ‖TorusGradient f x‖^2) := by ring
