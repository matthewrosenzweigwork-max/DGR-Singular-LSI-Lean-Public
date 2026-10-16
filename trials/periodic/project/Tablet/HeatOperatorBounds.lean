module

public import Tablet.HeatKernelFacts
public import Mathlib.Analysis.Convolution

@[expose] public section
-- [TABLET NODE: HeatOperatorBounds]
theorem HeatOperatorBounds (d : ℕ) (t : ℝ) (ht : 0 < t)
    (f : UnitAddTorus (Fin d) → ℝ) (hf : Measurable f)
    (hi : MeasureTheory.Integrable f (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d)))) :
    Measurable (HeatSemigroup d t f) ∧
    MeasureTheory.Integrable (HeatSemigroup d t f) (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d))) ∧
    (∫ x, HeatSemigroup d t f x ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d)))) = (∫ x, f x ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d)))) ∧
    (∫ x, |HeatSemigroup d t f x| ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d)))) ≤ (∫ x, |f x| ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d)))) ∧
    (∀ (l u : ℝ), (∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d))), l ≤ f x ∧ f x ≤ u) →
      ∀ x, l ≤ HeatSemigroup d t f x ∧ HeatSemigroup d t f x ≤ u) ∧
    (∀ (h : UnitAddTorus (Fin d) → ℝ), Measurable h →
      (∃ C : ℝ, ∀ x, |h x| ≤ C) →
      (∫ x, h x * HeatSemigroup d t f x ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d)))) =
        (∫ x, f x * HeatSemigroup d t h x ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d))))) := by
-- BODY
  classical
  let T := UnitAddTorus (Fin d)
  let m : MeasureTheory.Measure T := MeasureTheory.volume
  let p : T → ℝ := HeatKernel d t
  have hpc : Continuous p := (HeatKernelFacts d t ht).1
  have hpn : ∀ x, 0 ≤ p x := (HeatKernelFacts d t ht).2.1
  have hpe : ∀ x, p (-x) = p x := (HeatKernelFacts d t ht).2.2.1
  have hpm : (∫ x, p x ∂m) = 1 := (HeatKernelFacts d t ht).2.2.2.1
  obtain ⟨C, hC⟩ := (isCompact_univ : IsCompact (Set.univ : Set T)).exists_bound_of_continuousOn hpc.continuousOn
  have hpbound : ∀ x, ‖p x‖ ≤ C := fun x => hC x (Set.mem_univ x)
  have hpba : BddAbove (Set.range fun x => ‖p x‖) := ⟨C, by rintro _ ⟨x, rfl⟩; exact hpbound x⟩
  have hpi : MeasureTheory.Integrable p m := MeasureTheory.Integrable.of_bound hpc.measurable.aestronglyMeasurable C (Filter.Eventually.of_forall hpbound)
  let L := ContinuousLinearMap.mul ℝ ℝ
  have hop : ∀ g : T → ℝ, MeasureTheory.Integrable g m →
      Measurable (HeatSemigroup d t g) ∧ MeasureTheory.Integrable (HeatSemigroup d t g) m ∧
      (∫ x, HeatSemigroup d t g x ∂m) = ∫ x, g x ∂m := by
    intro g hgi
    have hc := hpba.continuous_convolution_left_of_integrable L hpc hgi
    have hin := hpi.integrable_convolution L hgi
    have heq := MeasureTheory.integral_convolution L hpi hgi
    have hconv : HeatSemigroup d t g = MeasureTheory.convolution p g L m := by
      funext x
      simp only [HeatSemigroup, MeasureTheory.convolution_def, ContinuousLinearMap.mul_apply', L, p, m]
      rfl
    rw [hconv]
    exact ⟨hc.measurable, hin, by simpa [L, hpm] using heq⟩
  have hpoint : ∀ g : T → ℝ, MeasureTheory.Integrable g m → ∀ x,
      MeasureTheory.Integrable (fun y => p y * g (x-y)) m := by
    intro g hgi x
    exact (hgi.comp_sub_left x).bdd_mul hpc.measurable.aestronglyMeasurable (Filter.Eventually.of_forall hpbound)
  have hfi : MeasureTheory.Integrable f m := hi
  have habs : ∀ x, |HeatSemigroup d t f x| ≤ HeatSemigroup d t (fun z => |f z|) x := by
    intro x
    simpa only [HeatSemigroup, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hpn _)] using
      MeasureTheory.norm_integral_le_integral_norm (fun y => p y * f (x-y)) (μ := m)
  have hcontract : (∫ x, |HeatSemigroup d t f x| ∂m) ≤ ∫ x, |f x| ∂m := by
    calc
      _ ≤ ∫ x, HeatSemigroup d t (fun z => |f z|) x ∂m :=
        MeasureTheory.integral_mono_ae (hop f hfi).2.1.abs (hop _ hfi.abs).2.1 (Filter.Eventually.of_forall habs)
      _ = _ := (hop _ hfi.abs).2.2
  refine ⟨(hop f hfi).1, (hop f hfi).2.1, (hop f hfi).2.2, hcontract, ?_, ?_⟩
  · intro l u hb x
    have hb' : ∀ᵐ y ∂m, l ≤ f (x-y) ∧ f (x-y) ≤ u :=
      (MeasureTheory.quasiMeasurePreserving_sub_left_of_right_invariant m x).tendsto_ae hb
    have hli : MeasureTheory.Integrable (fun y => p y * l) m := hpi.mul_const l
    have hui : MeasureTheory.Integrable (fun y => p y * u) m := hpi.mul_const u
    have hl := MeasureTheory.integral_mono_ae hli (hpoint f hfi x) (hb'.mono fun y hy => mul_le_mul_of_nonneg_left hy.1 (hpn y))
    have hu := MeasureTheory.integral_mono_ae (hpoint f hfi x) hui (hb'.mono fun y hy => mul_le_mul_of_nonneg_left hy.2 (hpn y))
    simpa only [HeatSemigroup, MeasureTheory.integral_mul_const, hpm, one_mul] using And.intro hl hu
  · intro h hm hb
    obtain ⟨D, hD⟩ := hb
    have hDnorm : ∀ x, ‖h x‖ ≤ D := fun x => by simpa only [Real.norm_eq_abs] using hD x
    have hci : MeasureTheory.Integrable (fun v : T × T => p v.2 * f (v.1-v.2)) (m.prod m) := by
      simpa only [L, ContinuousLinearMap.mul_apply'] using hpi.convolution_integrand L hfi
    have hfirst : MeasureTheory.Integrable (fun v : T × T => h v.1 * (p v.2 * f (v.1-v.2))) (m.prod m) :=
      hci.bdd_mul (hm.comp measurable_fst).aestronglyMeasurable (Filter.Eventually.of_forall fun v => hDnorm v.1)
    have hsecond : MeasureTheory.Integrable (fun v : T × T => f v.1 * (p v.2 * h (v.1+v.2))) (m.prod m) := by
      have hh : Measurable (fun v : T × T => h (v.1+v.2)) := hm.comp (measurable_fst.add measurable_snd)
      have hi' := (hfi.mul_prod hpi).bdd_mul hh.aestronglyMeasurable (Filter.Eventually.of_forall fun v => hDnorm (v.1+v.2))
      convert hi' using 1
      funext v
      ring
    have htrans : ∀ y : T,
        (∫ x, h x * (p y * f (x-y)) ∂m) = ∫ z, f z * (p y * h (z+y)) ∂m := by
      intro y
      calc
        _ = ∫ z, h (z+y) * (p y * f ((z+y)-y)) ∂m :=
          (MeasureTheory.integral_add_right_eq_self (fun x => h x * (p y * f (x-y))) y (μ := m)).symm
        _ = _ := by
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall fun z => by simp only [add_sub_cancel_right]; ring
    have hneg : ∀ z : T, (∫ y, p y * h (z+y) ∂m) = HeatSemigroup d t h z := by
      intro z
      calc
        _ = ∫ y, p (-y) * h (z+(-y)) ∂m :=
          (MeasureTheory.integral_neg_eq_self (fun y => p y * h (z+y)) m).symm
        _ = ∫ y, p y * h (z-y) ∂m := by
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall fun y => by dsimp only; rw [hpe, sub_eq_add_neg]
        _ = _ := rfl
    change (∫ x, h x * HeatSemigroup d t f x ∂m) = ∫ x, f x * HeatSemigroup d t h x ∂m
    calc
      _ = ∫ x, ∫ y, h x * (p y * f (x-y)) ∂m ∂m := by
        congr 1
        funext x
        rw [MeasureTheory.integral_const_mul]
        rfl
      _ = ∫ y, ∫ x, h x * (p y * f (x-y)) ∂m ∂m :=
        MeasureTheory.integral_integral_swap hfirst
      _ = ∫ y, ∫ z, f z * (p y * h (z+y)) ∂m ∂m := by
        congr 1
        funext y
        exact htrans y
      _ = ∫ z, ∫ y, f z * (p y * h (z+y)) ∂m ∂m :=
        (MeasureTheory.integral_integral_swap hsecond).symm
      _ = ∫ z, f z * HeatSemigroup d t h z ∂m := by
        congr 1
        funext z
        rw [MeasureTheory.integral_const_mul, hneg]

