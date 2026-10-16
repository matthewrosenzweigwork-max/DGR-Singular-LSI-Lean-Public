module

public import Tablet.ConfigurationReference
public import Tablet.CollisionSet
public import Mathlib.Probability.Independence.Basic

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Set

-- [TABLET NODE: ConfigurationCollisionNull]
theorem ConfigurationCollisionNull (d N : ℕ) (hd : 0 < d)
    (μ : Measure (OneParticle d)) [IsProbabilityMeasure μ]
    (hμ : μ ≪ (volume : Measure (OneParticle d))) :
    ConfigurationReference d N μ (CollisionSet d N) = 0 := by
-- BODY
  classical
  have productCoordinate_pairNull {ι E : Type} [Fintype ι] [TopologicalSpace E]
      [MeasurableSpace E] [BorelSpace E] [T2Space E] [SecondCountableTopology E]
      (μ : Measure E) [IsProbabilityMeasure μ] [NullSingletonClass μ]
      (i j : ι) (hij : i ≠ j) :
      (Measure.pi (fun _ : ι => μ)) {Y : ι → E | Y i = Y j} = 0 := by
    have hInd := (iIndepFun_pi (μ := fun _ : ι => μ) (X := fun _ => id)
      (fun _ => aemeasurable_id)).indepFun hij
    have hp : MeasurePreserving (fun Y : ι → E => (Y i, Y j))
        (Measure.pi (fun _ : ι => μ)) (μ.prod μ) := by
      refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), ?_⟩
      have h := hInd.map_prod_eq_prod_map_map
        (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
      simpa only [(measurePreserving_eval (fun _ : ι => μ) i).map_eq,
        (measurePreserving_eval (fun _ : ι => μ) j).map_eq] using h
    have hm : MeasurableSet {p : E × E | p.1 = p.2} :=
      (isClosed_eq continuous_fst continuous_snd).measurableSet
    have hnull : μ.prod μ {p : E × E | p.1 = p.2} = 0 := by
      rw [Measure.measure_prod_null hm]
      exact Eventually.of_forall (fun x => by
        change μ {y : E | x = y} = 0
        have hy : {y : E | x = y} = {x} := by ext y; simp [eq_comm]
        rw [hy, measure_singleton])
    have h := hp.measure_preimage hm.nullMeasurableSet
    change (Measure.pi (fun _ : ι => μ)) {Y : ι → E | Y i = Y j} = _ at h
    exact h.trans hnull
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  let : NullSingletonClass μ := ⟨fun x => hμ (measure_singleton x)⟩
  let F := fun Y : Fin N → OneParticle d =>
    WithLp.toLp 2 (fun ik : Fin N × Fin d => Y ik.1 ik.2)
  have hm : Measurable F := by unfold F; fun_prop
  have hclosed : IsClosed (CollisionSet d N) := by
    have heq : CollisionSet d N =
        ⋃ i : Fin N, ⋃ j : Fin N, {X : ParticleConfig d N |
          i < j ∧ ParticlePosition X i = ParticlePosition X j} := by
      ext X
      simp [CollisionSet]
    rw [heq]
    apply isClosed_iUnion_of_finite
    intro i
    apply isClosed_iUnion_of_finite
    intro j
    by_cases hij : i < j
    · simp only [hij, true_and]
      exact isClosed_eq (by unfold ParticlePosition; fun_prop)
        (by unfold ParticlePosition; fun_prop)
    · simp [hij]
  unfold ConfigurationReference
  rw [Measure.map_apply hm hclosed.measurableSet]
  have hpair (i j : Fin N) : (Measure.pi (fun _ : Fin N => μ))
      {Y : Fin N → OneParticle d | i < j ∧ ParticlePosition (F Y) i =
        ParticlePosition (F Y) j} = 0 := by
    by_cases hij : i < j
    · apply measure_mono_null (t := {Y : Fin N → OneParticle d | Y i = Y j})
      · intro Y hY
        apply PiLp.ext
        intro k
        have hh := congrArg (fun z : OneParticle d => z k) hY.2
        exact hh
      · exact productCoordinate_pairNull μ i j (ne_of_lt hij)
    · simp only [hij, false_and, ofPred_false, measure_empty]
  have he : F ⁻¹' CollisionSet d N =
      ⋃ i : Fin N, ⋃ j : Fin N,
        {Y : Fin N → OneParticle d | i < j ∧
          ParticlePosition (F Y) i = ParticlePosition (F Y) j} := by
    ext Y
    simp [CollisionSet]
  rw [he]
  exact measure_iUnion_null (fun i => measure_iUnion_null (hpair i))
