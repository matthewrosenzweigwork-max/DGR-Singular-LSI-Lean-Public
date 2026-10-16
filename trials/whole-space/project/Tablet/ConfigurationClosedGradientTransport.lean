module

public import Tablet.ConfigurationGradientPullback
public import Tablet.ConfigurationTranslationGeometry
public import Tablet.ClosedPhysicalEnergy
public import Tablet.CollisionFreeGradientCore
public import Tablet.LawVariance
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Constructions.SumProd

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped ContDiff ENNReal
noncomputable section

-- [TABLET NODE: ConfigurationClosedGradientTransport]
theorem ConfigurationClosedGradientTransport {d N : ℕ} (a : OneParticle d)
    (P : Measure (ParticleConfig d N)) :
    let e := (ConfigurationTranslation a).toMeasurableEquiv
    let H := ConfigurationGradientPullback a P
    Set.image H (SmoothGradientCore (P.map e)) = SmoothGradientCore P ∧
    Set.image H (ClosedGradientGraph (P.map e)) = ClosedGradientGraph P ∧
    Set.image H (CollisionFreeGradientCore (P.map e)) = CollisionFreeGradientCore P ∧
    Set.image H (closure (CollisionFreeGradientCore (P.map e))) = closure (CollisionFreeGradientCore P) ∧
    (∀ q : Lp ℝ 2 (P.map e) × Lp (ParticleConfig d N) 2 (P.map e),
      LawVariance P (H q).1 = LawVariance (P.map e) q.1 ∧
      ClosedPhysicalEnergy (H q) = ClosedPhysicalEnergy q) := by
-- BODY
  have configShift_symm_apply (a : OneParticle d) (X : ParticleConfig d N) :
      (ConfigurationTranslation a).toMeasurableEquiv.symm X =
        X + (WithLp.toLp 2 (fun ik : Fin N × Fin d => a ik.2) : ParticleConfig d N) := by
    change X + -(-((WithLp.toLp 2 (fun ik : Fin N × Fin d => a ik.2)) : ParticleConfig d N)) = _
    rw [neg_neg]
  have collision_shift (a : OneParticle d) (X : ParticleConfig d N) :
      (ConfigurationTranslation a).toMeasurableEquiv X ∈ CollisionSet d N ↔ X ∈ CollisionSet d N :=
    (ConfigurationTranslationGeometry a 0 0 0).1 X
  have EuclideanGradient_configShift (a : OneParticle d)
      (f : ParticleConfig d N → ℝ) (X : ParticleConfig d N) :
      EuclideanGradient (fun Y => f ((ConfigurationTranslation a).toMeasurableEquiv Y)) X =
        EuclideanGradient f ((ConfigurationTranslation a).toMeasurableEquiv X) :=
    (ConfigurationTranslationGeometry a 0 0 0).2.2.2.1 f X
  have EuclideanGradient_configShift_symm (a : OneParticle d)
      (f : ParticleConfig d N → ℝ) (X : ParticleConfig d N) :
      EuclideanGradient (fun Y => f ((ConfigurationTranslation a).toMeasurableEquiv.symm Y)) X =
        EuclideanGradient f ((ConfigurationTranslation a).toMeasurableEquiv.symm X) :=
    (ConfigurationTranslationGeometry a 0 0 0).2.2.2.2 f X
  have collision_shift_symm (a : OneParticle d) (X : ParticleConfig d N) :
      ((ConfigurationTranslation a).toMeasurableEquiv).symm X ∈ CollisionSet d N ↔ X ∈ CollisionSet d N := by
    have h := collision_shift a (((ConfigurationTranslation a).toMeasurableEquiv).symm X)
    simpa only [MeasurableEquiv.apply_symm_apply] using h.symm
  have smoothCore_pullback (a : OneParticle d) (P : Measure (ParticleConfig d N))
      (q : Lp ℝ 2 (P.map ((ConfigurationTranslation a).toMeasurableEquiv)) × Lp (ParticleConfig d N) 2 (P.map ((ConfigurationTranslation a).toMeasurableEquiv)))
      (hq : q ∈ SmoothGradientCore (P.map ((ConfigurationTranslation a).toMeasurableEquiv))) :
      ConfigurationGradientPullback a P q ∈ SmoothGradientCore P := by
    obtain ⟨f, hC, hsupport, hf, hg, rfl⟩ := hq
    have hMP := ((ConfigurationTranslation a).toMeasurableEquiv).measurable.measurePreserving P
    have hf' := hf.comp_measurePreserving hMP
    have hgrad : EuclideanGradient (fun X => f ((ConfigurationTranslation a).toMeasurableEquiv X)) =
        fun X => EuclideanGradient f ((ConfigurationTranslation a).toMeasurableEquiv X) := by
      funext X
      exact EuclideanGradient_configShift a f X
    have hg' : MemLp (EuclideanGradient (fun X => f ((ConfigurationTranslation a).toMeasurableEquiv X))) 2 P := by
      rw [hgrad]
      exact hg.comp_measurePreserving hMP
    refine ⟨fun X => f ((ConfigurationTranslation a).toMeasurableEquiv X),
      hC.comp (contDiff_id.add contDiff_const),
      hsupport.comp_homeomorph (ConfigurationTranslation a), hf', hg', ?_⟩
    apply Prod.ext
    · change Lp.compMeasurePreserving ((ConfigurationTranslation a).toMeasurableEquiv) hMP (hf.toLp f) = hf'.toLp _
      exact Lp.toLp_compMeasurePreserving hf hMP
    · change Lp.compMeasurePreserving ((ConfigurationTranslation a).toMeasurableEquiv) hMP (hg.toLp (EuclideanGradient f)) = hg'.toLp _
      rw [Lp.toLp_compMeasurePreserving]
      apply MemLp.toLp_congr
      exact Eventually.of_forall (fun X => (EuclideanGradient_configShift a f X).symm)
  have smoothCore_pushforward (a : OneParticle d) (P : Measure (ParticleConfig d N))
      (q : Lp ℝ 2 P × Lp (ParticleConfig d N) 2 P) (hq : q ∈ SmoothGradientCore P) :
      (ConfigurationGradientPullback a P).symm q ∈ SmoothGradientCore (P.map ((ConfigurationTranslation a).toMeasurableEquiv)) := by
    obtain ⟨f, hC, hsupport, hf, hg, rfl⟩ := hq
    have hMP := ((ConfigurationTranslation a).toMeasurableEquiv).measurePreserving_symm P
    have hf' := hf.comp_measurePreserving hMP
    have hgrad : EuclideanGradient (fun X => f (((ConfigurationTranslation a).toMeasurableEquiv).symm X)) =
        fun X => EuclideanGradient f (((ConfigurationTranslation a).toMeasurableEquiv).symm X) := by
      funext X
      exact EuclideanGradient_configShift_symm a f X
    have hg' : MemLp (EuclideanGradient (fun X => f (((ConfigurationTranslation a).toMeasurableEquiv).symm X))) 2 (P.map ((ConfigurationTranslation a).toMeasurableEquiv)) := by
      rw [hgrad]
      exact hg.comp_measurePreserving hMP
    have hC' : ContDiff ℝ ∞ (fun X => f (((ConfigurationTranslation a).toMeasurableEquiv).symm X)) := by
      simp only [configShift_symm_apply]
      exact hC.comp (contDiff_id.add contDiff_const)
    have hs' : HasCompactSupport (fun X => f (((ConfigurationTranslation a).toMeasurableEquiv).symm X)) := by
      change HasCompactSupport (f ∘ (ConfigurationTranslation a).symm)
      exact hsupport.comp_homeomorph (ConfigurationTranslation a).symm
    refine ⟨fun X => f (((ConfigurationTranslation a).toMeasurableEquiv).symm X), hC', hs', hf', hg', ?_⟩
    apply Prod.ext
    · change Lp.compMeasurePreserving ((ConfigurationTranslation a).toMeasurableEquiv).symm hMP (hf.toLp f) = hf'.toLp _
      exact Lp.toLp_compMeasurePreserving hf hMP
    · change Lp.compMeasurePreserving ((ConfigurationTranslation a).toMeasurableEquiv).symm hMP (hg.toLp (EuclideanGradient f)) = hg'.toLp _
      rw [Lp.toLp_compMeasurePreserving]
      apply MemLp.toLp_congr
      exact Eventually.of_forall (fun X => (EuclideanGradient_configShift_symm a f X).symm)
  have smoothCore_image (a : OneParticle d) (P : Measure (ParticleConfig d N)) :
      (ConfigurationGradientPullback a P) '' SmoothGradientCore (P.map ((ConfigurationTranslation a).toMeasurableEquiv)) = SmoothGradientCore P := by
    ext q
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact smoothCore_pullback a P u hu
    · intro hq
      exact ⟨(ConfigurationGradientPullback a P).symm q, smoothCore_pushforward a P q hq,
        (ConfigurationGradientPullback a P).apply_symm_apply q⟩
  have closedGradientGraph_image (a : OneParticle d) (P : Measure (ParticleConfig d N)) :
      (ConfigurationGradientPullback a P) '' ClosedGradientGraph (P.map ((ConfigurationTranslation a).toMeasurableEquiv)) = ClosedGradientGraph P := by
    unfold ClosedGradientGraph
    rw [(ConfigurationGradientPullback a P).image_closure, smoothCore_image]
  have closedPhysicalEnergy_preserved (a : OneParticle d) (P : Measure (ParticleConfig d N))
      (q : Lp ℝ 2 (P.map ((ConfigurationTranslation a).toMeasurableEquiv)) × Lp (ParticleConfig d N) 2 (P.map ((ConfigurationTranslation a).toMeasurableEquiv))) :
      ClosedPhysicalEnergy (ConfigurationGradientPullback a P q) = ClosedPhysicalEnergy q := by
    unfold ClosedPhysicalEnergy
    change ‖L2MeasurePullback (F := ParticleConfig d N) ((ConfigurationTranslation a).toMeasurableEquiv) P q.2‖ ^ 2 = ‖q.2‖ ^ 2
    rw [LinearIsometryEquiv.norm_map]
  have graphPullback_toLp_pair (a : OneParticle d) (P : Measure (ParticleConfig d N))
      (f : ParticleConfig d N → ℝ) (hf : MemLp f 2 (P.map ((ConfigurationTranslation a).toMeasurableEquiv)))
      (hg : MemLp (EuclideanGradient f) 2 (P.map ((ConfigurationTranslation a).toMeasurableEquiv)))
      (hf' : MemLp (fun X => f ((ConfigurationTranslation a).toMeasurableEquiv X)) 2 P)
      (hg' : MemLp (EuclideanGradient (fun X => f ((ConfigurationTranslation a).toMeasurableEquiv X))) 2 P) :
      ConfigurationGradientPullback a P (hf.toLp f, hg.toLp (EuclideanGradient f)) =
        (hf'.toLp _, hg'.toLp _) := by
    have hMP := ((ConfigurationTranslation a).toMeasurableEquiv).measurable.measurePreserving P
    apply Prod.ext
    · change Lp.compMeasurePreserving ((ConfigurationTranslation a).toMeasurableEquiv) hMP (hf.toLp f) = hf'.toLp _
      rw [Lp.toLp_compMeasurePreserving]
      apply MemLp.toLp_congr
      exact Eventually.of_forall (fun _ => rfl)
    · change Lp.compMeasurePreserving ((ConfigurationTranslation a).toMeasurableEquiv) hMP (hg.toLp (EuclideanGradient f)) = hg'.toLp _
      rw [Lp.toLp_compMeasurePreserving]
      apply MemLp.toLp_congr
      exact Eventually.of_forall (fun X => (EuclideanGradient_configShift a f X).symm)
  have graphPushforward_toLp_pair (a : OneParticle d) (P : Measure (ParticleConfig d N))
      (f : ParticleConfig d N → ℝ) (hf : MemLp f 2 P) (hg : MemLp (EuclideanGradient f) 2 P)
      (hf' : MemLp (fun X => f (((ConfigurationTranslation a).toMeasurableEquiv).symm X)) 2 (P.map ((ConfigurationTranslation a).toMeasurableEquiv)))
      (hg' : MemLp (EuclideanGradient (fun X => f (((ConfigurationTranslation a).toMeasurableEquiv).symm X))) 2 (P.map ((ConfigurationTranslation a).toMeasurableEquiv))) :
      (ConfigurationGradientPullback a P).symm (hf.toLp f, hg.toLp (EuclideanGradient f)) =
        (hf'.toLp _, hg'.toLp _) := by
    have hMP := ((ConfigurationTranslation a).toMeasurableEquiv).measurePreserving_symm P
    apply Prod.ext
    · change Lp.compMeasurePreserving ((ConfigurationTranslation a).toMeasurableEquiv).symm hMP (hf.toLp f) = hf'.toLp _
      rw [Lp.toLp_compMeasurePreserving]
      apply MemLp.toLp_congr
      exact Eventually.of_forall (fun _ => rfl)
    · change Lp.compMeasurePreserving ((ConfigurationTranslation a).toMeasurableEquiv).symm hMP (hg.toLp (EuclideanGradient f)) = hg'.toLp _
      rw [Lp.toLp_compMeasurePreserving]
      apply MemLp.toLp_congr
      exact Eventually.of_forall (fun X => (EuclideanGradient_configShift_symm a f X).symm)
  have collisionFreeCore_pullback (a : OneParticle d) (P : Measure (ParticleConfig d N))
      (q : Lp ℝ 2 (P.map ((ConfigurationTranslation a).toMeasurableEquiv)) × Lp (ParticleConfig d N) 2 (P.map ((ConfigurationTranslation a).toMeasurableEquiv)))
      (hq : q ∈ CollisionFreeGradientCore (P.map ((ConfigurationTranslation a).toMeasurableEquiv))) :
      ConfigurationGradientPullback a P q ∈ CollisionFreeGradientCore P := by
    obtain ⟨f, hC, hsupport, hcollision, hf, hg, rfl⟩ := hq
    have hMP := ((ConfigurationTranslation a).toMeasurableEquiv).measurable.measurePreserving P
    have hf' := hf.comp_measurePreserving hMP
    have hgrad : EuclideanGradient (fun X => f ((ConfigurationTranslation a).toMeasurableEquiv X)) =
        fun X => EuclideanGradient f ((ConfigurationTranslation a).toMeasurableEquiv X) := by
      funext X
      exact EuclideanGradient_configShift a f X
    have hg' : MemLp (EuclideanGradient (fun X => f ((ConfigurationTranslation a).toMeasurableEquiv X))) 2 P := by
      rw [hgrad]
      exact hg.comp_measurePreserving hMP
    have hdisj : Disjoint (tsupport (fun X => f ((ConfigurationTranslation a).toMeasurableEquiv X))) (CollisionSet d N) := by
      apply Set.disjoint_left.2
      intro X hx hX
      change X ∈ tsupport (f ∘ ConfigurationTranslation a) at hx
      rw [tsupport_comp_eq_preimage f (ConfigurationTranslation a)] at hx
      exact (Set.disjoint_left.1 hcollision) hx ((collision_shift a X).2 hX)
    exact ⟨fun X => f ((ConfigurationTranslation a).toMeasurableEquiv X), hC.comp (contDiff_id.add contDiff_const),
      hsupport.comp_homeomorph (ConfigurationTranslation a), hdisj, hf', hg',
      graphPullback_toLp_pair a P f hf hg hf' hg'⟩
  have collisionFreeCore_pushforward (a : OneParticle d) (P : Measure (ParticleConfig d N))
      (q : Lp ℝ 2 P × Lp (ParticleConfig d N) 2 P) (hq : q ∈ CollisionFreeGradientCore P) :
      (ConfigurationGradientPullback a P).symm q ∈ CollisionFreeGradientCore (P.map ((ConfigurationTranslation a).toMeasurableEquiv)) := by
    obtain ⟨f, hC, hsupport, hcollision, hf, hg, rfl⟩ := hq
    have hMP := ((ConfigurationTranslation a).toMeasurableEquiv).measurePreserving_symm P
    have hf' := hf.comp_measurePreserving hMP
    have hgrad : EuclideanGradient (fun X => f (((ConfigurationTranslation a).toMeasurableEquiv).symm X)) =
        fun X => EuclideanGradient f (((ConfigurationTranslation a).toMeasurableEquiv).symm X) := by
      funext X
      exact EuclideanGradient_configShift_symm a f X
    have hg' : MemLp (EuclideanGradient (fun X => f (((ConfigurationTranslation a).toMeasurableEquiv).symm X))) 2 (P.map ((ConfigurationTranslation a).toMeasurableEquiv)) := by
      rw [hgrad]
      exact hg.comp_measurePreserving hMP
    have hC' : ContDiff ℝ ∞ (fun X => f (((ConfigurationTranslation a).toMeasurableEquiv).symm X)) := by
      simp only [configShift_symm_apply]
      exact hC.comp (contDiff_id.add contDiff_const)
    have hs' : HasCompactSupport (fun X => f (((ConfigurationTranslation a).toMeasurableEquiv).symm X)) := by
      change HasCompactSupport (f ∘ (ConfigurationTranslation a).symm)
      exact hsupport.comp_homeomorph (ConfigurationTranslation a).symm
    have hdisj : Disjoint (tsupport (fun X => f (((ConfigurationTranslation a).toMeasurableEquiv).symm X))) (CollisionSet d N) := by
      apply Set.disjoint_left.2
      intro X hx hX
      change X ∈ tsupport (f ∘ (ConfigurationTranslation a).symm) at hx
      rw [tsupport_comp_eq_preimage f (ConfigurationTranslation a).symm] at hx
      exact (Set.disjoint_left.1 hcollision) hx ((collision_shift_symm a X).2 hX)
    exact ⟨fun X => f (((ConfigurationTranslation a).toMeasurableEquiv).symm X), hC', hs', hdisj, hf', hg',
      graphPushforward_toLp_pair a P f hf hg hf' hg'⟩
  have collisionFreeCore_image (a : OneParticle d) (P : Measure (ParticleConfig d N)) :
      (ConfigurationGradientPullback a P) '' CollisionFreeGradientCore (P.map ((ConfigurationTranslation a).toMeasurableEquiv)) =
        CollisionFreeGradientCore P := by
    ext q
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact collisionFreeCore_pullback a P u hu
    · intro hq
      exact ⟨(ConfigurationGradientPullback a P).symm q, collisionFreeCore_pushforward a P q hq,
        (ConfigurationGradientPullback a P).apply_symm_apply q⟩
  have collisionFreeCore_closure_image (a : OneParticle d) (P : Measure (ParticleConfig d N)) :
      (ConfigurationGradientPullback a P) '' closure (CollisionFreeGradientCore (P.map ((ConfigurationTranslation a).toMeasurableEquiv))) =
        closure (CollisionFreeGradientCore P) := by
    rw [(ConfigurationGradientPullback a P).image_closure, collisionFreeCore_image]
  refine ⟨smoothCore_image a P, closedGradientGraph_image a P, collisionFreeCore_image a P,
    collisionFreeCore_closure_image a P, ?_⟩
  intro q
  refine ⟨?_, closedPhysicalEnergy_preserved a P q⟩
  have hcoe : ((L2MeasurePullback (ConfigurationTranslation a).toMeasurableEquiv P q.1) : ParticleConfig d N → ℝ)
      =ᵐ[P] fun X => q.1 ((ConfigurationTranslation a) X) :=
    Lp.coeFn_compMeasurePreserving q.1 ((ConfigurationTranslation a).toMeasurableEquiv.measurable.measurePreserving P)
  change ProbabilityTheory.variance (L2MeasurePullback (ConfigurationTranslation a).toMeasurableEquiv P q.1) P =
    ProbabilityTheory.variance q.1 (P.map (ConfigurationTranslation a).toMeasurableEquiv)
  rw [ProbabilityTheory.variance_congr hcoe]
  exact (ProbabilityTheory.variance_map_equiv q.1 (ConfigurationTranslation a).toMeasurableEquiv).symm
