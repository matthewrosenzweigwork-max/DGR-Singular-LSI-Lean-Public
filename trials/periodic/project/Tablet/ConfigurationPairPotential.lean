module

public import Tablet.ConfigurationCalculus
public import Tablet.PairEnergy
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Group.Prod

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ContDiff
-- [TABLET NODE: ConfigurationPairPotential]
theorem ConfigurationPairPotential (d N : ℕ) (hN : 2 ≤ N)
    (G : UnitAddTorus (Fin d) → ℝ) (hG : TorusSmooth G)
    (hn : ∀ x, 0 ≤ G x) (M β : ℝ) (hM : 0 ≤ M) (hβ : 0 ≤ β)
    (hΔ : ∀ x, TorusLaplacian G x ≤ M) :
    let V := fun X : Configuration d N => β * PairEnergy G X
    let Vflat := fun x => V ((ConfigurationFlatten d N).symm x)
    V ∈ SmoothCore d N ∧ TorusSmooth Vflat ∧
    (∀ X, 0 ≤ V X) ∧
    (∫ X, V X ∂(MeasureTheory.volume : MeasureTheory.Measure (Configuration d N))) =
      β * ((N : ℝ) - 1) * (∫ x, G x) / 2 ∧
    (∀ X, TorusLaplacian Vflat (ConfigurationFlatten d N X) =
      2 * β / N * ∑ i : Fin N, ∑ j : Fin N,
        if i < j then TorusLaplacian G (X i - X j) else 0) ∧
    (∀ x, TorusLaplacian Vflat x ≤ β * ((N : ℝ) - 1) * M) := by
-- BODY
  classical
  let flatVector (d N : ℕ)
      (y : EuclideanSpace ℝ (Fin N × Fin d)) : EuclideanSpace ℝ (Fin (N*d)) :=
    WithLp.toLp 2 (fun k => y ((finProdFinEquiv.symm k).1,(finProdFinEquiv.symm k).2))

  have quotient_commutes (d N : ℕ) (y : EuclideanSpace ℝ (Fin N × Fin d)) :
      ConfigurationFlatten d N (ConfigurationLift d N y) = TorusLift (N*d) (flatVector d N y) := by
    rfl

  let flatLinearEquiv (d N : ℕ) :
      EuclideanSpace ℝ (Fin N × Fin d) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (N*d)) :=
    (WithLp.linearEquiv 2 ℝ (Fin N × Fin d → ℝ)).trans
      ((LinearEquiv.piCongrLeft ℝ (fun _ : Fin (N*d) => ℝ)
        (finProdFinEquiv)).trans
          (WithLp.linearEquiv 2 ℝ (Fin (N*d) → ℝ)).symm)

  let flatCLE (d N : ℕ) :
      EuclideanSpace ℝ (Fin N × Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin (N*d)) :=
    (flatLinearEquiv d N).toContinuousLinearEquiv

  have flatCLE_apply (d N : ℕ) (y : EuclideanSpace ℝ (Fin N × Fin d)) :
      flatCLE d N y = flatVector d N y := by
    ext k
    simp [flatCLE, flatLinearEquiv, flatVector, LinearEquiv.piCongrLeft]

  have quotient_inverse_commutes (d N : ℕ) (z : EuclideanSpace ℝ (Fin (N*d))) :
      ConfigurationLift d N ((flatCLE d N).symm z) =
        (ConfigurationFlatten d N).symm (TorusLift (N*d) z) := by
    apply (ConfigurationFlatten d N).injective
    rw [Equiv.apply_symm_apply, quotient_commutes]
    rw [← flatCLE_apply, ContinuousLinearEquiv.apply_symm_apply]
  
  open scoped ContDiff in

  have flatCLE_symm_single (d N : ℕ) (k : Fin (N*d)) :
      (flatCLE d N).symm (EuclideanSpace.single k 1) =
        EuclideanSpace.single ((finProdFinEquiv.symm k).1,
          (finProdFinEquiv.symm k).2) 1 := by
    ext ij
    change (Pi.single k (1 : ℝ) : Fin (N*d) → ℝ) (finProdFinEquiv ij) =
      (Pi.single ((finProdFinEquiv.symm k).1,(finProdFinEquiv.symm k).2) (1 : ℝ) : Fin N × Fin d → ℝ) ij
    have he : finProdFinEquiv ij = k ↔
        ij = ((finProdFinEquiv.symm k).1,(finProdFinEquiv.symm k).2) := by
      constructor
      · intro h
        have hh := congrArg finProdFinEquiv.symm h
        rw [Equiv.symm_apply_apply] at hh
        exact Prod.ext (congrArg Prod.fst hh) (congrArg Prod.snd hh)
      · intro h
        rw [h]
        exact finProdFinEquiv.apply_symm_apply k
    simp only [Pi.single_apply, he]

  have canonical_commutes (d N : ℕ) (X : Configuration d N) :
      flatCLE d N (WithLp.toLp 2 (fun ij =>
        (AddCircle.equivIco (1 : ℝ) 0 (X ij.1 ij.2) : ℝ))) =
      WithLp.toLp 2 (fun k =>
        (AddCircle.equivIco (1 : ℝ) 0 ((ConfigurationFlatten d N X) k) : ℝ)) := by
    rw [flatCLE_apply]
    rfl
  
  open scoped ContDiff in

  let differenceCLM {d N : ℕ} (i j : Fin N) :
      EuclideanSpace ℝ (Fin N × Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (fun k =>
        (ContinuousLinearMap.proj (i,k)).comp
          (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N × Fin d => ℝ)).toContinuousLinearMap -
        (ContinuousLinearMap.proj (j,k)).comp
          (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N × Fin d => ℝ)).toContinuousLinearMap))

  have differenceCLM_apply {d N : ℕ} (i j : Fin N)
      (y : EuclideanSpace ℝ (Fin N × Fin d)) (k : Fin d) :
      differenceCLM i j y k = y (i,k) - y (j,k) := by simp [differenceCLM]

  have difference_quotient {d N : ℕ} (i j : Fin N)
      (y : EuclideanSpace ℝ (Fin N × Fin d)) :
      TorusLift d (differenceCLM i j y) = ConfigurationLift d N y i - ConfigurationLift d N y j := by
    funext k
    simp [TorusLift, ConfigurationLift, differenceCLM_apply, AddCircle.coe_sub]

  have difference_single_left {d N : ℕ} (i j : Fin N) (hij : i ≠ j) (k : Fin d) :
      differenceCLM i j (EuclideanSpace.single (i,k) 1) = EuclideanSpace.single k 1 := by
    ext l
    simp [differenceCLM_apply, PiLp.single_apply, hij, Ne.symm hij]

  have difference_single_right {d N : ℕ} (i j : Fin N) (hij : i ≠ j) (k : Fin d) :
      differenceCLM i j (EuclideanSpace.single (j,k) 1) = -EuclideanSpace.single k 1 := by
    ext l
    simp [differenceCLM_apply, PiLp.single_apply, hij, Ne.symm hij]

  have difference_single_other {d N : ℕ} (i j a : Fin N)
      (hai : a ≠ i) (haj : a ≠ j) (k : Fin d) :
      differenceCLM i j (EuclideanSpace.single (a,k) 1) = 0 := by
    ext l
    simp [differenceCLM_apply, PiLp.single_apply, hai, haj, Ne.symm hai, Ne.symm haj]

  have difference_smooth {d N : ℕ} (i j : Fin N) (G : UnitAddTorus (Fin d) → ℝ)
      (hG : TorusSmooth G) :
      ContDiff ℝ ∞ (fun y => G (ConfigurationLift d N y i - ConfigurationLift d N y j)) := by
    have h := hG.comp (differenceCLM i j).contDiff
    simpa only [Function.comp_def, difference_quotient] using h

  have second_comp {A B : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
      [NormedAddCommGroup B] [NormedSpace ℝ B] (H : B → ℝ) (hH : ContDiff ℝ ∞ H)
      (D : A →L[ℝ] B) (z v : A) :
      fderiv ℝ (fun y => fderiv ℝ (H ∘ D) y v) z v =
        fderiv ℝ (fun y => fderiv ℝ H y (D v)) (D z) (D v) := by
    have hdH := hH.differentiable (by simp)
    have hcoeff : Differentiable ℝ (fun y => fderiv ℝ H y (D v)) :=
      (((contDiff_infty_iff_fderiv.mp hH).2).clm_apply contDiff_const).differentiable (by simp)
    have hfun : (fun y => fderiv ℝ (H ∘ D) y v) =
        (fun y => fderiv ℝ H y (D v)) ∘ D := by
      funext y
      rw [fderiv_comp y hdH.differentiableAt D.differentiableAt, D.fderiv]
      rfl
    rw [hfun, fderiv_comp z hcoeff.differentiableAt D.differentiableAt, D.fderiv]
    rfl

  have second_neg {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
      (H : A → ℝ) (z v : A) :
      fderiv ℝ (fun y => fderiv ℝ H y (-v)) z (-v) =
        fderiv ℝ (fun y => fderiv ℝ H y v) z v := by
    have hfun : (fun y => fderiv ℝ H y (-v)) = -(fun y => fderiv ℝ H y v) := by
      funext y
      simp
    rw [hfun, fderiv_neg]
    simp

  have torus_translation_eq {d : ℕ} (y z : EuclideanSpace ℝ (Fin d))
      (h : TorusLift d y = TorusLift d z) (x : EuclideanSpace ℝ (Fin d)) :
      TorusLift d (x+(z-y)) = TorusLift d x := by
    funext k
    have hk := congrFun h k
    change (y k : AddCircle (1 : ℝ)) = (z k : AddCircle (1 : ℝ)) at hk
    simp only [TorusLift, PiLp.add_apply, PiLp.sub_apply]
    rw [AddCircle.coe_add, AddCircle.coe_sub, ← hk, sub_self, add_zero]

  have torus_fderiv_eq {d : ℕ} (G : UnitAddTorus (Fin d) → ℝ)
      (y z : EuclideanSpace ℝ (Fin d)) (h : TorusLift d y = TorusLift d z) :
      fderiv ℝ (fun x => G (TorusLift d x)) y =
        fderiv ℝ (fun x => G (TorusLift d x)) z := by
    let H := fun x => G (TorusLift d x)
    have hfun : (fun x => H (x+(z-y))) = H := by
      funext x
      exact congrArg G (torus_translation_eq y z h x)
    have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := H) (x := y) (z-y)
    rw [hfun] at hd
    simpa using hd

  have torus_second_eq {d : ℕ} (G : UnitAddTorus (Fin d) → ℝ)
      (y z v : EuclideanSpace ℝ (Fin d)) (h : TorusLift d y = TorusLift d z) :
      fderiv ℝ (fun x => fderiv ℝ (fun w => G (TorusLift d w)) x v) y v =
        fderiv ℝ (fun x => fderiv ℝ (fun w => G (TorusLift d w)) x v) z v := by
    let F := fun x => fderiv ℝ (fun w => G (TorusLift d w)) x v
    have hfun : (fun x => F (x+(z-y))) = F := by
      funext x
      exact congrArg (fun L => L v)
        (torus_fderiv_eq G (x+(z-y)) x (torus_translation_eq y z h x))
    have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := F) (x := y) (z-y)
    rw [hfun] at hd
    have he := congrArg (fun L => L v) hd
    simpa [F] using he

  let second {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
      (H : A → ℝ) (z v : A) : ℝ := fderiv ℝ (fun y => fderiv ℝ H y v) z v

  let trace {ι : Type} [Fintype ι] [DecidableEq ι] (H : EuclideanSpace ℝ ι → ℝ)
      (z : EuclideanSpace ℝ ι) : ℝ := ∑ k, second H z (EuclideanSpace.single k 1)

  have second_const_mul {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
      (H : A → ℝ) (hH : ContDiff ℝ ∞ H) (b : ℝ) (z v : A) :
      second (fun y => b*H y) z v = b * second H z v := by
    have hd := hH.differentiable (by simp)
    have hc := (((contDiff_infty_iff_fderiv.mp hH).2).clm_apply
      (contDiff_const : ContDiff ℝ ∞ (fun _ : A => v))).differentiable (by simp)
    have he : (fun y => fderiv ℝ (fun x => b*H x) y v) =
        (fun y => b * fderiv ℝ H y v) := by
      funext y
      rw [fderiv_const_mul hd.differentiableAt]
      rfl
    unfold second
    rw [he, fderiv_const_mul hc.differentiableAt]
    rfl

  have second_sum {A ι : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
      [Fintype ι] (H : ι → A → ℝ) (hH : ∀ k, ContDiff ℝ ∞ (H k)) (z v : A) :
      second (fun y => ∑ k, H k y) z v = ∑ k, second (H k) z v := by
    have he : (fun y => fderiv ℝ (fun x => ∑ k, H k x) y v) =
        fun y => ∑ k, fderiv ℝ (H k) y v := by
      funext y
      have hf : (fun x => ∑ k, H k x) = ∑ k, H k := by ext x; simp
      rw [hf, fderiv_sum (fun k _ => ((hH k).differentiable (by simp)).differentiableAt)]
      simp
    unfold second
    rw [he]
    have hf : (fun y => ∑ k, fderiv ℝ (H k) y v) = ∑ k, (fun y => fderiv ℝ (H k) y v) := by ext y; simp
    rw [hf, fderiv_sum (fun k _ =>
      ((((contDiff_infty_iff_fderiv.mp (hH k)).2).clm_apply contDiff_const).differentiable
        (by simp)).differentiableAt)]
    simp

  have trace_flatten (d N : ℕ) (f : Configuration d N → ℝ)
      (hf : f ∈ SmoothCore d N) (X : Configuration d N) :
      TorusLaplacian (fun x => f ((ConfigurationFlatten d N).symm x))
        (ConfigurationFlatten d N X) =
      trace (fun y => f (ConfigurationLift d N y))
        (WithLp.toLp 2 (fun ij => (AddCircle.equivIco (1 : ℝ) 0 (X ij.1 ij.2) : ℝ))) := by
    let Q := fun y => f (ConfigurationLift d N y)
    let yX : EuclideanSpace ℝ (Fin N × Fin d) := WithLp.toLp 2
      (fun ij => (AddCircle.equivIco (1 : ℝ) 0 (X ij.1 ij.2) : ℝ))
    let yx : EuclideanSpace ℝ (Fin (N*d)) := WithLp.toLp 2
      (fun k => (AddCircle.equivIco (1 : ℝ) 0 ((ConfigurationFlatten d N X) k) : ℝ))
    have hrep : (flatCLE d N).symm yx = yX := by
      rw [← show flatCLE d N yX = yx from canonical_commutes d N X]
      exact (flatCLE d N).symm_apply_apply yX
    have hfun : (fun z => f ((ConfigurationFlatten d N).symm (TorusLift (N*d) z))) =
        Q ∘ (flatCLE d N).symm.toContinuousLinearMap := by
      funext z
      exact congrArg f (quotient_inverse_commutes d N z).symm
    change (∑ k, second (fun z => f ((ConfigurationFlatten d N).symm (TorusLift (N*d) z)))
      yx (EuclideanSpace.single k 1)) = ∑ ij, second Q yX (EuclideanSpace.single ij 1)
    simp_rw [hfun]
    unfold second
    simp_rw [second_comp Q (show ContDiff ℝ ∞ Q from hf)
      (flatCLE d N).symm.toContinuousLinearMap]
    simp only [ContinuousLinearEquiv.coe_coe, hrep, flatCLE_symm_single]
    exact finProdFinEquiv.symm.sum_comp (fun ij => second Q yX (EuclideanSpace.single ij 1))

  have trace_difference {d N : ℕ} (G : UnitAddTorus (Fin d) → ℝ)
      (hG : TorusSmooth G) (i j : Fin N) (hij : i ≠ j)
      (y : EuclideanSpace ℝ (Fin N × Fin d)) :
      trace (fun z => G (ConfigurationLift d N z i - ConfigurationLift d N z j)) y =
        2 * trace (fun w => G (TorusLift d w)) (differenceCLM i j y) := by
    let H := fun w => G (TorusLift d w)
    have hfun : (fun z => G (ConfigurationLift d N z i - ConfigurationLift d N z j)) =
        H ∘ differenceCLM i j := by
      funext z
      simp only [Function.comp_def, H, difference_quotient]
    have he (a : Fin N) (k : Fin d) :
        second (H ∘ differenceCLM i j) y (EuclideanSpace.single (a,k) 1) =
        (if a=i then second H (differenceCLM i j y) (EuclideanSpace.single k 1) else 0) +
        (if a=j then second H (differenceCLM i j y) (EuclideanSpace.single k 1) else 0) := by
      unfold second
      rw [second_comp H hG]
      by_cases hai : a=i
      · subst a
        simp [difference_single_left i j hij, hij]
      · by_cases haj : a=j
        · subst a
          simp only [difference_single_right i j hij, second_neg, if_neg (Ne.symm hij),
            if_true, zero_add]
        · simp [difference_single_other i j a hai haj, hai, haj]
    rw [hfun]
    unfold trace
    rw [Fintype.sum_prod_type]
    simp_rw [he, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    dsimp only [H]
    ring

  have trace_difference_canonical {d N : ℕ} (G : UnitAddTorus (Fin d) → ℝ)
      (hG : TorusSmooth G) (i j : Fin N) (hij : i ≠ j) (X : Configuration d N) :
      trace (fun z => G (ConfigurationLift d N z i - ConfigurationLift d N z j))
        (WithLp.toLp 2 (fun ij => (AddCircle.equivIco (1 : ℝ) 0 (X ij.1 ij.2) : ℝ))) =
        2 * TorusLaplacian G (X i-X j) := by
    rw [trace_difference G hG i j hij]
    congr 1
    unfold trace TorusLaplacian
    apply Finset.sum_congr rfl
    intro k _
    unfold second
    apply torus_second_eq
    funext l
    simp only [TorusLift, differenceCLM_apply]
    simp [AddCircle.coe_sub]

  have unitTorus_probability (d : ℕ) :
      IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := by
    haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
      rw [AddCircle.volume_eq_smul_haarAddCircle]
      simp
      infer_instance
    infer_instance

  have configuration_pair_measurePreserving (d N : ℕ) (i j : Fin N) (hij : i ≠ j) :
      MeasurePreserving (fun X : Configuration d N => (X i, X j))
        volume (volume.prod volume) := by
    haveI := unitTorus_probability d
    have hi := (iIndepFun_pi (μ := fun _ : Fin N =>
      (volume : Measure (UnitAddTorus (Fin d)))) (X := fun _ => id)
      (fun _ => aemeasurable_id)).indepFun hij
    refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), ?_⟩
    change Measure.map (fun X : Configuration d N => (X i, X j))
      (Measure.pi (fun _ : Fin N => (volume : Measure (UnitAddTorus (Fin d))))) = _
    have h := hi.map_prod_eq_prod_map_map
      (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
    simpa only [(measurePreserving_eval (fun _ : Fin N =>
      (volume : Measure (UnitAddTorus (Fin d)))) i).map_eq,
      (measurePreserving_eval (fun _ : Fin N =>
      (volume : Measure (UnitAddTorus (Fin d)))) j).map_eq] using h

  have configuration_difference_measurePreserving (d N : ℕ) (i j : Fin N) (hij : i ≠ j) :
      MeasurePreserving (fun X : Configuration d N => X i - X j) volume volume := by
    haveI := unitTorus_probability d
    have hp := configuration_pair_measurePreserving d N i j hij
    have hs : MeasurePreserving (fun p : UnitAddTorus (Fin d) × UnitAddTorus (Fin d) => p.1 - p.2)
        (volume.prod volume) volume :=
      measurePreserving_fst.comp (measurePreserving_sub_prod volume volume)
    exact hs.comp hp

  have configuration_difference_integral (d N : ℕ) (i j : Fin N) (hij : i ≠ j)
      (g : UnitAddTorus (Fin d) → ℝ) (hg : Measurable g) :
      (∫ X : Configuration d N, g (X i - X j)) = ∫ x, g x := by
    have hp := configuration_difference_measurePreserving d N i j hij
    rw [← hp.map_eq]
    exact (integral_map hp.measurable.aemeasurable hg.aestronglyMeasurable).symm

  have configuration_difference_integrable (d N : ℕ) (i j : Fin N) (hij : i ≠ j)
      (g : UnitAddTorus (Fin d) → ℝ) (hg : Measurable g)
      (hi : Integrable g volume) :
      Integrable (fun X : Configuration d N => g (X i - X j)) volume :=
    (configuration_difference_measurePreserving d N i j hij).integrable_comp
      hg.aestronglyMeasurable |>.mpr hi

  have pair_count_real (N : ℕ) :
      (∑ i : Fin N, ∑ j : Fin N, if i < j then (1 : ℝ) else 0) =
        (N : ℝ) * ((N : ℝ) - 1) / 2 := by
    have hterm (i j : Fin N) :
        (if j = i then (0 : ℝ) else 1) =
        (if i < j then 1 else 0) + (if j < i then 1 else 0) := by
      rcases lt_trichotomy i j with h | h | h
      · simp [h, ne_of_gt h, not_lt_of_gt h]
      · subst j; simp
      · simp [h, ne_of_lt h, not_lt_of_gt h]
    have hsum : (∑ i : Fin N, ∑ j : Fin N, if j = i then (0 : ℝ) else 1) =
        2 * (∑ i : Fin N, ∑ j : Fin N, if i < j then (1 : ℝ) else 0) := by
      simp_rw [hterm, Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j : Fin N => if j < i then (1 : ℝ) else 0)]
      ring
    have hrow (i : Fin N) :
        (∑ j : Fin N, if j = i then (0 : ℝ) else 1) = (N : ℝ) - 1 := by
      have hp (j : Fin N) : (if j = i then (0 : ℝ) else 1) =
          1 - (if j = i then 1 else 0) := by split_ifs <;> ring
      simp_rw [hp]
      simp [Finset.sum_sub_distrib]
    simp_rw [hrow] at hsum
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    linarith

  have pairEnergy_integrable_mean (d N : ℕ) (hN : 1 ≤ N)
      (g : UnitAddTorus (Fin d) → ℝ) (hg : Measurable g) (hi : Integrable g volume) :
      Integrable (PairEnergy (N := N) g) volume ∧
        (∫ X : Configuration d N, PairEnergy g X) =
          ((N : ℝ)-1)/2 * ∫ x, g x := by
    have hp (i j : Fin N) : Integrable
        (fun X : Configuration d N => if i < j then g (X i-X j) else 0) volume := by
      split_ifs with h
      · exact configuration_difference_integrable d N i j (ne_of_lt h) g hg hi
      · exact integrable_const 0
    have hsum : Integrable
        (fun X : Configuration d N => ∑ i : Fin N, ∑ j : Fin N,
          if i < j then g (X i-X j) else 0) volume :=
      integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hp i j))
    constructor
    · exact hsum.const_mul _
    · simp only [PairEnergy, integral_const_mul]
      rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hp i j))]
      simp_rw [integral_finset_sum _ (fun j _ => hp _ j)]
      have he (i j : Fin N) :
          (∫ X : Configuration d N, if i < j then g (X i-X j) else 0) =
          (if i < j then 1 else 0) * (∫ x, g x) := by
        by_cases h : i < j
        · simp only [h, ↓reduceIte, one_mul]
          exact configuration_difference_integral d N i j (ne_of_lt h) g hg
        · simp [h]
      simp_rw [he, ← Finset.sum_mul]
      rw [pair_count_real]
      have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
      field_simp

  have torus_smooth_continuous {d : ℕ} (G : UnitAddTorus (Fin d) → ℝ)
      (hG : TorusSmooth G) : Continuous G := by
    have hc : IsOpenQuotientMap ((↑) : ℝ → AddCircle (1 : ℝ)) :=
      QuotientAddGroup.isOpenQuotientMap_mk
    have hp : IsOpenQuotientMap
        (Pi.map (fun _ : Fin d => ((↑) : ℝ → AddCircle (1 : ℝ)))) :=
      IsOpenQuotientMap.piMap (fun _ => hc)
    have hq : IsOpenQuotientMap (TorusLift d) :=
      hp.comp (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isOpenQuotientMap
    exact hq.continuous_comp_iff.mp hG.continuous

  have potential_smooth (d N : ℕ) (G : UnitAddTorus (Fin d) → ℝ)
      (hG : TorusSmooth G) (β : ℝ) :
      (fun X : Configuration d N => β * PairEnergy G X) ∈ SmoothCore d N := by
    change ContDiff ℝ ∞ (fun y => β*((N:ℝ)⁻¹ * ∑ i : Fin N, ∑ j : Fin N,
      if i < j then G (ConfigurationLift d N y i-ConfigurationLift d N y j) else 0))
    apply contDiff_const.mul
    apply contDiff_const.mul
    apply ContDiff.sum
    intro i _
    apply ContDiff.sum
    intro j _
    by_cases hij : i<j
    · simpa only [hij, ↓reduceIte] using difference_smooth i j G hG
    · simpa only [hij, ↓reduceIte] using
        (contDiff_const : ContDiff ℝ ∞ (fun _ : EuclideanSpace ℝ (Fin N × Fin d) => (0:ℝ)))

  have potential_trace (d N : ℕ) (G : UnitAddTorus (Fin d) → ℝ)
      (hG : TorusSmooth G) (β : ℝ) (X : Configuration d N) :
      TorusLaplacian (fun x => β * PairEnergy G ((ConfigurationFlatten d N).symm x))
        (ConfigurationFlatten d N X) =
        2*β/N * ∑ i : Fin N, ∑ j : Fin N,
          if i<j then TorusLaplacian G (X i-X j) else 0 := by
    let H := fun i j (y : EuclideanSpace ℝ (Fin N × Fin d)) =>
      if i<j then G (ConfigurationLift d N y i-ConfigurationLift d N y j) else 0
    have hs (i j : Fin N) : ContDiff ℝ ∞ (H i j) := by
      by_cases hij : i<j
      · simpa only [H,hij,↓reduceIte] using difference_smooth i j G hG
      · simpa only [H,hij,↓reduceIte] using
          (contDiff_const : ContDiff ℝ ∞ (fun _ : EuclideanSpace ℝ (Fin N × Fin d) => (0:ℝ)))
    have hsrow (i : Fin N) : ContDiff ℝ ∞ (fun y => ∑ j, H i j y) :=
      ContDiff.sum (fun j _ => hs i j)
    have hsum : ContDiff ℝ ∞ (fun y => ∑ i, ∑ j, H i j y) :=
      ContDiff.sum (fun i _ => hsrow i)
    rw [trace_flatten d N _ (potential_smooth d N G hG β)]
    unfold PairEnergy trace
    change (∑ k, second (fun y => β*((N:ℝ)⁻¹ * ∑ i, ∑ j, H i j y))
      (WithLp.toLp 2 (fun ij => (AddCircle.equivIco (1 : ℝ) 0 (X ij.1 ij.2) : ℝ)))
      (EuclideanSpace.single k 1)) = _
    simp_rw [second_const_mul (fun y => (N:ℝ)⁻¹ * ∑ i, ∑ j, H i j y)
      (contDiff_const.mul hsum) β]
    simp_rw [second_const_mul (fun y => ∑ i, ∑ j, H i j y) hsum (N:ℝ)⁻¹]
    simp_rw [second_sum (fun i y => ∑ j, H i j y) hsrow]
    simp_rw [second_sum (H _) (hs _)]
    simp_rw [← Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (f := fun ij j => second (H _ j) _ (EuclideanSpace.single ij 1))]
    have ht (i j : Fin N) :
        (∑ ij, second (H i j)
          (WithLp.toLp 2 (fun ij => (AddCircle.equivIco (1 : ℝ) 0 (X ij.1 ij.2) : ℝ)))
          (EuclideanSpace.single ij 1)) =
        2 * (if i<j then TorusLaplacian G (X i-X j) else 0) := by
      by_cases hij : i<j
      · simpa only [H,hij,↓reduceIte,trace] using
          trace_difference_canonical G hG i j (ne_of_lt hij) X
      · simp [H,hij,second]
    simp_rw [ht, ← Finset.mul_sum]
    ring

  classical
  dsimp only
  let V := fun X : Configuration d N => β * PairEnergy G X
  have hV : V ∈ SmoothCore d N := potential_smooth d N G hG β
  have hGn : Continuous G := torus_smooth_continuous G hG
  have hGi : Integrable G volume :=
    hGn.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace G)
  have hm := pairEnergy_integrable_mean d N (by omega) G hGn.measurable hGi
  have hNpos : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hbound (X : Configuration d N) :
      2*β/N * (∑ i : Fin N, ∑ j : Fin N,
        if i<j then TorusLaplacian G (X i-X j) else 0) ≤ β*((N:ℝ)-1)*M := by
    have he : (∑ i : Fin N, ∑ j : Fin N,
        if i<j then TorusLaplacian G (X i-X j) else 0) ≤
      (∑ i : Fin N, ∑ j : Fin N, if i<j then (1:ℝ) else 0)*M := by
      simp_rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases hij : i<j
      · simpa only [hij,↓reduceIte,one_mul] using hΔ (X i-X j)
      · simp [hij]
    calc
      _ ≤ 2*β/N * ((∑ i : Fin N, ∑ j : Fin N, if i<j then (1:ℝ) else 0)*M) :=
        mul_le_mul_of_nonneg_left he (div_nonneg (mul_nonneg (by norm_num) hβ) hNpos.le)
      _ = _ := by rw [pair_count_real]; field_simp
  refine ⟨hV, (ConfigurationCalculus d N).2.2.2 V hV |>.1, ?_, ?_, ?_, ?_⟩
  · intro X
    apply mul_nonneg hβ
    unfold PairEnergy
    apply mul_nonneg (inv_nonneg.mpr hNpos.le)
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    split_ifs
    · exact hn _
    · exact le_rfl
  · rw [integral_const_mul, hm.2]
    ring
  · exact potential_trace d N G hG β
  · intro x
    let X := (ConfigurationFlatten d N).symm x
    have hx : ConfigurationFlatten d N X = x := Equiv.apply_symm_apply _ x
    rw [← hx, potential_trace d N G hG β X]
    exact hbound X
