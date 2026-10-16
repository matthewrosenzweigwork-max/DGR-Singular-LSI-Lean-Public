import Tablet.AtomicPotential
import Tablet.TorusSobolev
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Constructions
import Mathlib.MeasureTheory.Group.Integral
open MeasureTheory
open scoped ContDiff
-- [TABLET NODE: AtomicPotentialFormBound]
theorem AtomicPotentialFormBound (d : ℕ) (B c M A θ C : ℝ)
    (hB : 0 ≤ B) (hc : 0 ≤ c) (hM : 0 ≤ M) (hA : 0 ≤ A) (hθ : 0 ≤ θ) (hC : 0 ≤ C)
    (G H : UnitAddTorus (Fin d) → ℝ) (hGs : TorusSmooth G) (hHc : Continuous H)
    (hGn : ∀ x, -c ≤ G x) (hHn : ∀ x, 0 ≤ H x)
    (hLap : ∀ x, TorusLaplacian G x = M-H x)
    (hForm : ∀ z : UnitAddTorus (Fin d), ∀ u : UnitAddTorus (Fin d) → ℝ,
      TorusSmooth u → (∫ x, max (G (x-z)) 0*(u x)^2) ≤
        A*(∫ x, ‖TorusGradient u x‖^2)+θ*(∫ x, H (x-z)*(u x)^2)+C*(∫ x, (u x)^2)) :
    ∀ (n : ℕ) (w : Fin n → ℝ) (y : Fin n → UnitAddTorus (Fin d)),
      (∀ j, 0 ≤ w j) → (∑ j, w j) ≤ B →
      let U := AtomicPotential G w y
      TorusSmooth U ∧ (∀ x, -(B*c) ≤ U x) ∧
      (∀ x, TorusLaplacian U x ≤ M*B) ∧
      (∀ x, TorusLaplacian U x = M*(∑ j, w j)-∑ j, w j*H (x-y j)) ∧
      ∀ u : UnitAddTorus (Fin d) → ℝ, TorusSmooth u →
        (∫ x, U x*(u x)^2) ≤ (B*A)*(∫ x, ‖TorusGradient u x‖^2)+
          θ*(∫ x, (M*B-TorusLaplacian U x)*(u x)^2)+(B*C)*(∫ x, (u x)^2) := by
-- BODY
  classical
  let second {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
      (H : A → ℝ) (z v : A) : ℝ := fderiv ℝ (fun y => fderiv ℝ H y v) z v
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

  let rep {d : ℕ} (x : UnitAddTorus (Fin d)) : EuclideanSpace ℝ (Fin d) :=
    WithLp.toLp 2 (fun j => (AddCircle.equivIco (1 : ℝ) 0 (x j) : ℝ))

  have lift_rep {d : ℕ} (x : UnitAddTorus (Fin d)) : TorusLift d (rep x) = x := by
    funext j
    simp [TorusLift, rep]

  have lift_sub {d : ℕ} (y z : EuclideanSpace ℝ (Fin d)) :
      TorusLift d (y-z) = TorusLift d y - TorusLift d z := by
    funext j
    simp [TorusLift, AddCircle.coe_sub]

  have smooth_translate {d : ℕ} (G : UnitAddTorus (Fin d) → ℝ)
      (hG : TorusSmooth G) (z : UnitAddTorus (Fin d)) :
      TorusSmooth (fun x => G (x-z)) := by
    have h := hG.comp (contDiff_id.sub (contDiff_const :
      ContDiff ℝ ∞ (fun _ : EuclideanSpace ℝ (Fin d) => rep z)))
    simpa only [TorusSmooth, Function.comp_def, id_eq, lift_sub, lift_rep] using h

  have lap_translate {d : ℕ} (G : UnitAddTorus (Fin d) → ℝ)
      (z x : UnitAddTorus (Fin d)) :
      TorusLaplacian (fun x => G (x-z)) x = TorusLaplacian G (x-z) := by
    have he : (fun y => G (TorusLift d y-z)) =
        fun y => G (TorusLift d (y-rep z)) := by
      funext y
      rw [lift_sub, lift_rep]
    change (∑ j : Fin d, second (fun y => G (TorusLift d y-z))
      (rep x) (EuclideanSpace.single j 1)) =
      ∑ j : Fin d, second (fun y => G (TorusLift d y)) (rep (x-z)) (EuclideanSpace.single j 1)
    rw [he]
    apply Finset.sum_congr rfl
    intro j _
    unfold second
    have hfirst : (fun y => fderiv ℝ (fun w => G (TorusLift d (w-rep z))) y
        (EuclideanSpace.single j 1)) =
        fun y => fderiv ℝ (fun w => G (TorusLift d w)) (y-rep z) (EuclideanSpace.single j 1) := by
      funext y
      exact congrArg (fun L => L (EuclideanSpace.single j 1))
        (fderiv_comp_sub (𝕜 := ℝ) (f := fun w => G (TorusLift d w)) (x := y) (rep z))
    rw [hfirst, fderiv_comp_sub (𝕜 := ℝ)
      (f := fun y => fderiv ℝ (fun w => G (TorusLift d w)) y (EuclideanSpace.single j 1))]
    exact torus_second_eq G _ _ _ (by rw [lift_sub, lift_rep, lift_rep, lift_rep])

  have lap_add_const {d : ℕ} (G : UnitAddTorus (Fin d) → ℝ) (c : ℝ) (x) :
      TorusLaplacian (fun x => G x+c) x = TorusLaplacian G x := by
    unfold TorusLaplacian
    simp_rw [fderiv_add_const]

  have lap_mul {d : ℕ} (G : UnitAddTorus (Fin d) → ℝ)
      (hG : TorusSmooth G) (b : ℝ) (x) :
      TorusLaplacian (fun x => b*G x) x = b * TorusLaplacian G x := by
    change (∑ j : Fin d, second (fun y => b*G (TorusLift d y))
      (rep x) (EuclideanSpace.single j 1)) =
      b * ∑ j : Fin d, second (fun y => G (TorusLift d y)) (rep x) (EuclideanSpace.single j 1)
    simp_rw [second_const_mul _ hG]
    exact (Finset.mul_sum _ _ _).symm

  have lap_sum {d n : ℕ} (G : Fin n → UnitAddTorus (Fin d) → ℝ)
      (hG : ∀ i, TorusSmooth (G i)) (x) :
      TorusLaplacian (fun x => ∑ i, G i x) x = ∑ i, TorusLaplacian (G i) x := by
    change (∑ j : Fin d, second (fun y => ∑ i, G i (TorusLift d y))
      (rep x) (EuclideanSpace.single j 1)) =
      ∑ i : Fin n, ∑ j : Fin d, second (fun y => G i (TorusLift d y))
        (rep x) (EuclideanSpace.single j 1)
    simp_rw [second_sum _ hG]
    exact Finset.sum_comm

  have smooth_scale {d : ℕ} (G : UnitAddTorus (Fin d) → ℝ)
      (hG : TorusSmooth G) (b : ℝ) : TorusSmooth (fun x => b*G x) :=
    contDiff_const.mul hG

  have atomic_smooth {d n : ℕ} (G : UnitAddTorus (Fin d) → ℝ)
      (hG : TorusSmooth G) (w : Fin n → ℝ) (z : Fin n → UnitAddTorus (Fin d)) :
      TorusSmooth (AtomicPotential G w z) := by
    change ContDiff ℝ ∞ (fun y => ∑ i, w i * G (TorusLift d y-z i))
    apply ContDiff.sum
    intro i _
    exact smooth_scale _ (smooth_translate G hG (z i)) (w i)

  have atomic_lap {d n : ℕ} (G : UnitAddTorus (Fin d) → ℝ)
      (hG : TorusSmooth G) (w : Fin n → ℝ) (z : Fin n → UnitAddTorus (Fin d)) (x) :
      TorusLaplacian (AtomicPotential G w z) x = ∑ i, w i * TorusLaplacian G (x-z i) := by
    unfold AtomicPotential
    rw [lap_sum _ (fun i => smooth_scale _ (smooth_translate G hG (z i)) (w i))]
    simp_rw [lap_mul _ (smooth_translate G hG _), lap_translate]

  have quotient (d : ℕ) : IsOpenQuotientMap (TorusLift d) := by
    have hc : IsOpenQuotientMap ((↑) : ℝ → AddCircle (1 : ℝ)) :=
      QuotientAddGroup.isOpenQuotientMap_mk
    have hp : IsOpenQuotientMap
        (Pi.map (fun _ : Fin d => ((↑) : ℝ → AddCircle (1 : ℝ)))) :=
      IsOpenQuotientMap.piMap (fun _ => hc)
    exact hp.comp (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isOpenQuotientMap

  have continuous {d : ℕ} {f : UnitAddTorus (Fin d) → ℝ}
      (hf : TorusSmooth f) : Continuous f := by
    apply (quotient d).continuous_comp_iff.mp
    exact hf.continuous

  intro n w y hw hmass
  let U := AtomicPotential G w y
  let S : UnitAddTorus (Fin d) → ℝ := fun x => ∑ j, w j*H (x-y j)
  have hSn : ∀ x, 0 ≤ S x := fun x => Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (hHn _)
  have hSc : Continuous S := continuous_finset_sum _ fun j _ =>
    continuous_const.mul (hHc.comp (continuous_id.sub continuous_const))
  have hEq : ∀ x, TorusLaplacian U x = M*(∑ j, w j)-S x := by
    intro x
    rw [atomic_lap G hGs w y x]
    simp_rw [hLap, mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    dsimp [S]; ring
  refine ⟨atomic_smooth G hGs w y, ?_, ?_, hEq, ?_⟩
  · intro x
    have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      mul_le_mul_of_nonneg_left (hGn (x-y j)) (hw j))
    have hBmul := mul_le_mul_of_nonneg_right hmass hc
    change -(B*c) ≤ ∑ j, w j*G (x-y j)
    rw [← Finset.sum_mul] at h
    nlinarith
  · intro x
    rw [hEq]
    have hh := mul_le_mul_of_nonneg_left hmass hM
    linarith [hSn x]
  · intro u hu
    have huc : Continuous u := continuous hu
    have hUi : ∀ j, Integrable (fun x => G (x-y j)*(u x)^2) volume := fun j =>
      ((continuous hGs).comp (continuous_id.sub continuous_const) |>.mul (huc.pow 2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hHi : ∀ j, Integrable (fun x => H (x-y j)*(u x)^2) volume := fun j =>
      (hHc.comp (continuous_id.sub continuous_const) |>.mul (huc.pow 2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hSi : Integrable (fun x => S x*(u x)^2) volume :=
      (hSc.mul (huc.pow 2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hui : Integrable (fun x => (u x)^2) volume :=
      (huc.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hraw (j : Fin n) : (∫ x, G (x-y j)*(u x)^2) ≤
        A*(∫ x, ‖TorusGradient u x‖^2)+θ*(∫ x, H (x-y j)*(u x)^2)+C*(∫ x, (u x)^2) := by
      have hmi : Integrable (fun x => max (G (x-y j)) 0*(u x)^2) volume :=
        (((continuous hGs).comp (continuous_id.sub continuous_const)).max continuous_const |>.mul (huc.pow 2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      exact (integral_mono (hUi j) hmi (fun x => mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))).trans (hForm (y j) u hu)
    have hUeq : (∫ x, U x*(u x)^2) = ∑ j, w j*(∫ x, G (x-y j)*(u x)^2) := by
      change (∫ x, (∑ j, w j*G (x-y j))*(u x)^2) = _
      simp_rw [Finset.sum_mul, mul_assoc]
      rw [integral_finsetSum _ (fun j _ => (hUi j).const_mul (w j))]
      simp_rw [integral_const_mul]
    have hSeq : (∫ x, S x*(u x)^2) = ∑ j, w j*(∫ x, H (x-y j)*(u x)^2) := by
      change (∫ x, (∑ j, w j*H (x-y j))*(u x)^2) = _
      simp_rw [Finset.sum_mul, mul_assoc]
      rw [integral_finsetSum _ (fun j _ => (hHi j).const_mul (w j))]
      simp_rw [integral_const_mul]
    have hTarget : (fun x => (M*B-TorusLaplacian U x)*(u x)^2) =
        (fun x => M*(B-∑ j, w j)*(u x)^2 + S x*(u x)^2) := by
      funext x; rw [hEq]; ring
    have hTarInt : (∫ x, (M*B-TorusLaplacian U x)*(u x)^2) =
        M*(B-∑ j, w j)*(∫ x, (u x)^2)+(∫ x, S x*(u x)^2) := by
      rw [hTarget, integral_add (hui.const_mul _) hSi, integral_const_mul]
    have hST : (∫ x, S x*(u x)^2) ≤ ∫ x, (M*B-TorusLaplacian U x)*(u x)^2 := by
      rw [hTarInt]
      exact le_add_of_nonneg_left (mul_nonneg (mul_nonneg hM (sub_nonneg.mpr hmass))
        (integral_nonneg fun x => sq_nonneg _))
    have hSum := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      mul_le_mul_of_nonneg_left (hraw j) (hw j))
    have hSumEq : (∑ j, w j*(A*(∫ x, ‖TorusGradient u x‖^2)+
        θ*(∫ x, H (x-y j)*(u x)^2)+C*(∫ x, (u x)^2))) =
        ((∑ j, w j)*A)*(∫ x, ‖TorusGradient u x‖^2)+
        θ*(∫ x, S x*(u x)^2)+((∑ j, w j)*C)*(∫ x, (u x)^2) := by
      rw [hSeq]
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
      congr 2
      all_goals first | (apply Finset.sum_congr rfl; intro j hj; ring) | (funext j; ring)
    rw [← hUeq, hSumEq] at hSum
    have hAE := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmass hA)
      (integral_nonneg (μ := volume) fun x : UnitAddTorus (Fin d) => sq_nonneg ‖TorusGradient u x‖)
    have hCZ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmass hC)
      (integral_nonneg (μ := volume) fun x : UnitAddTorus (Fin d) => sq_nonneg (u x))
    exact hSum.trans (add_le_add (add_le_add hAE (mul_le_mul_of_nonneg_left hST hθ)) hCZ)
