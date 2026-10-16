module

public import Tablet.Preamble
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Tactic

@[expose] public section
open scoped InnerProductSpace
-- [TABLET NODE: NonnegativeOperatorGap]
theorem NonnegativeOperatorGap {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] H) (δ : ℝ) (hδ : 0 < δ)
    (hself : ∀ v w, inner ℝ v (A w) = inner ℝ (A v) w)
    (hpos : ∀ v, 0 ≤ inner ℝ v (A v))
    (hquad : ∀ v, δ * inner ℝ v (A v) ≤ ‖A v‖^2) :
    ∀ v, (∀ w, A w = 0 → inner ℝ v w = 0) →
      δ * ‖v‖^2 ≤ inner ℝ v (A v) := by
-- BODY
  intro v hv
  have hvorth : v ∈ (LinearMap.ker A.toLinearMap)ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro w hw
    exact hv w hw
  have hrange (w : H) : δ * ‖A w‖ ^ 2 ≤ inner ℝ (A w) (A (A w)) := by
    have hp := hpos (A w - δ • w)
    have hexpand : inner ℝ (A w - δ • w) (A (A w - δ • w)) =
        inner ℝ (A w) (A (A w)) - 2 * δ * ‖A w‖ ^ 2 +
          δ ^ 2 * inner ℝ w (A w) := by
      simp only [map_sub, map_smul, inner_sub_left, inner_sub_right,
        inner_smul_left, inner_smul_right, RCLike.conj_to_real]
      rw [hself w (A w), real_inner_self_eq_norm_sq]
      ring
    rw [hexpand] at hp
    have hm := mul_le_mul_of_nonneg_left (hquad w) hδ.le
    nlinarith
  have hs : A.toLinearMap.IsSymmetric := fun x y => (hself x y).symm
  have hclosure : (LinearMap.range A.toLinearMap).topologicalClosure =
      (LinearMap.ker A.toLinearMap)ᗮ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, hs.orthogonal_range]
  have hclosed : IsClosed {x : H | δ * ‖x‖ ^ 2 ≤ inner ℝ x (A x)} :=
    isClosed_le (continuous_const.mul (continuous_norm.pow 2))
      (continuous_id.inner A.continuous)
  have hincl : (LinearMap.range A.toLinearMap : Set H) ⊆
      {x : H | δ * ‖x‖ ^ 2 ≤ inner ℝ x (A x)} := by
    rintro x ⟨w, rfl⟩
    exact hrange w
  have hvclosure : v ∈ closure (LinearMap.range A.toLinearMap : Set H) := by
    rw [← Submodule.topologicalClosure_coe, hclosure]
    exact hvorth
  exact closure_minimal hincl hclosed hvclosure
