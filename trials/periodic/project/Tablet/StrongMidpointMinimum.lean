module

public import Tablet.Preamble
public import Mathlib.Topology.Order.IsLUB

@[expose] public section

open Filter
open scoped Topology

-- [TABLET NODE: StrongMidpointMinimum]
theorem StrongMidpointMinimum {E : Type*} [MetricSpace E]
    (s : Set E) (F : E → ℝ) (c : ℝ) (hc : 0 < c)
    (hs : s.Nonempty) (hscomplete : IsComplete s)
    (hF : ContinuousOn F s) (hbounded : BddBelow (F '' s))
    (hmid : ∀ x ∈ s, ∀ y ∈ s, ∃ z ∈ s,
      F z ≤ (F x + F y) / 2 - c * dist x y ^ 2) :
    ∃ x ∈ s, ∀ y ∈ s, F x ≤ F y := by
-- BODY
  classical
  let a : ℝ := sInf (F '' s)
  obtain ⟨v, _, hvt, hv⟩ := exists_seq_tendsto_sInf (hs.image F) hbounded
  choose u hus huv using hv
  have hulower (n : ℕ) : a ≤ F (u n) := csInf_le hbounded ⟨u n, hus n, rfl⟩
  have hut : Tendsto (fun n => F (u n)) atTop (𝓝 a) := by
    simpa only [huv] using hvt
  have huc : CauchySeq u := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hδ : 0 < c * ε ^ 2 := mul_pos hc (sq_pos_of_pos hε)
    have he := hut.eventually (gt_mem_nhds (show a < a + c * ε ^ 2 by linarith))
    obtain ⟨N, hN⟩ := eventually_atTop.mp he
    refine ⟨N, ?_⟩
    intro m hm n hn
    obtain ⟨z, hz, hfz⟩ := hmid (u m) (hus m) (u n) (hus n)
    have hza : a ≤ F z := csInf_le hbounded ⟨z, hz, rfl⟩
    have hgap : c * dist (u m) (u n) ^ 2 < c * ε ^ 2 := by
      linarith [hN m hm, hN n hn]
    have hsquare : dist (u m) (u n) ^ 2 < ε ^ 2 := by
      by_contra hnot
      have hmul := mul_le_mul_of_nonneg_left (le_of_not_gt hnot) hc.le
      linarith
    nlinarith [dist_nonneg (x := u m) (y := u n)]
  obtain ⟨x, hx, hux⟩ := cauchySeq_tendsto_of_isComplete hscomplete hus huc
  have hft : Tendsto (fun n => F (u n)) atTop (𝓝 (F x)) :=
    (hF.continuousWithinAt hx).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hux, Filter.Eventually.of_forall hus⟩)
  have hfx : F x = a := tendsto_nhds_unique hft hut
  refine ⟨x, hx, ?_⟩
  intro y hy
  rw [hfx]
  exact csInf_le hbounded ⟨y, hy, rfl⟩
