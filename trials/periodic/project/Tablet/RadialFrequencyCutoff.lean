import Tablet.Preamble
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Data.Int.Interval
import Mathlib.Tactic
open scoped BigOperators
open Finset
-- [TABLET NODE: RadialFrequencyCutoff]
theorem RadialFrequencyCutoff (d:ℕ) (κ:ℝ) (hκ:1≤κ) :
    ∃K:Finset (Fin d→ℤ),(∀k,k∈K↔(∑j,(k j:ℝ)^2)≤κ^2) ∧
      (∀k,k∈K↔-k∈K) ∧ (0:Fin d→ℤ)∈K ∧ (K.card:ℝ)≤(5*κ)^d := by
-- BODY
  classical
  let square (d:ℕ) (k:Fin d→ℤ) : ℝ := ∑ j,(k j:ℝ)^2

  have square_nonneg (d:ℕ) (k:Fin d→ℤ) : 0≤square d k := by
    unfold square
    positivity

  have card_ball_bound (d:ℕ) (R:ℝ) (hR:1≤R) (S:Finset (Fin d→ℤ))
      (hS:∀k∈S,square d k≤R^2) : (S.card:ℝ)≤(5*R)^d := by
    classical
    let N:=⌈R⌉₊
    let B:=Fintype.piFinset (fun _:Fin d=>Finset.Icc (-(N:ℤ)) N)
    have hsub:S⊆B := by
      intro k hk
      simp only [B,Fintype.mem_piFinset,Finset.mem_Icc]
      intro j
      have hj : (k j:ℝ)^2≤square d k := by
        exact Finset.single_le_sum (fun i _=>sq_nonneg (k i:ℝ)) (Finset.mem_univ j)
      have hc : |(k j:ℝ)|≤R := by
        nlinarith [sq_abs (k j:ℝ),abs_nonneg (k j:ℝ),hS k hk]
      have hN : R≤(N:ℝ) := Nat.le_ceil R
      have habs : -(N:ℝ)≤(k j:ℝ) ∧ (k j:ℝ)≤N := by
        exact abs_le.mp (hc.trans hN)
      exact_mod_cast habs
    have hcard : B.card=(2*N+1)^d := by
      simp [B,Int.card_Icc]
      congr 1
      omega
    have hceil : (N:ℝ)<R+1 := Nat.ceil_lt_add_one (by linarith)
    calc
      (S.card:ℝ)≤(B.card:ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _=((2:ℝ)*N+1)^d := by rw [hcard];push_cast;ring
      _≤(5*R)^d := by gcongr;nlinarith

  let cutoff (d:ℕ) (κ:ℝ) : Finset (Fin d→ℤ) := by
    classical
    exact (Fintype.piFinset (fun _:Fin d=>Finset.Icc (-(⌈κ⌉₊:ℤ)) (⌈κ⌉₊:ℤ))).filter
      (fun k=>square d k≤κ^2)

  have mem_iff (d:ℕ) (κ:ℝ) (hκ:1≤κ) (k:Fin d→ℤ) :
      k∈cutoff d κ ↔ (∑j,(k j:ℝ)^2)≤κ^2 := by
    classical
    change k∈(Fintype.piFinset (fun _:Fin d=>Finset.Icc (-(⌈κ⌉₊:ℤ)) (⌈κ⌉₊:ℤ))).filter
      (fun k=>square d k≤κ^2) ↔ _
    rw [Finset.mem_filter]
    constructor
    · exact fun h=>h.2
    · intro h
      refine ⟨?_,h⟩
      simp only [Fintype.mem_piFinset,Finset.mem_Icc]
      intro j
      have hj:(k j:ℝ)^2≤∑i,(k i:ℝ)^2 :=
        Finset.single_le_sum (fun i _=>sq_nonneg (k i:ℝ)) (Finset.mem_univ j)
      have hc:|(k j:ℝ)|≤κ := by
        nlinarith [sq_abs (k j:ℝ),abs_nonneg (k j:ℝ)]
      have hN:κ≤(⌈κ⌉₊:ℝ) := Nat.le_ceil κ
      have habs:-(⌈κ⌉₊:ℝ)≤(k j:ℝ) ∧ (k j:ℝ)≤(⌈κ⌉₊:ℝ) := abs_le.mp (hc.trans hN)
      exact_mod_cast habs

  have symmetric (d:ℕ) (κ:ℝ) (hκ:1≤κ) (k:Fin d→ℤ) :
      k∈cutoff d κ ↔ -k∈cutoff d κ := by
    rw [mem_iff d κ hκ k,mem_iff d κ hκ (-k)]
    simp only [Pi.neg_apply,Int.cast_neg,neg_sq]

  have zero_mem (d:ℕ) (κ:ℝ) (hκ:1≤κ) : (0:Fin d→ℤ)∈cutoff d κ := by
    rw [mem_iff d κ hκ]
    simpa using sq_nonneg κ

  have card_bound (d:ℕ) (κ:ℝ) (hκ:1≤κ) : ((cutoff d κ).card:ℝ)≤(5*κ)^d := by
    apply card_ball_bound d κ hκ
    intro k hk
    exact (mem_iff d κ hκ k).mp hk

  exact ⟨cutoff d κ,mem_iff d κ hκ,symmetric d κ hκ,zero_mem d κ hκ,card_bound d κ hκ⟩
