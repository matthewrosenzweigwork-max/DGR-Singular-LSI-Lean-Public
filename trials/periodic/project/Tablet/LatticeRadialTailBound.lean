module

public import Tablet.Preamble
public import Mathlib.Algebra.Module.ZLattice.Summable
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic

@[expose] public section
open scoped BigOperators
open Finset
-- [TABLET NODE: LatticeRadialTailBound]
theorem LatticeRadialTailBound (d:ℕ) (r:ℝ) (hr:r < -(d:ℝ)) :
    ∃ C:ℝ,0<C ∧ ∀κ:ℝ,1≤κ →
      Summable (fun k:Fin d→ℤ=>if κ^2<∑j,(k j:ℝ)^2 then (∑j,(k j:ℝ)^2)^(r/2) else 0) ∧
      (∑'k:Fin d→ℤ,if κ^2<∑j,(k j:ℝ)^2 then (∑j,(k j:ℝ)^2)^(r/2) else 0)≤C*κ^((d:ℝ)+r) := by
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

  have dyadic_shell_exists (κ R:ℝ) (hκ:0<κ) (hR:κ≤R) :
      ∃j:ℕ,κ*(2:ℝ)^j≤R ∧ R<κ*(2:ℝ)^(j+1) := by
    obtain ⟨j,hlo,hhi⟩:=exists_nat_pow_near ((le_div_iff₀ hκ).mpr (by simpa using hR)) (by norm_num : (1:ℝ)<2)
    refine ⟨j,?_,?_⟩
    · exact (le_div_iff₀ hκ).mp hlo |> fun h=>by simpa [mul_comm] using h
    · exact (div_lt_iff₀ hκ).mp hhi |> fun h=>by simpa [mul_comm] using h

  have shell_weight_identity (d:ℕ) (r κ:ℝ) (hκ:0<κ) (j:ℕ) :
      (5*(κ*(2:ℝ)^(j+1)))^d*(κ*(2:ℝ)^j)^r =
        (10:ℝ)^d*κ^((d:ℝ)+r)*((2:ℝ)^((d:ℝ)+r))^j := by
    rw [pow_succ,Real.mul_rpow hκ.le (by positivity)]
    have hκpow : κ^d*κ^r=κ^((d:ℝ)+r) := by
      rw [←Real.rpow_natCast,←Real.rpow_add hκ]
    have h2pow : ((2:ℝ)^j)^d*((2:ℝ)^j)^r=((2:ℝ)^((d:ℝ)+r))^j := by
      rw [←Real.rpow_natCast,←Real.rpow_add (by positivity),←Real.rpow_pow_comm (by norm_num)]
    calc
      (5*(κ*((2:ℝ)^j*2)))^d*(κ^r*((2:ℝ)^j)^r) =
        (10:ℝ)^d*(κ^d*κ^r)*(((2:ℝ)^j)^d*((2:ℝ)^j)^r) := by
          simp only [mul_pow]
          rw [show (10:ℝ)=(5:ℝ)*2 by norm_num,mul_pow]
          ring
      _ = _ := by rw [hκpow,h2pow]

  have finite_tail_bound (d:ℕ) (r κ:ℝ) (hr:r < -(d:ℝ)) (hκ:1≤κ)
      (S:Finset (Fin d→ℤ)) (hS:∀k∈S,κ^2<square d k) :
      ∑k∈S,(square d k)^(r/2) ≤
        (10:ℝ)^d*κ^((d:ℝ)+r)*(1-(2:ℝ)^((d:ℝ)+r))⁻¹ := by
    classical
    have hκpos:0<κ := lt_of_lt_of_le (by norm_num) hκ
    have hrneg:r<0 := by linarith [(Nat.cast_nonneg d : (0:ℝ)≤d)]
    have hex : ∀k:Fin d→ℤ,∃j:ℕ,κ^2<square d k →
        κ*(2:ℝ)^j≤Real.sqrt (square d k) ∧
        Real.sqrt (square d k)<κ*(2:ℝ)^(j+1) := by
      intro k
      by_cases hk:κ^2<square d k
      · obtain ⟨j,hj⟩:=dyadic_shell_exists κ (Real.sqrt (square d k)) hκpos
          ((Real.le_sqrt hκpos.le (square_nonneg d k)).mpr hk.le)
        exact ⟨j,fun _=>hj⟩
      · exact ⟨0,fun h=>False.elim (hk h)⟩
    choose index hindex using hex
    have hweight (k:Fin d→ℤ) (hk:k∈S) :
        (square d k)^(r/2)≤(κ*(2:ℝ)^index k)^r := by
      have h:=Real.rpow_le_rpow_of_nonpos (by positivity : 0<κ*(2:ℝ)^index k)
        (hindex k (hS k hk)).1 hrneg.le
      have he : (Real.sqrt (square d k))^r=(square d k)^(r/2) := by
        rw [Real.sqrt_eq_rpow,←Real.rpow_mul (square_nonneg d k)]
        congr 1
        ring
      exact he ▸ h
    have hgroup (j:ℕ) :
        ∑k∈S.filter (fun k=>index k=j),(square d k)^(r/2) ≤
          (10:ℝ)^d*κ^((d:ℝ)+r)*((2:ℝ)^((d:ℝ)+r))^j := by
      let U:=S.filter (fun k=>index k=j)
      have hU : ∀k∈U,square d k≤(κ*(2:ℝ)^(j+1))^2 := by
        intro k hk
        obtain ⟨hkm,hkj⟩:=Finset.mem_filter.mp hk
        have hhi:Real.sqrt (square d k)<κ*(2:ℝ)^(j+1) := by
          simpa [hkj] using (hindex k (hS k hkm)).2
        nlinarith [Real.sq_sqrt (square_nonneg d k),Real.sqrt_nonneg (square d k),
          (show 0<κ*(2:ℝ)^(j+1) by positivity)]
      have hR:1≤κ*(2:ℝ)^(j+1) := by
        nlinarith [one_le_pow₀ (by norm_num : (1:ℝ)≤2) (n:=j+1)]
      calc
        ∑k∈U,(square d k)^(r/2)≤∑_k∈U,(κ*(2:ℝ)^j)^r := by
          apply Finset.sum_le_sum
          intro k hk
          obtain ⟨hkm,hkj⟩:=Finset.mem_filter.mp hk
          simpa [hkj] using hweight k hkm
        _=(U.card:ℝ)*(κ*(2:ℝ)^j)^r := by simp
        _≤(5*(κ*(2:ℝ)^(j+1)))^d*(κ*(2:ℝ)^j)^r :=
          mul_le_mul_of_nonneg_right (card_ball_bound d _ hR U hU) (by positivity)
        _=_ := shell_weight_identity d r κ hκpos j
    let A:=(10:ℝ)^d*κ^((d:ℝ)+r)
    let ρ:=(2:ℝ)^((d:ℝ)+r)
    have hρpos:0<ρ := by dsimp [ρ];positivity
    have hρlt:ρ<1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have hgeom : Summable (fun j:ℕ=>A*ρ^j) :=
      (summable_geometric_of_abs_lt_one (by rw [abs_of_pos hρpos];exact hρlt)).mul_left A
    calc
      ∑k∈S,(square d k)^(r/2) =
        ∑j∈S.image index,∑k∈S.filter (fun k=>index k=j),(square d k)^(r/2) := by
          exact (Finset.sum_fiberwise_of_maps_to (fun k hk=>Finset.mem_image.mpr ⟨k,hk,rfl⟩) _).symm
      _≤∑j∈S.image index,A*ρ^j := Finset.sum_le_sum (fun j _=>hgroup j)
      _≤∑'j:ℕ,A*ρ^j := Summable.sum_le_tsum _ (fun _ _=>by dsimp [A];positivity) hgeom
      _=A*(1-ρ)⁻¹ := by
        rw [tsum_mul_left,tsum_geometric_of_abs_lt_one (by rw [abs_of_pos hρpos];exact hρlt)]

  /- A radial integer-lattice tail with the sharp dimensional decay exponent. -/
  have tsum_tail_bound (d:ℕ) (r:ℝ) (hr:r < -(d:ℝ)) :
      ∃ C:ℝ,0<C ∧ ∀κ:ℝ,1≤κ →
        Summable (fun k:Fin d→ℤ=>if κ^2<square d k then (square d k)^(r/2) else 0) ∧
        (∑'k:Fin d→ℤ,if κ^2<square d k then (square d k)^(r/2) else 0)≤C*κ^((d:ℝ)+r) := by
    classical
    let C:=(10:ℝ)^d*(1-(2:ℝ)^((d:ℝ)+r))⁻¹
    have hρ : (2:ℝ)^((d:ℝ)+r)<1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have hC:0<C := by dsimp [C];positivity
    refine ⟨C,hC,?_⟩
    intro κ hκ
    let f:=fun k:Fin d→ℤ=>if κ^2<square d k then (square d k)^(r/2) else 0
    have hf:0≤f := by
      intro k
      dsimp [f]
      split_ifs
      · exact Real.rpow_nonneg (square_nonneg d k) _
      · exact le_rfl
    have hsum (S:Finset (Fin d→ℤ)) : ∑k∈S,f k≤C*κ^((d:ℝ)+r) := by
      calc
        ∑k∈S,f k=∑k∈S.filter (fun k=>κ^2<square d k),(square d k)^(r/2) := by
          rw [Finset.sum_filter]
        _≤(10:ℝ)^d*κ^((d:ℝ)+r)*(1-(2:ℝ)^((d:ℝ)+r))⁻¹ :=
          finite_tail_bound d r κ hr hκ _ (fun k hk=>(Finset.mem_filter.mp hk).2)
        _=C*κ^((d:ℝ)+r) := by dsimp [C];ring
    exact ⟨summable_of_sum_le hf hsum,Real.tsum_le_of_sum_le hf hsum⟩

  exact tsum_tail_bound d r hr
