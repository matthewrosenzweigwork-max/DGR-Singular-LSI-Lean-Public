module

public import Tablet.Preamble
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section
open scoped BigOperators ComplexConjugate
-- [TABLET NODE: SummableGramEnergyBound]
theorem SummableGramEnergyBound {ι : Type*} (N : ℕ) (hN : 1≤N)
    (w : ι → ℝ) (v : ι → Fin N → ℂ) (hw : ∀k,0≤w k) (hws : Summable w)
    (hv : ∀k i,‖v k i‖≤2) :
    -2*(∑'k,w k) ≤ (N:ℝ)⁻¹ * ∑i : Fin N,∑j : Fin N,
      if i < j then ∑'k,w k*(v k i*conj (v k j)).re else 0 := by
-- BODY
  classical
  have hscalar (f : Fin N → ℝ) :
      2*(∑ i : Fin N,∑ j : Fin N,if i < j then f i*f j else 0) +
        (∑ i : Fin N,(f i)^2) = (∑ i : Fin N,f i)^2 := by
    have hterm (i j : Fin N) : f i*f j =
        (if i < j then f i*f j else 0) +
        (if j < i then f j*f i else 0) +
        (if j=i then (f i)^2 else 0) := by
      rcases lt_trichotomy i j with h|h|h
      · simp [h,ne_of_gt h,not_lt_of_gt h]
      · subst j;simp [pow_two]
      · simp [h,ne_of_lt h,not_lt_of_gt h,mul_comm]
    have hfull : (∑ i : Fin N,∑ j : Fin N,f i*f j) = (∑ i : Fin N,f i)^2 := by
      rw [pow_two,Finset.sum_mul_sum]
    rw [←hfull]
    have hexpand : (∑ i : Fin N,∑ j : Fin N,f i*f j) =
        ∑ i : Fin N,∑ j : Fin N,
          ((if i < j then f i*f j else 0)+(if j < i then f j*f i else 0)+
          (if j=i then (f i)^2 else 0)) :=
      Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hterm i j))
    rw [hexpand]
    simp only [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j : Fin N => if j < i then f j*f i else 0)]
    simp
    ring
  let p (k : ι) := ∑i : Fin N,∑j : Fin N,
    if i < j then (v k i*conj (v k j)).re else 0
  have hrepr (k : ι) (i j : Fin N) :
      (v k i*conj (v k j)).re=(v k i).re*(v k j).re+(v k i).im*(v k j).im := by
    simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im]; ring
  have hnorm (k : ι) (i : Fin N) : (v k i).re^2+(v k i).im^2≤4 := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) (hv k i) 2
    rw [Complex.sq_norm,Complex.normSq_apply] at hh
    nlinarith
  have hdiag (k : ι) : (∑i : Fin N,((v k i).re^2+(v k i).im^2))≤4*(N:ℝ) := by
    calc
      _ ≤ ∑_ : Fin N,(4:ℝ) := Finset.sum_le_sum fun i _ => hnorm k i
      _ = _ := by simp; ring
  have hpair (k : ι) : -2*(N:ℝ)≤p k := by
    have hre := hscalar (fun i => (v k i).re)
    have him := hscalar (fun i => (v k i).im)
    have hp : p k=(∑i : Fin N,∑j : Fin N,if i < j then (v k i).re*(v k j).re else 0)+
        (∑i : Fin N,∑j : Fin N,if i < j then (v k i).im*(v k j).im else 0) := by
      dsimp [p]
      simp_rw [hrepr]
      have hite (i j : Fin N) :
          (if i < j then (v k i).re*(v k j).re+(v k i).im*(v k j).im else 0)=
          (if i < j then (v k i).re*(v k j).re else 0)+
          (if i < j then (v k i).im*(v k j).im else 0) := by split_ifs <;> ring
      simp_rw [hite,Finset.sum_add_distrib]
    have hd := hdiag k
    simp only [Finset.sum_add_distrib] at hd
    rw [hp]
    nlinarith [sq_nonneg (∑i : Fin N,(v k i).re),sq_nonneg (∑i : Fin N,(v k i).im)]
  let f (i j : Fin N) (k : ι) := if i < j then w k*(v k i*conj (v k j)).re else 0
  have hterm (i j : Fin N) : Summable (f i j) := by
    apply (hws.mul_left 4).of_norm_bounded
    intro k
    dsimp [f]
    split_ifs
    · rw [abs_mul,abs_of_nonneg (hw k)]
      have hRe : |(v k i*conj (v k j)).re|≤4 := by
        calc
          _ ≤ ‖v k i*conj (v k j)‖ := Complex.abs_re_le_norm _
          _ = ‖v k i‖*‖v k j‖ := by rw [norm_mul,Complex.norm_conj]
          _ ≤ 2*2 := mul_le_mul (hv k i) (hv k j) (norm_nonneg _) (by norm_num)
          _ = _ := by norm_num
      nlinarith [mul_le_mul_of_nonneg_left hRe (hw k)]
    · simpa using mul_nonneg (by norm_num : (0:ℝ)≤4) (hw k)
  have hfinite (s : Finset (Fin N)) (g : Fin N → ι → ℝ) (hg : ∀i,Summable (g i)) :
      Summable (fun k => ∑i∈s,g i k) := by
    induction s using Finset.induction_on with
    | empty => simpa using (summable_zero : Summable (fun _ : ι => (0:ℝ)))
    | @insert i s hi ih => simpa only [Finset.sum_insert hi] using (hg i).add ih
  have hrow (i : Fin N) : Summable (fun k => ∑j : Fin N,f i j k) :=
    hfinite Finset.univ (fun j k => f i j k) (fun j => hterm i j)
  have htotal : Summable (fun k => ∑i : Fin N,∑j : Fin N,f i j k) :=
    hfinite Finset.univ (fun i k => ∑j,f i j k) hrow
  have hfp (k : ι) : (∑i : Fin N,∑j : Fin N,f i j k)=w k*p k := by
    dsimp [f,p]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> ring
  have hswap : (∑i : Fin N,∑j : Fin N,if i < j then ∑'k,w k*(v k i*conj (v k j)).re else 0)=
      ∑'k,w k*p k := by
    have hite (i j : Fin N) : (if i < j then ∑'k,w k*(v k i*conj (v k j)).re else 0)=∑'k,f i j k := by
      dsimp [f]; split_ifs <;> simp
    simp_rw [hite]
    have hrw (i : Fin N) : (∑j : Fin N,∑'k,f i j k)=∑'k,∑j : Fin N,f i j k :=
      (Summable.tsum_finsetSum (fun j hj => hterm i j)).symm
    simp_rw [hrw]
    rw [←Summable.tsum_finsetSum (fun i hi => hrow i)]
    simp_rw [hfp]
  have hps : Summable (fun k => w k*p k) := by simpa only [hfp] using htotal
  have hbound : -2*(N:ℝ)*(∑'k,w k)≤∑'k,w k*p k := by
    calc
      _ = ∑'k,w k*(-2*(N:ℝ)) := by rw [tsum_mul_right]; ring
      _ ≤ _ := (hws.mul_right (-2*(N:ℝ))).tsum_le_tsum
        (fun k => mul_le_mul_of_nonneg_left (hpair k) (hw k)) hps
  rw [hswap]
  have hnp : (N:ℝ)≠0 := by exact_mod_cast (show N≠0 by omega)
  calc
    _ = (N:ℝ)⁻¹*(-2*(N:ℝ)*(∑'k,w k)) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr (Nat.cast_nonneg _))
