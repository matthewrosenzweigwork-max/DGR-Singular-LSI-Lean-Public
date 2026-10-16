module

public import Tablet.LatticeRadialTailBound
public import Tablet.RieszMellinCoefficientBounds
public import Mathlib.Tactic

@[expose] public section
open scoped BigOperators
-- [TABLET NODE: RieszMellinRadialSquaredTailBound]
theorem RieszMellinRadialSquaredTailBound (d:ℕ) (s a:ℝ) (hsd:s<(d:ℝ)/2) (ha:0<a) :
    ∃ C:ℝ,0<C ∧ ∀δ ε κ:ℝ,0<δ → 0≤ε → 1≤κ →
      Summable (fun k:Fin d→ℤ=>if κ^2<∑j,(k j:ℝ)^2 then
        (RieszMellinCoefficient d s a δ ε k)^2 else 0) ∧
      (∑'k:Fin d→ℤ,if κ^2<∑j,(k j:ℝ)^2 then
        (RieszMellinCoefficient d s a δ ε k)^2 else 0)≤C*κ^(2*s-(d:ℝ)) := by
-- BODY
  classical
  let square (d:ℕ) (k:Fin d→ℤ) : ℝ := ∑ j,(k j:ℝ)^2

  have square_nonneg (d:ℕ) (k:Fin d→ℤ) : 0≤square d k := by
    unfold square
    positivity

  have dominated_squared_tail (d:ℕ) (r A:ℝ) (hr:r < -(d:ℝ)) (hA:0<A) :
      ∃ C:ℝ,0<C ∧ ∀ (c:(Fin d→ℤ)→ℝ),
        (∀k,0≤c k) → (∀k,k≠0 → c k≤A*(square d k)^(r/4)) →
        ∀κ:ℝ,1≤κ →
        Summable (fun k:Fin d→ℤ=>if κ^2<square d k then (c k)^2 else 0) ∧
        (∑'k:Fin d→ℤ,if κ^2<square d k then (c k)^2 else 0)≤C*κ^((d:ℝ)+r) := by
    classical
    obtain ⟨C,hC,hbound⟩:=LatticeRadialTailBound d r hr
    refine ⟨A^2*C,by positivity,?_⟩
    intro c hc hcap κ hκ
    let f:=fun k:Fin d→ℤ=>if κ^2<square d k then (c k)^2 else 0
    let g:=fun k:Fin d→ℤ=>if κ^2<square d k then (square d k)^(r/2) else 0
    have hf:0≤f := by intro k;dsimp [f];split_ifs <;> positivity
    have hpoint (k:Fin d→ℤ) : f k≤A^2*g k := by
      dsimp [f,g]
      split_ifs with hk
      · have hk0:k≠0 := by
          intro hz
          subst k
          have hnon:(0:ℝ)≤κ^2 := sq_nonneg κ
          have hz:κ^2<0 := by simpa [square] using hk
          linarith
        have hsq: (c k)^2≤(A*(square d k)^(r/4))^2 := by
          exact pow_le_pow_left₀ (hc k) (hcap k hk0) 2
        have he:((square d k)^(r/4))^2=(square d k)^(r/2) := by
          rw [←Real.rpow_natCast,←Real.rpow_mul (square_nonneg d k)]
          congr 1
          norm_num
          ring
        simpa only [mul_pow,he] using hsq
      · simp
    have hsum (S:Finset (Fin d→ℤ)) : ∑k∈S,f k≤(A^2*C)*κ^((d:ℝ)+r) := by
      calc
        ∑k∈S,f k≤∑k∈S,A^2*g k := Finset.sum_le_sum (fun k _=>hpoint k)
        _=A^2*∑k∈S,g k := by rw [Finset.mul_sum]
        _≤A^2*∑'k:Fin d→ℤ,g k := mul_le_mul_of_nonneg_left
          (Summable.sum_le_tsum S (fun k _=>by
            dsimp [g]
            split_ifs
            · exact Real.rpow_nonneg (square_nonneg d k) _
            · exact le_rfl)
            (hbound κ hκ).1) (sq_nonneg A)
        _≤A^2*(C*κ^((d:ℝ)+r)) := mul_le_mul_of_nonneg_left (hbound κ hκ).2 (sq_nonneg A)
        _=(A^2*C)*κ^((d:ℝ)+r) := by ring
    exact ⟨summable_of_sum_le hf hsum,Real.tsum_le_of_sum_le hf hsum⟩

  have singular_factor (d:ℕ) (s a:ℝ) (k:Fin d→ℤ) :
      a*(4*Real.pi^2*∑j,(k j:ℝ)^2)^(-((d:ℝ)-s)/2)=
        (a*(4*Real.pi^2)^(-((d:ℝ)-s)/2))*(square d k)^(-((d:ℝ)-s)/2) := by
    change a*(4*Real.pi^2*square d k)^(-((d:ℝ)-s)/2)=_
    rw [Real.mul_rpow (by positivity : (0:ℝ)≤4*Real.pi^2) (square_nonneg d k)]
    ring

  classical
  let A:=a*(4*Real.pi^2)^(-((d:ℝ)-s)/2)
  have hA:0<A := by dsimp [A];positivity
  have hr:2*s-2*(d:ℝ) < -(d:ℝ) := by linarith
  obtain ⟨C,hC,hbound⟩:=dominated_squared_tail d (2*s-2*(d:ℝ)) A hr hA
  refine ⟨C,hC,?_⟩
  intro δ ε κ hδ hε hκ
  have hsd':s<(d:ℝ) := by linarith [(Nat.cast_nonneg d : (0:ℝ)≤d)]
  have hc:=RieszMellinCoefficientBounds d s a hsd' ha δ ε hδ hε
  have hcap (k:Fin d→ℤ) (hk:k≠0) :
      RieszMellinCoefficient d s a δ ε k≤A*(square d k)^((2*s-2*(d:ℝ))/4) := by
    have h:= (hc.2.2 k).2.1
    rw [if_neg hk,singular_factor] at h
    have he : (2*s-2*(d:ℝ))/4=-((d:ℝ)-s)/2 := by ring
    rw [he]
    exact h
  have h:=hbound (RieszMellinCoefficient d s a δ ε) (fun k=>(hc.2.2 k).1) hcap κ hκ
  have he : (d:ℝ)+(2*s-2*(d:ℝ))=2*s-(d:ℝ) := by ring
  rw [he] at h
  convert! h using 1 <;> rfl

