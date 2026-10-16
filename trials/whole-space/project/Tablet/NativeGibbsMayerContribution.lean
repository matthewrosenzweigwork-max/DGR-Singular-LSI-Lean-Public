module

public import Tablet.NativeGibbsTransformedL2
public import Tablet.NativeReferenceMayerOperator
public import Tablet.GibbsInsertionReference
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Tactic

@[expose] public section
open MeasureTheory Filter Set
open scoped InnerProduct ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

-- [TABLET NODE: NativeGibbsMayerContribution]
theorem NativeGibbsMayerContribution (d : ℕ) (hd : 3 ≤ d) (s B κ L M1 : ℝ)
    (hs : 0 < s) (hsd : s ≤ (d:ℝ)-2) (hB : 0 ≤ B) (hκ : 0 < κ) (hL : 1 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → ∃ a₀ : ℝ, 0 < a₀ ∧
      ∀ (V b : OneParticle d → ℝ), Continuous V → BoundedMultiplier d L b →
        (∀ x, κ/2*‖x‖^2 ≤ V x-V 0) →
        (∀ x, ‖x‖ ≤ 1 → V x-V 0 ≤ M1) →
      ∀ N : ℕ, 2 ≤ N → ∀ coupling ε : ℝ,
        0 ≤ coupling → coupling ≤ B → 0 < ε → coupling/(N:ℝ) ≤ a₀ →
      let μ := ReferenceLaw V b
      let P := GibbsLaw (N:=N) μ s coupling ε
      let U := fun (X : ParticleConfig d N) (i : Fin N) (z : OneParticle d) =>
        ∑ j ∈ Finset.univ.erase i, (coupling/(N:ℝ))*RieszKernel s ε (z-ParticlePosition X j)
      let Z := fun X i => ∫ z, Real.exp (-U X i z) ∂μ
      let J := fun i => (P.prod μ).withDensity (fun q => ENNReal.ofReal (Real.exp (-U q.1 i q.2)))
      (∀ X i, Real.exp (-(B*C)) ≤ Z X i) ∧
      ∀ f : ParticleConfig d N → ℝ, MemLp f 2 P →
        let F := fun (X : ParticleConfig d N) (i : Fin N) (z : OneParticle d) =>
          Real.exp (-U X i z)*(f (ParticleInsertion X i z)-f X)
        let M := fun X => ∑ i : Fin N, ∑ j : Fin N, if i=j then 0 else
          ∫ z, ∫ v, (1-Real.exp (-(coupling/(N:ℝ))*RieszKernel s ε (z-v)))*
            F X i z*F X j v ∂μ ∂μ
        Integrable M P ∧
          -(coupling*δ+(coupling/(N:ℝ))*C)*
            (∑ i : Fin N, ∫ q, (f (ParticleInsertion q.1 i q.2)-f q.1)^2 ∂J i) ≤
              ∫ X, M X ∂P := by
-- BODY
  classical
  have finite_remainder {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (N : ℕ) (T : H →L[ℝ] H) (r c : ℝ) (hr : 0 ≤ r) (_hc : 0 ≤ c)
      (hT : ‖T‖ ≤ c) (hlo : ∀ v, -r * ‖v‖^2 ≤ inner ℝ v (T v)) (F : Fin N → H) :
      -(N * r + c) * (∑ i, ‖F i‖ ^ 2) ≤
        (∑ i, ∑ j, if i = j then 0 else inner ℝ (F i) (T (F j))) := by
    have hnorm : ‖∑ i, F i‖ ^ 2 ≤ (N : ℝ) * ∑ i, ‖F i‖ ^ 2 := by
      calc
        _ ≤ (∑ i, ‖F i‖) ^ 2 := by gcongr; exact norm_sum_le _ _
        _ ≤ _ := by simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖F i‖)
    have hdiag (i : Fin N) : inner ℝ (F i) (T (F i)) ≤ c * ‖F i‖ ^ 2 := by
      calc
        _ ≤ ‖F i‖ * ‖T (F i)‖ := real_inner_le_norm _ _
        _ ≤ ‖F i‖ * (c * ‖F i‖) := mul_le_mul_of_nonneg_left
          ((T.le_opNorm (F i)).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))) (norm_nonneg _)
        _ = _ := by ring
    have hsum : ∑ i, inner ℝ (F i) (T (F i)) ≤ c * ∑ i, ‖F i‖ ^ 2 := by
      simpa only [Finset.mul_sum] using Finset.sum_le_sum (fun i _ => hdiag i)
    have hid : inner ℝ (∑ i, F i) (T (∑ i, F i)) =
        (∑ i, ∑ j, if i = j then 0 else inner ℝ (F i) (T (F j))) +
        ∑ i, inner ℝ (F i) (T (F i)) := by
      simp only [map_sum]
      rw [sum_inner]
      simp_rw [inner_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      have hh : (∑ j : Fin N, if i = j then inner ℝ (F i) (T (F j)) else 0) =
          inner ℝ (F i) (T (F i)) := by simp
      rw [← hh, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp_all
    have hlo' := hlo (∑ i, F i)
    have hn := mul_le_mul_of_nonpos_left hnorm (neg_nonpos.mpr hr)
    rw [hid] at hlo'
    nlinarith
  have norm_sq_toLp {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
      (f : Ω → ℝ) (hf : MemLp f 2 μ) : ‖hf.toLp f‖^2=∫ x, (f x)^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    simp [hx, RCLike.inner_apply, pow_two]
  have row_lower {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (N : ℕ) (K : Ω → Ω → ℝ) (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
      (r c : ℝ) (hr : 0 ≤ r) (hc : 0 ≤ c) (hT : ‖T‖ ≤ c)
      (hrep : ∀ g (hg : MemLp g 2 μ), T (hg.toLp g)=ᵐ[μ] fun z => ∫ v, K z v*g v ∂μ)
      (hlo : ∀ v, -r*‖v‖^2 ≤ inner ℝ v (T v))
      (F : Fin N → Ω → ℝ) (hF : ∀ i, MemLp (F i) 2 μ) :
      -((N:ℝ)*r+c)*(∑ i, ∫ z, (F i z)^2 ∂μ) ≤
        ∑ i, ∑ j, if i=j then 0 else ∫ z, ∫ v, K z v*F i z*F j v ∂μ ∂μ := by
    let v := fun i => (hF i).toLp (F i)
    have hi (i j : Fin N) : inner ℝ (v i) (T (v j)) = ∫ z, ∫ w, K z w*F i z*F j w ∂μ ∂μ := by
      rw [L2.inner_def]
      have he : (fun z => inner ℝ (v i z) (T (v j) z))=ᵐ[μ]
          fun z => F i z*(∫ w, K z w*F j w ∂μ) := by
        filter_upwards [(hF i).coeFn_toLp, hrep (F j) (hF j)] with z hz ht
        simp [v,hz,ht,RCLike.inner_apply,mul_comm]
      rw [integral_congr_ae he]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        dsimp only
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun w => by ring
    have hn (i : Fin N) : ‖v i‖^2=∫ z, (F i z)^2 ∂μ := norm_sq_toLp _ _
    have hh := finite_remainder N T r c hr hc hT hlo v
    simpa only [hi,hn] using hh
  obtain ⟨CM,hCM,hMayer⟩ := NativeReferenceMayerOperator d (by omega) s κ L M1 hs (by linarith) hκ hL
  obtain ⟨CI,hCI,hInsert⟩ := GibbsInsertionReference d hd s B κ L M1 hs hsd hB hκ hL
  obtain ⟨CR,hCR,hReference⟩ := ReferenceOffsetDensity d (by omega) s κ L M1 hs (by linarith) hκ hL
  let C := CM+CI
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro δ hδ
  obtain ⟨a₀,ha₀,hOp⟩ := hMayer δ hδ
  refine ⟨a₀,ha₀,?_⟩
  intro V b hV hb hquad hlocal N hN coupling ε hc hcB hε ha₀c
  dsimp only
  let μ := ReferenceLaw V b
  let P := GibbsLaw (N:=N) μ s coupling ε
  let a := coupling/(N:ℝ)
  let U := fun (X : ParticleConfig d N) (i : Fin N) (z : OneParticle d) =>
    ∑ j ∈ Finset.univ.erase i, a*RieszKernel s ε (z-ParticlePosition X j)
  let J := fun i => (P.prod μ).withDensity (fun q => ENNReal.ofReal (Real.exp (-U q.1 i q.2)))
  letI : IsProbabilityMeasure μ := (hReference V b hV hb hquad hlocal).2.2.1
  letI : IsProbabilityMeasure P := (SoftGibbsNormalization (N:=N) μ s coupling ε hs hc hε).2.2
  have ha : 0 ≤ a := div_nonneg hc (Nat.cast_nonneg _)
  have hMC : a*CM ≤ a*C := mul_le_mul_of_nonneg_left (by dsimp [C]; linarith) ha
  obtain ⟨T,hT,_⟩ := hOp V b hV hb hquad hlocal ε hε a ha ha₀c
  have hTbound : ‖T‖ ≤ a*C := hT.1.trans hMC
  refine ⟨?_,?_⟩
  · intro X i
    have hh := hInsert V b hV hb hquad hlocal N hN coupling ε hc hcB hε X i
    exact (Real.exp_le_exp.mpr (by dsimp [C]; nlinarith [mul_nonneg hB hCM])).trans hh.2.2.2.2.1
  · intro f hf
    let F := fun (X : ParticleConfig d N) (i : Fin N) (z : OneParticle d) =>
      Real.exp (-U X i z)*(f (ParticleInsertion X i z)-f X)
    let M := fun X => ∑ i : Fin N, ∑ j : Fin N, if i=j then 0 else
      ∫ z, ∫ v, (1-Real.exp (-a*RieszKernel s ε (z-v)))*F X i z*F X j v ∂μ ∂μ
    have ht := NativeGibbsTransformedL2 d N μ s coupling ε hs hc hε f hf
    have hQi (i : Fin N) : Integrable (fun X => ∫ z, (F X i z)^2 ∂μ) P :=
      (ht.1 i).1.integrable_sq.integral_prod_left
    have hCi (i j : Fin N) : Integrable (fun X => ∫ z, ∫ v,
        (1-Real.exp (-a*RieszKernel s ε (z-v)))*F X i z*F X j v ∂μ ∂μ) P :=
      (ht.2.2 i j).2.integral_prod_left.integral_prod_left
    have hOi (i j : Fin N) : Integrable (fun X => if i=j then (0:ℝ) else
        ∫ z, ∫ v, (1-Real.exp (-a*RieszKernel s ε (z-v)))*F X i z*F X j v ∂μ ∂μ) P := by
      split_ifs
      · exact integrable_const 0
      · exact hCi i j
    have hMi : Integrable M P := integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hOi i j))
    have hQsum := integrable_finsetSum Finset.univ (fun i _ => hQi i)
    have hpoint : ∀ᵐ X ∂P, -((N:ℝ)*(a*δ)+a*C)*(∑ i : Fin N, ∫ z, (F X i z)^2 ∂μ) ≤ M X := by
      filter_upwards [ht.2.1] with X hX
      exact row_lower μ N _ T (a*δ) (a*C) (mul_nonneg ha hδ.le) (mul_nonneg ha hC)
        hTbound hT.2.2.2 hT.2.2.1 (F X) hX
    have hint := integral_mono_ae (hQsum.const_mul (-((N:ℝ)*(a*δ)+a*C))) hMi hpoint
    rw [integral_const_mul, integral_finsetSum _ (fun i _ => hQi i)] at hint
    have htotal := Finset.sum_le_sum (fun (i : Fin N) (_ : i∈Finset.univ) => (ht.1 i).2)
    have he : (N:ℝ)*(a*δ)+a*C = coupling*δ+a*C := by
      have hNp : (N:ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
      dsimp [a]
      field_simp
    refine ⟨hMi, ?_⟩
    rw [he] at hint
    exact (mul_le_mul_of_nonpos_left htotal (neg_nonpos.mpr (add_nonneg (mul_nonneg hc hδ.le) (mul_nonneg ha hC)))).trans hint
