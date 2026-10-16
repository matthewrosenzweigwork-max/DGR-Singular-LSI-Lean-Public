module

public import Tablet.NativeGibbsJumpOperator
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Tactic

@[expose] public section
open MeasureTheory Filter Set
open scoped InnerProduct ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

-- [TABLET NODE: NativeGibbsJumpKernel]
theorem NativeGibbsJumpKernel (d N : ℕ) (μ : Measure (OneParticle d))
    [IsProbabilityMeasure μ] (s coupling ε : ℝ) (hs : 0 < s) (hc : 0 ≤ coupling) (hε : 0 < ε) :
    let P := GibbsLaw (N:=N) μ s coupling ε
    let U := fun (X : ParticleConfig d N) (i : Fin N) (z : OneParticle d) =>
      ∑ j ∈ Finset.univ.erase i, (coupling/(N:ℝ))*RieszKernel s ε (z-ParticlePosition X j)
    ∀ A : Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P,
      (∀ (f : ParticleConfig d N → ℝ) (hf : MemLp f 2 P),
        A (hf.toLp f) =ᵐ[P] fun X => ∑ i : Fin N, ∫ z,
          Real.exp (-U X i z)*(f X-f (ParticleInsertion X i z)) ∂μ) →
      ∀ (f : ParticleConfig d N → ℝ) (hf : MemLp f 2 P),
        A (hf.toLp f)=0 ↔ ∃ c : ℝ, ∀ᵐ X ∂P, f X=c := by
-- BODY
  classical
  have coordinate_invariance_constant {Ω : Type} [MeasurableSpace Ω] {N : ℕ}
      (μ : Measure Ω) [IsProbabilityMeasure μ] (f : (Fin N → Ω) → ℝ)
      (_hf : MemLp f 2 (Measure.pi (fun _ : Fin N => μ)))
      (hInv : ∀ i : Fin N, ∀ᵐ p ∂(Measure.pi (fun _ : Fin N => μ)).prod μ,
        f (Function.update p.1 i p.2) = f p.1) :
      ∃ c : ℝ, ∀ᵐ X ∂Measure.pi (fun _ : Fin N => μ), f X = c := by
    classical
    let C := (Fin N → Ω)
    let m := Measure.pi (fun _ : Fin N => μ)
    haveI : IsProbabilityMeasure m := inferInstance
    let mix := fun (s : Finset (Fin N)) (X Y : C) (j : Fin N) =>
      if j ∈ s then Y j else X j
    let S := fun s (v : C × C) => (mix s v.1 v.2, mix s v.2 v.1)
    have mp (s : Finset (Fin N)) : MeasurePreserving (S s) (m.prod m) (m.prod m) := by
      let swap : Fin N ⊕ Fin N → Fin N ⊕ Fin N := fun j => match j with
        | Sum.inl i => if i ∈ s then Sum.inr i else Sum.inl i
        | Sum.inr i => if i ∈ s then Sum.inl i else Sum.inr i
      have hinvol : Function.Involutive swap := by
        intro j
        cases j with
        | inl i => by_cases h : i ∈ s <;> simp [swap, h]
        | inr i => by_cases h : i ∈ s <;> simp [swap, h]
      let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin N ⊕ Fin N => Ω)
      let a := MeasurableEquiv.piCongrLeft (fun _ : Fin N ⊕ Fin N => Ω)
        (hinvol.toPerm swap)
      have he : MeasurePreserving e.symm (m.prod m)
          (Measure.pi (fun _ : Fin N ⊕ Fin N => μ)) :=
        measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin N ⊕ Fin N => μ)
      have ha : MeasurePreserving a (Measure.pi (fun _ : Fin N ⊕ Fin N => μ))
          (Measure.pi (fun _ : Fin N ⊕ Fin N => μ)) := measurePreserving_piCongrLeft (fun _ : Fin N ⊕ Fin N => μ) _
      have h := ((MeasurePreserving.symm e.symm he).comp ha).comp he
      convert h using 1
      funext v
      apply Prod.ext <;> funext j
      · change mix s v.1 v.2 j = a (e.symm v) (Sum.inl j)
        rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
        by_cases hjs : j ∈ s <;> simp [mix, swap, Function.Involutive.toPerm, e, hjs] <;> rfl
      · change mix s v.2 v.1 j = a (e.symm v) (Sum.inr j)
        rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
        by_cases hjs : j ∈ s <;> simp [mix, swap, Function.Involutive.toPerm, e, hjs] <;> rfl
    have hmix (s : Finset (Fin N)) : ∀ᵐ v ∂m.prod m,
        f (mix s v.1 v.2) = f v.1 := by
      induction s using Finset.induction_on with
      | empty => exact Filter.Eventually.of_forall (fun v => by simp [mix])
      | @insert i s hi ih =>
        have heval : MeasurePreserving (fun v : C × C => (v.1, v.2 i))
            (m.prod m) (m.prod μ) := by
          exact (MeasurePreserving.id m).prod (measurePreserving_eval (fun _ : Fin N =>
            μ) i)
        have hj := ((heval.comp (mp s)).quasiMeasurePreserving.ae (hInv i))
        filter_upwards [ih, hj] with v h hstep
        change f (Function.update (mix s v.1 v.2) i (mix s v.2 v.1 i)) =
          f (mix s v.1 v.2) at hstep
        have hu : Function.update (mix s v.1 v.2) i (mix s v.2 v.1 i) =
            mix (insert i s) v.1 v.2 := by
          funext j
          by_cases hj : j = i
          · subst j
            simp [Function.update, mix, hi]
          · simp [Function.update, mix, hj]
        rw [hu] at hstep
        exact hstep.trans h
    have hpair : ∀ᵐ v ∂m.prod m, f v.2 = f v.1 := by
      simpa [mix] using hmix Finset.univ
    obtain ⟨X, hX⟩ := (Measure.ae_ae_of_ae_prod hpair).exists
    exact ⟨f X, hX⟩
  dsimp only
  let P := GibbsLaw (N:=N) μ s coupling ε
  let Q := ConfigurationReference d N μ
  let m := Measure.pi (fun _ : Fin N => μ)
  let U := fun (X : ParticleConfig d N) (i : Fin N) (z : OneParticle d) =>
    ∑ j ∈ Finset.univ.erase i, (coupling/(N:ℝ))*RieszKernel s ε (z-ParticlePosition X j)
  let r := fun i (q : ParticleConfig d N × OneParticle d) => Real.exp (-U q.1 i q.2)
  let J := fun i => (P.prod μ).withDensity (fun q => ENNReal.ofReal (r i q))
  let delta (f : ParticleConfig d N → ℝ) (i : Fin N) (q : ParticleConfig d N × OneParticle d) :=
    f (ParticleInsertion q.1 i q.2)-f q.1
  haveI : IsProbabilityMeasure P := (SoftGibbsNormalization μ s coupling ε hs hc hε).2.2
  haveI : IsProbabilityMeasure Q := ConfigurationReferenceProbability d N μ
  have hPc : P ≪ Q := withDensity_absolutelyContinuous _ _
  have hQc : Q ≪ P := by
    apply withDensity_absolutelyContinuous'
    · exact (((SoftInteractionRegularity (d:=d) (N:=N) s coupling ε hs hc hε).1.measurable.const_mul _).ennreal_ofReal.aemeasurable)
    · exact Eventually.of_forall fun X => ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos
        (inv_pos.mpr (SoftGibbsNormalization μ s coupling ε hs hc hε).2.1.1)
        ((SoftInteractionRegularity (d:=d) (N:=N) s coupling ε hs hc hε).2 X)))
  have hrm (i : Fin N) : Measurable (r i) := by
    have hUm : Measurable (fun q : ParticleConfig d N × OneParticle d => U q.1 i q.2) := by
      dsimp [U]; apply Finset.measurable_sum; intro j hj; apply Measurable.const_mul
      simp only [RieszKernel,ne_of_gt hε,if_false]
      unfold ParticlePosition
      fun_prop
    exact hUm.neg.exp
  have hJc (i : Fin N) : P.prod μ ≪ J i :=
    withDensity_absolutelyContinuous' (hrm i).ennreal_ofReal.aemeasurable
      (Eventually.of_forall fun q => ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))
  have hbJ (i : Fin N) := NativeGibbsReplacementBalance d N μ s coupling ε hs hc hε i
  have hinsmeas (i : Fin N) : Measurable (fun q : ParticleConfig d N × OneParticle d => ParticleInsertion q.1 i q.2) :=
    measurable_fst.comp (hbJ i).1.measurable
  have hLp (f : ParticleConfig d N → ℝ) (hf : MemLp f 2 P) (i : Fin N) : MemLp (delta f i) 2 (J i) :=
    ((hf.mono_measure (hbJ i).2.2).comp_of_map (hinsmeas i).aemeasurable).sub
      ((hf.mono_measure (hbJ i).2.1).comp_of_map measurable_fst.aemeasurable)
  let e : (Fin N → OneParticle d) ≃L[ℝ] ParticleConfig d N :=
    LinearEquiv.toContinuousLinearEquiv
      { toFun := fun Y => WithLp.toLp 2 (fun ik => Y ik.1 ik.2)
        invFun := fun X i => ParticlePosition X i
        left_inv := by intro Y; ext i k; rfl
        right_inv := by intro X; ext ik; rfl
        map_add' := by intro Y Z; ext ik; rfl
        map_smul' := by intro a Y; ext ik; rfl }
  let em := e.toHomeomorph.toMeasurableEquiv
  have hem : MeasurableEmbedding em := em.measurableEmbedding
  have hmap : m.map em=Q := rfl
  have hmp : MeasurePreserving em m Q := ⟨em.measurable,hmap⟩
  let ep := em.prodCongr (MeasurableEquiv.refl (OneParticle d))
  have hprodmap : (m.prod μ).map ep=Q.prod μ := by
    change (m.prod μ).map (Prod.map em id)=Q.prod μ
    rw [← Measure.map_prod_map m μ em.measurable measurable_id,hmap]
    simp
  have hins (Y : Fin N → OneParticle d) (i : Fin N) (z : OneParticle d) :
      em (Function.update Y i z)=ParticleInsertion (em Y) i z := by
    ext jk; rcases jk with ⟨j,k⟩; by_cases hji : j=i
    · subst j; simp [em,e,ParticleInsertion]
    · simp [em,e,ParticleInsertion,hji]
  intro A hA
  obtain ⟨A₀,hA₀,_⟩ := NativeGibbsJumpOperator d N μ s coupling ε hs hc hε
  have hAA : A=A₀ := by
    apply ContinuousLinearMap.ext; intro v; apply Lp.ext
    simpa only [Lp.toLp_coeFn] using
      (hA v (Lp.memLp v)).trans (hA₀.2.2.2.1 v (Lp.memLp v)).symm
  subst A
  intro f hf
  constructor
  · intro hz
    have hzero : (1/2:ℝ)*∑ i : Fin N,∫ q,(delta f i q)^2 ∂J i=0 := by
      rw [← hA₀.2.2.2.2.2 f hf,hz];simp
    have hsum : (∑ i : Fin N,∫ q,(delta f i q)^2 ∂J i)=0 := by linarith
    have hi (i : Fin N) : (∫ q,(delta f i q)^2 ∂J i)=0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i hi => integral_nonneg fun q => sq_nonneg _)).mp hsum i (Finset.mem_univ i)
    have hinv (i : Fin N) : ∀ᵐ q ∂Q.prod μ,f (ParticleInsertion q.1 i q.2)=f q.1 := by
      have hh := (integral_eq_zero_iff_of_nonneg (fun q => sq_nonneg (delta f i q)) (hLp f hf i).integrable_sq).mp (hi i)
      have he : ∀ᵐ q ∂J i,f (ParticleInsertion q.1 i q.2)=f q.1 :=
        hh.mono fun q hq => sub_eq_zero.mp (sq_eq_zero_iff.mp hq)
      exact (hQc.prod Measure.AbsolutelyContinuous.rfl).ae_eq ((hJc i).ae_eq he)
    let g := fun Y : Fin N → OneParticle d => Real.arctan (f (em Y))
    have hgm : AEStronglyMeasurable g m :=
      Real.continuous_arctan.comp_aestronglyMeasurable
        ((hf.aestronglyMeasurable.mono_ac hQc).comp_measurePreserving hmp)
    have hgLp : MemLp g 2 m := MemLp.of_bound hgm (Real.pi/2) (Eventually.of_forall fun Y => by
      rw [Real.norm_eq_abs];exact abs_le.mpr ⟨(Real.arctan_mem_Ioo _).1.le,(Real.arctan_mem_Ioo _).2.le⟩)
    have hgInv (i : Fin N) : ∀ᵐ q ∂m.prod μ,g (Function.update q.1 i q.2)=g q.1 := by
      have he : ∀ᵐ q ∂(m.prod μ).map ep,f (ParticleInsertion q.1 i q.2)=f q.1 := by
        rw [hprodmap];exact hinv i
      have hp := ep.measurableEmbedding.ae_map_iff.mp he
      filter_upwards [hp] with q hq
      change f (ParticleInsertion (em q.1) i q.2)=f (em q.1) at hq
      change Real.arctan (f (em (Function.update q.1 i q.2)))=Real.arctan (f (em q.1))
      rw [hins,hq]
    obtain ⟨c,hc⟩ := coordinate_invariance_constant μ g hgLp hgInv
    obtain ⟨Y₀,hY₀⟩ := hc.exists
    have hconst : ∀ᵐ Y ∂m,f (em Y)=f (em Y₀) := hc.mono fun Y hY =>
      Real.arctan_injective (hY.trans hY₀.symm)
    have hconstQ : ∀ᵐ X ∂Q,f X=f (em Y₀) := by
      rw [← hmap];exact hem.ae_map_iff.mpr hconst
    exact ⟨f (em Y₀),hPc.ae_eq hconstQ⟩
  · rintro ⟨c,hc⟩
    have hdelta (i : Fin N) : ∀ᵐ q ∂J i,delta f i q=0 := by
      have ho := ae_eq_comp measurable_fst.aemeasurable ((Measure.absolutelyContinuous_of_le (hbJ i).2.1).ae_eq hc)
      have hn := ae_eq_comp (hinsmeas i).aemeasurable ((Measure.absolutelyContinuous_of_le (hbJ i).2.2).ae_eq hc)
      filter_upwards [ho,hn] with q hq hq'
      change f q.1=c at hq
      change f (ParticleInsertion q.1 i q.2)=c at hq'
      dsimp [delta];rw [hq,hq'];ring
    apply ext_inner_left ℝ;intro w
    have hw := hA₀.2.2.2.2.1 w f (Lp.memLp w) hf
    simp only [Lp.toLp_coeFn] at hw
    rw [hw]
    have hi (i : Fin N) : (∫ q,delta (⇑w) i q*delta f i q ∂J i)=0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hdelta i] with q hq
      rw [hq,mul_zero];rfl
    change (1/2:ℝ)*(∑ i : Fin N,∫ q,delta (⇑w) i q*delta f i q ∂J i)=inner ℝ w 0
    simp only [hi,Finset.sum_const_zero,mul_zero,inner_zero_right]
