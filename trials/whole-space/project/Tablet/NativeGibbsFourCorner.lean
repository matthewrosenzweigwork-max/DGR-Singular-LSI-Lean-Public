module

public import Tablet.NativeGibbsReplacementBalance
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic

@[expose] public section
open MeasureTheory Filter Set
open scoped ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

-- [TABLET NODE: NativeGibbsFourCorner]
theorem NativeGibbsFourCorner (d N : ℕ) (μ : Measure (OneParticle d))
    [IsProbabilityMeasure μ] (s coupling ε : ℝ) (hs : 0 < s) (hc : 0 ≤ coupling) (hε : 0 < ε)
    (i j : Fin N) (hij : i ≠ j) :
    let P := GibbsLaw (N:=N) μ s coupling ε
    let a := coupling/(N:ℝ)
    let U := fun (X : ParticleConfig d N) (i : Fin N) (z : OneParticle d) =>
      ∑ k ∈ Finset.univ.erase i, a*RieszKernel s ε (z-ParticlePosition X k)
    let R := ((P.prod μ).prod μ).withDensity (fun q => ENNReal.ofReal
      (Real.exp (-U q.1.1 i q.1.2-U q.1.1 j q.2-a*RieszKernel s ε (q.1.2-q.2))))
    ∀ (f : ParticleConfig d N → ℝ), MemLp f 2 P →
      let D := fun q : (ParticleConfig d N × OneParticle d) × OneParticle d =>
        f q.1.1-f (ParticleInsertion q.1.1 i q.1.2)-f (ParticleInsertion q.1.1 j q.2)+
          f (ParticleInsertion (ParticleInsertion q.1.1 i q.1.2) j q.2)
      Integrable (fun q => (f (ParticleInsertion q.1.1 i q.1.2)-f q.1.1)*
        (f (ParticleInsertion q.1.1 j q.2)-f q.1.1)) R ∧
      Integrable (fun q => (D q)^2) R ∧
      (∫ q,(f (ParticleInsertion q.1.1 i q.1.2)-f q.1.1)*
        (f (ParticleInsertion q.1.1 j q.2)-f q.1.1) ∂R)=(1/4:ℝ)*(∫ q,(D q)^2 ∂R) ∧
      (∫ X,∫ z,∫ v,Real.exp (-a*RieszKernel s ε (z-v))*
        (Real.exp (-U X i z)*(f (ParticleInsertion X i z)-f X))*
        (Real.exp (-U X j v)*(f (ParticleInsertion X j v)-f X)) ∂μ ∂μ ∂P)=
        (1/4:ℝ)*(∫ q,(D q)^2 ∂R) ∧
      0 ≤ ∫ X,∫ z,∫ v,Real.exp (-a*RieszKernel s ε (z-v))*
        (Real.exp (-U X i z)*(f (ParticleInsertion X i z)-f X))*
        (Real.exp (-U X j v)*(f (ParticleInsertion X j v)-f X)) ∂μ ∂μ ∂P := by
-- BODY
  classical
  have preserving_integral {α : Type} [MeasurableSpace α] (J : Measure α)
      (S : α → α) (hS : MeasurePreserving S J J) (g : α → ℝ) (hg : Integrable g J) :
      (∫ x, g x ∂J)=∫ x, g (S x) ∂J := by
    have hm : AEStronglyMeasurable g (J.map S) := by rw [hS.map_eq]; exact hg.1
    have h := integral_map hS.measurable.aemeasurable hm
    simpa only [hS.map_eq] using h
  have commuting_involutions_four_corner {α : Type} [MeasurableSpace α] (J : Measure α)
      (S T : α → α) (hS : MeasurePreserving S J J) (hT : MeasurePreserving T J J)
      (hSS : ∀ x, S (S x)=x) (hTT : ∀ x, T (T x)=x)
      (hST : ∀ x, S (T x)=T (S x)) (f : α → ℝ) (hf : MemLp f 2 J) :
      Integrable (fun x => (f (S x)-f x)*(f (T x)-f x)) J ∧
      Integrable (fun x => (f x-f (S x)-f (T x)+f (S (T x)))^2) J ∧
      (∫ x, (f (S x)-f x)*(f (T x)-f x) ∂J)=
        (1/4:ℝ)*(∫ x, (f x-f (S x)-f (T x)+f (S (T x)))^2 ∂J) ∧
      0 ≤ ∫ x, (f (S x)-f x)*(f (T x)-f x) ∂J := by
    have hfS := hf.comp_measurePreserving hS
    have hfT := hf.comp_measurePreserving hT
    have hfST := hf.comp_measurePreserving (hS.comp hT)
    let g := fun x => (f (S x)-f x)*(f (T x)-f x)
    let gS := fun x => (f x-f (S x))*(f (S (T x))-f (S x))
    let gT := fun x => (f (S (T x))-f (T x))*(f x-f (T x))
    let gST := fun x => (f (T x)-f (S (T x)))*(f (S x)-f (S (T x)))
    let D := fun x => f x-f (S x)-f (T x)+f (S (T x))
    have hg : Integrable g J := (hfS.sub hf).integrable_mul (hfT.sub hf)
    have hgS : Integrable gS J := (hf.sub hfS).integrable_mul (hfST.sub hfS)
    have hgT : Integrable gT J := (hfST.sub hfT).integrable_mul (hf.sub hfT)
    have hgST : Integrable gST J := (hfT.sub hfST).integrable_mul (hfS.sub hfST)
    have hDi : Integrable (fun x => (D x)^2) J := ((hf.sub hfS).sub hfT |>.add hfST).integrable_sq
    have heS : (∫ x, g x ∂J)=∫ x, gS x ∂J := by
      rw [preserving_integral J S hS g hg]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp [g,gS]; rw [hSS,← hST]
    have heT : (∫ x, g x ∂J)=∫ x, gT x ∂J := by
      rw [preserving_integral J T hT g hg]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp [g,gT]; rw [hTT]
    have heST : (∫ x, g x ∂J)=∫ x, gST x ∂J := by
      rw [preserving_integral J (S ∘ T) (hS.comp hT) g hg]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp [g,gST,Function.comp_def]
        rw [hSS,← hST (T x),hTT]
    have hsum : (∫ x, g x ∂J)+(∫ x, gS x ∂J)+(∫ x, gT x ∂J)+(∫ x, gST x ∂J)=
        ∫ x, (D x)^2 ∂J := by
      have ha := integral_add hg hgS
      have hb := integral_add (hg.add hgS) hgT
      have hc := integral_add ((hg.add hgS).add hgT) hgST
      simp only [Pi.add_apply] at ha hb hc
      rw [← ha,← hb,← hc]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp [g,gS,gT,gST,D]; ring
    rw [← heS,← heT,← heST] at hsum
    have he : (∫ x, g x ∂J)=(1/4:ℝ)*(∫ x, (D x)^2 ∂J) := by linarith
    refine ⟨hg,hDi,he,?_⟩
    rw [he]
    exact mul_nonneg (by norm_num) (integral_nonneg fun x => sq_nonneg _)
  have density_transport {α : Type} [MeasurableSpace α] (ν η : Measure α)
      (S : α → α) (hS : MeasurePreserving S ν η) (ρ τ : α → ENNReal)
      (hτ : Measurable τ) (hρτ : ∀ x,ρ x=τ (S x)) :
      MeasurePreserving S (ν.withDensity ρ) (η.withDensity τ) := by
    refine ⟨hS.measurable,?_⟩
    apply Measure.ext;intro A hA
    rw [Measure.map_apply hS.measurable hA,withDensity_apply _ (hA.preimage hS.measurable),withDensity_apply _ hA]
    rw [← lintegral_indicator (hA.preimage hS.measurable),← lintegral_indicator hA]
    calc
      _ = ∫⁻ x,A.indicator τ (S x) ∂ν := by
        apply lintegral_congr_ae
        exact Eventually.of_forall fun x => by by_cases hx : S x ∈ A <;> simp [Set.indicator,hx,hρτ]
      _ = _ := hS.lintegral_comp (hτ.indicator hA)
  dsimp only
  let P := GibbsLaw (N:=N) μ s coupling ε
  let a := coupling/(N:ℝ)
  let U := fun (X : ParticleConfig d N) (i : Fin N) (z : OneParticle d) =>
    ∑ k ∈ Finset.univ.erase i,a*RieszKernel s ε (z-ParticlePosition X k)
  let r := fun i (q : ParticleConfig d N × OneParticle d) => Real.exp (-U q.1 i q.2)
  let J := fun i => (P.prod μ).withDensity (fun q => ENNReal.ofReal (r i q))
  let Q := (P.prod μ).prod μ
  let rate := fun i j (q : (ParticleConfig d N × OneParticle d) × OneParticle d) =>
    Real.exp (-U q.1.1 i q.1.2-U q.1.1 j q.2-a*RieszKernel s ε (q.1.2-q.2))
  let R := fun i j => Q.withDensity (fun q => ENNReal.ofReal (rate i j q))
  let S := fun i (q : (ParticleConfig d N × OneParticle d) × OneParticle d) =>
    ((ParticleInsertion q.1.1 i q.1.2,ParticlePosition q.1.1 i),q.2)
  let G := fun q : (ParticleConfig d N × OneParticle d) × OneParticle d => ((q.1.1,q.2),q.1.2)
  let T := fun j q => G (S j (G q))
  haveI : IsProbabilityMeasure P := (SoftGibbsNormalization μ s coupling ε hs hc hε).2.2
  have ha : 0 ≤ a := div_nonneg hc (Nat.cast_nonneg N)
  have hKs (x y : OneParticle d) : RieszKernel s ε (x-y)=RieszKernel s ε (y-x) := by
    have hn : ‖x-y‖=‖y-x‖ := norm_sub_rev x y
    simp only [RieszKernel,hn]
  have hUn (X : ParticleConfig d N) (i : Fin N) (z : OneParticle d) : 0 ≤ U X i z := by
    dsimp only [U];exact Finset.sum_nonneg fun k hk => mul_nonneg ha ((RieszKernelBounds s ε hs hε.le).1 _)
  have hUm (i : Fin N) : Measurable (fun q : ParticleConfig d N × OneParticle d => U q.1 i q.2) := by
    dsimp only [U];apply Finset.measurable_sum;intro k hk;apply Measurable.const_mul
    simp only [RieszKernel,ne_of_gt hε,if_false];unfold ParticlePosition;fun_prop
  have hqX : Measurable (fun q : (ParticleConfig d N × OneParticle d) × OneParticle d => q.1.1) :=
    measurable_fst.comp measurable_fst
  have hqz : Measurable (fun q : (ParticleConfig d N × OneParticle d) × OneParticle d => q.1.2) :=
    measurable_snd.comp measurable_fst
  have hqv : Measurable (fun q : (ParticleConfig d N × OneParticle d) × OneParticle d => q.2) := measurable_snd
  have hqpair : Measurable (fun q : (ParticleConfig d N × OneParticle d) × OneParticle d => q.1) := measurable_fst
  have hqkernel : Measurable (fun q : (ParticleConfig d N × OneParticle d) × OneParticle d =>
      a*RieszKernel s ε (q.1.2-q.2)) := by
    apply Measurable.const_mul
    simp only [RieszKernel,ne_of_gt hε,if_false];fun_prop
  have hratem (i j : Fin N) : Measurable (rate i j) :=
    (((hUm i).comp hqpair).neg.sub ((hUm j).comp (hqX.prodMk hqv))).sub hqkernel |>.exp
  have hrate (i j : Fin N) (q : (ParticleConfig d N × OneParticle d) × OneParticle d) :
      0 ≤ rate i j q ∧ rate i j q ≤ 1 := by
    refine ⟨Real.exp_nonneg _,Real.exp_le_one_iff.mpr ?_⟩
    have hk := mul_nonneg ha ((RieszKernelBounds s ε hs hε.le).1 (q.1.2-q.2))
    have hi := hUn q.1.1 i q.1.2;have hj := hUn q.1.1 j q.2
    linarith
  have hRle (i j : Fin N) : R i j ≤ Q := by
    have h := withDensity_mono (μ:=Q) (Eventually.of_forall fun q =>
      (ENNReal.ofReal_le_ofReal (hrate i j q).2).trans_eq ENNReal.ofReal_one)
    simpa only [R,withDensity_const,one_smul] using h
  have insert_position (X : ParticleConfig d N) (i k : Fin N) (z : OneParticle d) :
      ParticlePosition (ParticleInsertion X i z) k=if k=i then z else ParticlePosition X k := by
    ext l;by_cases hki : k=i <;> simp [ParticlePosition,ParticleInsertion,hki]
  have hinsertcomm (X : ParticleConfig d N) (i j : Fin N) (z v : OneParticle d) (hij : i ≠ j) :
      ParticleInsertion (ParticleInsertion X i z) j v=ParticleInsertion (ParticleInsertion X j v) i z := by
    ext kl;rcases kl with ⟨k,l⟩;by_cases hki : k=i <;> by_cases hkj : k=j <;>
      simp_all [ParticleInsertion]
  have hself (X : ParticleConfig d N) (i : Fin N) : ParticleInsertion X i (ParticlePosition X i)=X := by
    ext kl;rcases kl with ⟨k,l⟩;by_cases hki : k=i <;> simp_all [ParticleInsertion,ParticlePosition]
  have htwice (X : ParticleConfig d N) (i : Fin N) (z v : OneParticle d) :
      ParticleInsertion (ParticleInsertion X i z) i v=ParticleInsertion X i v := by
    ext kl;rcases kl with ⟨k,l⟩;by_cases hki : k=i <;> simp_all [ParticleInsertion]
  have hUchange (X : ParticleConfig d N) (i j : Fin N) (z v : OneParticle d) (hij : i ≠ j) :
      U (ParticleInsertion X i z) j v=U X j v-a*RieszKernel s ε (v-ParticlePosition X i)+a*RieszKernel s ε (v-z) := by
    have hi : i ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hij,Finset.mem_univ i⟩
    have hsplit := Finset.sum_erase_add (Finset.univ.erase j)
      (fun k => a*RieszKernel s ε (v-ParticlePosition X k)) hi
    have hsplit' := Finset.sum_erase_add (Finset.univ.erase j)
      (fun k => a*RieszKernel s ε (v-ParticlePosition (ParticleInsertion X i z) k)) hi
    have he : (∑ k ∈ (Finset.univ.erase j).erase i,a*RieszKernel s ε (v-ParticlePosition (ParticleInsertion X i z) k))=
        ∑ k ∈ (Finset.univ.erase j).erase i,a*RieszKernel s ε (v-ParticlePosition X k) := by
      apply Finset.sum_congr rfl;intro k hk;rw [insert_position,if_neg (Finset.mem_erase.mp hk).1]
    rw [he,insert_position,if_pos rfl] at hsplit'
    dsimp only [U];linarith only [hsplit,hsplit']
  have hS (i j : Fin N) (hij : i ≠ j) : MeasurePreserving (S i) (R i j) (R i j) := by
    let aux := fun q : (ParticleConfig d N × OneParticle d) × OneParticle d =>
      ENNReal.ofReal (Real.exp (-U q.1.1 j q.2-a*RieszKernel s ε (q.1.2-q.2)))
    have haux : Measurable aux :=
      (((hUm j).comp (hqX.prodMk hqv)).neg.sub hqkernel).exp.ennreal_ofReal
    have hriMeas : Measurable (fun q : ParticleConfig d N × OneParticle d =>
        ENNReal.ofReal (Real.exp (-U q.1 i q.2))) := by
      simpa only [Pi.neg_apply] using (hUm i).neg.exp.ennreal_ofReal
    have hfirst : Measurable (fun q : (ParticleConfig d N × OneParticle d) × OneParticle d =>
        ENNReal.ofReal (Real.exp (-U q.1.1 i q.1.2))) := hriMeas.comp hqpair
    have hbase : R i j=((J i).prod μ).withDensity aux := by
      dsimp only [R,J,r]
      rw [prod_withDensity_left hriMeas,←withDensity_mul _
        hfirst haux]
      apply withDensity_congr_ae;exact Eventually.of_forall fun q => by
        dsimp only [aux,rate,Pi.mul_apply];rw [←ENNReal.ofReal_mul (Real.exp_nonneg _),←Real.exp_add];congr 2;ring
    have hJle : J i ≤ P.prod μ := by
      have h := withDensity_mono (μ:=P.prod μ) (Eventually.of_forall fun q =>
        (ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hUn q.1 i q.2)))).trans_eq ENNReal.ofReal_one)
      simpa only [J,r,withDensity_const,one_smul] using h
    haveI : IsFiniteMeasure (J i) := isFiniteMeasure_of_le (P.prod μ) hJle
    have hmp : MeasurePreserving (S i) ((J i).prod μ) ((J i).prod μ) :=
      (NativeGibbsReplacementBalance d N μ s coupling ε hs hc hε i).1.prod (MeasurePreserving.id μ)
    rw [hbase]
    apply density_transport _ _ _ hmp aux aux haux
    intro q;dsimp only [aux,S]
    rw [hUchange _ i j _ _ hij]
    rw [hKs q.2 (ParticlePosition q.1.1 i),hKs q.2 q.1.2]
    congr 2;ring
  have hGbase : MeasurePreserving G Q Q := by
    let e : ((ParticleConfig d N × OneParticle d) × OneParticle d) ≃ᵐ
        ParticleConfig d N × (OneParticle d × OneParticle d) := MeasurableEquiv.prodAssoc
    have he : MeasurePreserving e Q (P.prod (μ.prod μ)) := measurePreserving_prodAssoc P μ μ
    have hmid : MeasurePreserving (Prod.map id Prod.swap) (P.prod (μ.prod μ)) (P.prod (μ.prod μ)) :=
      (MeasurePreserving.id P).prod Measure.measurePreserving_swap
    exact (MeasurePreserving.symm e he).comp (hmid.comp he)
  have hG (i j : Fin N) : MeasurePreserving G (R i j) (R j i) := by
    apply density_transport Q Q G hGbase _ _ (hratem j i).ennreal_ofReal
    intro q;dsimp only [rate,G];rw [hKs q.2 q.1.2];congr 2;ring
  have hT : MeasurePreserving (T j) (R i j) (R i j) := (hG j i).comp ((hS j i hij.symm).comp (hG i j))
  have hSS (q : (ParticleConfig d N × OneParticle d) × OneParticle d) : S i (S i q)=q := by
    dsimp only [S];rw [insert_position,if_pos rfl,htwice,hself]
  have hTT (q : (ParticleConfig d N × OneParticle d) × OneParticle d) : T j (T j q)=q := by
    dsimp only [T,G,S];rw [insert_position,if_pos rfl,htwice,hself]
  have hST (q : (ParticleConfig d N × OneParticle d) × OneParticle d) : S i (T j q)=T j (S i q) := by
    dsimp only [S,T,G]
    rw [insert_position,if_neg hij,insert_position,if_neg hij.symm,hinsertcomm _ i j _ _ hij]
  intro f hf
  have hproj : MeasurePreserving (fun q : (ParticleConfig d N × OneParticle d) × OneParticle d => q.1.1) Q P :=
    (measurePreserving_fst (μ:=P) (ν:=μ)).comp (measurePreserving_fst (μ:=P.prod μ) (ν:=μ))
  have hdom : (R i j).map (fun q => q.1.1) ≤ P := by
    have h := Measure.map_mono (hRle i j) hproj.measurable;rw [hproj.map_eq] at h;exact h
  have hfo : MemLp (fun q : (ParticleConfig d N × OneParticle d) × OneParticle d => f q.1.1) 2 (R i j) :=
    (hf.mono_measure hdom).comp_of_map hproj.measurable.aemeasurable
  have hh := commuting_involutions_four_corner (R i j) (S i) (T j) (hS i j hij) hT hSS hTT hST
    (fun q => f q.1.1) hfo
  dsimp only [S,T,G] at hh
  have hcomm' (X : ParticleConfig d N) (z v : OneParticle d) :
      ParticleInsertion (ParticleInsertion X j z) i v=ParticleInsertion (ParticleInsertion X i v) j z :=
    hinsertcomm X j i z v hij.symm
  simp_rw [hcomm'] at hh
  have hfin : ∀ᵐ q ∂Q,ENNReal.ofReal (rate i j q)<⊤ := Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hprod := (integrable_withDensity_iff_integrable_smul' (hratem i j).ennreal_ofReal hfin).mp hh.1
  simp only [ENNReal.toReal_ofReal (hrate i j _).1,smul_eq_mul] at hprod
  have hrows : (∫ q,(f (ParticleInsertion q.1.1 i q.1.2)-f q.1.1)*
        (f (ParticleInsertion q.1.1 j q.2)-f q.1.1) ∂R i j)=
      ∫ X,∫ z,∫ v,Real.exp (-a*RieszKernel s ε (z-v))*
        (Real.exp (-U X i z)*(f (ParticleInsertion X i z)-f X))*
        (Real.exp (-U X j v)*(f (ParticleInsertion X j v)-f X)) ∂μ ∂μ ∂P := by
    change (∫ q,_ ∂Q.withDensity _)=_
    rw [integral_withDensity_eq_integral_toReal_smul (hratem i j).ennreal_ofReal hfin]
    simp only [ENNReal.toReal_ofReal (hrate i j _).1,smul_eq_mul]
    rw [integral_prod _ hprod,integral_prod _ hprod.integral_prod_left]
    apply integral_congr_ae;exact Eventually.of_forall fun X => by
      apply integral_congr_ae;exact Eventually.of_forall fun z => by
        apply integral_congr_ae;exact Eventually.of_forall fun v => by
          dsimp only [rate];simp only [sub_eq_add_neg,Real.exp_add];ring
  refine ⟨hh.1,hh.2.1,hh.2.2.1,hrows.symm.trans hh.2.2.1,?_⟩
  rw [←hrows];exact hh.2.2.2
