module

public import Tablet.NonnegativeOperatorGap
public import Tablet.ReplacementCoercivity
public import Tablet.HeatOperatorBounds
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

@[expose] public section
open MeasureTheory Filter Set UnitAddTorus
open scoped ComplexConjugate
set_option maxHeartbeats 1500000
-- [TABLET NODE: HeatReplacementGap]
theorem HeatReplacementGap (d : ℕ) (G : UnitAddTorus (Fin d) → ℝ)
    (hG : Measurable G) (hi : MeasureTheory.Integrable G MeasureTheory.volume)
    (hn : ∀ x, 0 ≤ G x) (he : ∀ x, G (-x) = G x)
    (hF : ∀ k : Fin d → ℤ,
      0 ≤ ∫ x, G x * (UnitAddTorus.mFourier k x).re)
    (B u : ℝ) (hB : 0 ≤ B) (hu : 1 ≤ u) :
    let c := ∫ x, G x
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ ε : ℝ, 0 ≤ ε →
      let Gε := if ε = 0 then G else HeatSemigroup d ε G
      Measurable Gε ∧ MeasureTheory.Integrable Gε MeasureTheory.volume ∧
      (∀ x, 0 ≤ Gε x) ∧ (∀ x, Gε (-x) = Gε x) ∧
      (∫ x, Gε x) = c ∧
      (∀ k : Fin d → ℤ, 0 ≤ ∫ x, Gε x * (UnitAddTorus.mFourier k x).re) ∧
      ∀ (N : ℕ), N₀ ≤ N → ∀ (l β : ℝ) (q : BoundedBackground d l u),
      0 ≤ β → β ≤ B →
      ∀ (f : Configuration d N → ℝ),
      MeasureTheory.MemLp f 2 (CanonicalLaw (N := N) Gε q.density β) →
        ProbabilityTheory.variance f (CanonicalLaw (N := N) Gε q.density β) ≤
          2 * Real.exp (B * u * c) *
          (-(∫ X, f X * JumpOperator Gε q.density β f X
            ∂CanonicalLaw (N := N) Gε q.density β)) := by
-- BODY
  let conv {d : ℕ} (K : UnitAddTorus (Fin d) → ℝ) (f : UnitAddTorus (Fin d) → ℂ) :=
    fun x => ∫ y, K y • f (x-y)

  have char_add {d : ℕ} (k : Fin d → ℤ) (x y : UnitAddTorus (Fin d)) :
      mFourier k (x+y) = mFourier k x * mFourier k y := by
    simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply, smul_add,
      AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

  have char_inv {d : ℕ} (k : Fin d → ℤ) (x : UnitAddTorus (Fin d)) :
      mFourier k (-x) = conj (mFourier k x) := by
    simp only [mFourier, ContinuousMap.coe_mk, Pi.neg_apply, fourier_apply, smul_neg,
      fourier_neg', map_prod]

  have char_norm {d : ℕ} (k : Fin d → ℤ) (x : UnitAddTorus (Fin d)) : ‖mFourier k x‖ = 1 := by
    simp only [mFourier, ContinuousMap.coe_mk, norm_prod, fourier_apply, Circle.norm_coe,
      Finset.prod_const_one]

  let coef {d : ℕ} (f : UnitAddTorus (Fin d) → ℂ) (k : Fin d → ℤ) :=
    ∫ x, mFourier k x * f x

  have coef_integrable {d : ℕ} (f : UnitAddTorus (Fin d) → ℂ) (hi : Integrable f volume) (k : Fin d → ℤ) :
      Integrable (fun x => mFourier k x * f x) volume := by
    exact hi.bdd_mul (mFourier k).continuous.measurable.aestronglyMeasurable
      (Eventually.of_forall fun x => (char_norm k x).le)

  have coef_conv {d : ℕ} (K : UnitAddTorus (Fin d) → ℝ) (hKm : Measurable K)
      (C : ℝ) (hK : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), ‖K x‖ ≤ C)
      (f : UnitAddTorus (Fin d) → ℂ) (hfi : Integrable f volume) (k : Fin d → ℤ) :
      coef (conv K f) k = coef (fun x => (K x : ℂ)) k * coef f k := by
    have hKi : Integrable K volume := Integrable.of_bound hKm.aestronglyMeasurable C hK
    have hci : Integrable (fun v : UnitAddTorus (Fin d) × UnitAddTorus (Fin d) =>
        (mFourier k v.1) * (K v.2 • f (v.1-v.2))) (volume.prod volume) :=
      (hKi.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hfi).bdd_mul
        ((mFourier k).continuous.measurable.comp measurable_fst).aestronglyMeasurable
        (Eventually.of_forall fun v => (char_norm k v.1).le)
    have htrans (y : UnitAddTorus (Fin d)) :
        (∫ x, mFourier k x * (K y • f (x-y))) =
          mFourier k y * (K y : ℂ) * coef f k := by
      calc
        _ = ∫ z, mFourier k (z+y) * (K y • f ((z+y)-y)) :=
          (integral_add_right_eq_self _ y).symm
        _ = ∫ z, (mFourier k y * (K y : ℂ)) * (mFourier k z * f z) := by
          apply integral_congr_ae
          exact Eventually.of_forall fun z => by
            dsimp only
            rw [char_add, add_sub_cancel_right]
            simp only [Complex.real_smul]
            ring
        _ = _ := integral_const_mul _ _
    change (∫ x, mFourier k x * conv K f x) = _
    calc
      _ = ∫ x, ∫ y, mFourier k x * (K y • f (x-y)) := by
        congr 1
        funext x
        change mFourier k x * (∫ y, K y • f (x-y)) = _
        exact (integral_const_mul _ _).symm
      _ = ∫ y, ∫ x, mFourier k x * (K y • f (x-y)) := integral_integral_swap hci
      _ = ∫ y, (mFourier k y * (K y : ℂ)) * coef f k := by
        congr 1
        funext y
        exact htrans y
      _ = _ := integral_mul_const _ _

  have coef_real {d : ℕ} (K : UnitAddTorus (Fin d) → ℝ) (hi : Integrable K volume)
      (he : ∀ x, K (-x) = K x) (k : Fin d → ℤ) :
      coef (fun x => (K x : ℂ)) k = (∫ x, K x * (mFourier k x).re : ℝ) := by
    have hic : Integrable (fun x => (K x : ℂ)) volume := Complex.ofRealCLM.integrable_comp hi
    have hreal : conj (coef (fun x => (K x : ℂ)) k) = coef (fun x => (K x : ℂ)) k := by
      unfold coef
      rw [← integral_conj]
      calc
        _ = ∫ x, mFourier k (-x) * (K (-x) : ℂ) := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by dsimp; simp only [map_mul, char_inv, he, Complex.conj_ofReal]
        _ = _ := integral_neg_eq_self (fun x => mFourier k x * (K x : ℂ)) volume
    have hre : (coef (fun x => (K x : ℂ)) k).re = ∫ x, K x * (mFourier k x).re := by
      unfold coef
      change RCLike.re (∫ x, mFourier k x * (K x : ℂ)) = _
      rw [← integral_re (coef_integrable _ hic k)]
      congr 1
      funext x
      change (mFourier k x * (K x : ℂ)).re = K x * (mFourier k x).re
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      ring
    apply Complex.ext
    · simpa using hre
    · simpa using Complex.conj_eq_iff_im.mp hreal

  have real_conv_even {d : ℕ} (K f : UnitAddTorus (Fin d) → ℝ)
      (heK : ∀ x, K (-x) = K x) (hef : ∀ x, f (-x) = f x) :
      ∀ x, (∫ y, K y*f (-x-y)) = ∫ y, K y*f (x-y) := by
    intro x
    calc
      _ = ∫ y, K (-y)*f (-x-(-y)) := (integral_neg_eq_self _ volume).symm
      _ = _ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by
          dsimp only
          rw [heK, show -x-(-y) = -(x-y) by abel, hef]

  have real_conv_coef {d : ℕ} (K f : UnitAddTorus (Fin d) → ℝ) (hKc : Continuous K)
      (heK : ∀ x, K (-x) = K x) (hfi : Integrable f volume) (hef : ∀ x, f (-x) = f x)
      (k : Fin d → ℤ) :
      (∫ x, (∫ y, K y*f (x-y))*(mFourier k x).re) =
        (∫ x, K x*(mFourier k x).re)*(∫ x, f x*(mFourier k x).re) := by
    obtain ⟨C,hC⟩ := (isCompact_univ : IsCompact (univ : Set (UnitAddTorus (Fin d)))).exists_bound_of_continuousOn hKc.continuousOn
    have hKb : ∀ᵐ x ∂volume, ‖K x‖ ≤ C := Eventually.of_forall fun x => hC x (mem_univ x)
    have hKi : Integrable K volume := Integrable.of_bound hKc.measurable.aestronglyMeasurable C hKb
    have hpoint x : Integrable (fun y => K y*f (x-y)) volume := (hfi.comp_sub_left x).bdd_mul hKc.measurable.aestronglyMeasurable hKb
    have hconv : conv K (fun x => (f x : ℂ)) = fun x => ((∫ y, K y*f (x-y) : ℝ) : ℂ) := by
      funext x
      simpa only [conv,Complex.ofRealCLM_apply,Complex.real_smul,Complex.ofReal_mul] using
        Complex.ofRealCLM.integral_comp_comm (hpoint x)
    have hconvI : Integrable (fun x => ∫y,K y*f (x-y)) volume := by
      change Integrable (convolution K f (ContinuousLinearMap.mul ℝ ℝ) volume) volume
      exact hKi.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hfi
    have heconv : ∀ x, (∫y,K y*f (-x-y)) = ∫y,K y*f (x-y) := real_conv_even K f heK hef
    have h := coef_conv K hKc.measurable C hKb (fun x => (f x : ℂ)) (Complex.ofRealCLM.integrable_comp hfi) k
    rw [hconv, coef_real _ hconvI heconv k, coef_real K hKi heK k, coef_real f hfi hef k] at h
    exact_mod_cast h

  have heat_preserves {d : ℕ} (t : ℝ) (ht : 0 < t) (G : UnitAddTorus (Fin d) → ℝ)
      (hG : Measurable G) (hi : Integrable G volume) (hn : ∀ x, 0 ≤ G x)
      (he : ∀ x, G (-x) = G x)
      (hF : ∀ k : Fin d → ℤ, 0 ≤ ∫x,G x*(mFourier k x).re) :
      Measurable (HeatSemigroup d t G) ∧ Integrable (HeatSemigroup d t G) volume ∧
      (∀x,0 ≤ HeatSemigroup d t G x) ∧ (∀x,HeatSemigroup d t G (-x)=HeatSemigroup d t G x) ∧
      (∫x,HeatSemigroup d t G x)=(∫x,G x) ∧
      (∀k:Fin d→ℤ,0 ≤ ∫x,HeatSemigroup d t G x*(mFourier k x).re) := by
    have hOp := HeatOperatorBounds d t ht G hG hi
    have hK := HeatKernelFacts d t ht
    have hth : 0 < t/2 := by positivity
    have hKh := HeatKernelFacts d (t/2) hth
    have hKhi : Integrable (HeatKernel d (t/2)) volume := hKh.1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hKcoeff k : 0 ≤ ∫x,HeatKernel d t x*(mFourier k x).re := by
      have hhalf : HeatSemigroup d (t/2) (HeatKernel d (t/2)) = HeatKernel d t := by
        funext x
        simpa only [add_halves] using hKh.2.2.2.2.2 (t/2) hth x
      have hh := real_conv_coef (HeatKernel d (t/2)) (HeatKernel d (t/2)) hKh.1 hKh.2.2.1 hKhi hKh.2.2.1 k
      change (∫x,HeatSemigroup d (t/2) (HeatKernel d (t/2)) x*(mFourier k x).re) = _ at hh
      rw [hhalf] at hh
      rw [hh]
      exact mul_self_nonneg _
    refine ⟨hOp.1,hOp.2.1,?_,?_,hOp.2.2.1,?_⟩
    · intro x
      exact integral_nonneg fun y => mul_nonneg (hK.2.1 y) (hn (x-y))
    · exact real_conv_even (HeatKernel d t) G hK.2.2.1 he
    · intro k
      change 0 ≤ ∫x,(∫y,HeatKernel d t y*G (x-y))*(mFourier k x).re
      rw [real_conv_coef (HeatKernel d t) G hK.1 hK.2.2.1 hi he k]
      exact mul_nonneg (hKcoeff k) (hF k)

  have probability_gap {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (L : Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P) (δ : ℝ) (hδ : 0 < δ)
      (hself : ∀v w,inner ℝ v (L w)=inner ℝ (L v) w)
      (hpos : ∀v,0 ≤ -inner ℝ v (L v))
      (hquad : ∀v,δ*(-inner ℝ v (L v)) ≤ ‖L v‖^2)
      (hker : ∀v,L v=0 ↔ ∃c:ℝ,∀ᵐx∂P,v x=c)
      (f : Ω→ℝ) (hf : MemLp f 2 P) :
      δ*ProbabilityTheory.variance f P ≤ -inner ℝ (hf.toLp f) (L (hf.toLp f)) := by
    let c := ∫x,f x∂P
    let g := fun x => f x-c
    have hc : MemLp (fun _:Ω => c) 2 P := memLp_const c
    have hg : MemLp g 2 P := hf.sub hc
    let v := hf.toLp f
    let w := hc.toLp (fun _:Ω=>c)
    let v₀ := hg.toLp g
    have hsub : v₀ = v-w := by exact hf.toLp_sub hc
    have hw : L w=0 := (hker w).2 ⟨c,hc.coeFn_toLp⟩
    have hLv : L v₀=L v := by rw [hsub,map_sub,hw,sub_zero]
    have hmean : ∫x,g x∂P=0 := by
      dsimp [g,c]
      rw [integral_sub (hf.integrable (by norm_num)) (integrable_const _)]
      simp
    let A := -L
    have hselfA : ∀v w,inner ℝ v (A w)=inner ℝ (A v) w := by
      intro v w; simpa [A] using congrArg Neg.neg (hself v w)
    have hposA : ∀v,0 ≤ inner ℝ v (A v) := by intro v; simpa [A] using hpos v
    have hquadA : ∀v,δ*inner ℝ v (A v) ≤ ‖A v‖^2 := by intro v; simpa [A] using hquad v
    have horth : ∀w,A w=0 → inner ℝ v₀ w=0 := by
      intro w hw
      have hwL : L w=0 := by simpa [A] using hw
      obtain ⟨b,hb⟩ := (hker w).1 hwL
      rw [L2.inner_def]
      have he : (fun x => inner ℝ (v₀ x) (w x)) =ᵐ[P] fun x => g x*b := by
        filter_upwards [hg.coeFn_toLp,hb] with x hx hy
        simp [v₀,hx,hy,mul_comm]
      rw [integral_congr_ae he,integral_mul_const,hmean,zero_mul]
    have hh := NonnegativeOperatorGap A δ hδ hselfA hposA hquadA v₀ horth
    have hnorm : ‖v₀‖^2 = ProbabilityTheory.variance f P := by
      rw [← real_inner_self_eq_norm_sq,L2.inner_def]
      have he : (fun x => inner ℝ (v₀ x) (v₀ x)) =ᵐ[P] fun x => (f x-c)^2 := by
        filter_upwards [hg.coeFn_toLp] with x hx
        simp [v₀,hx,g,pow_two]
      rw [integral_congr_ae he]
      simpa [c] using (VarianceVariational P f hf c).1
    have hpair : inner ℝ v₀ (L v₀)=inner ℝ v (L v) := by
      rw [hLv,hsub,inner_sub_left]
      rw [hself w v,hw,inner_zero_left,sub_zero]
    simpa [A,hnorm,hpair,v] using hh
  classical
  haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp; infer_instance
  let m : Measure (UnitAddTorus (Fin d)) := volume
  let c := ∫x,G x∂m
  have hc : 0 ≤ c := integral_nonneg hn
  have hu0 : 0 ≤ u := zero_le_one.trans hu
  have hmay := MayerConvolutionBounds d G hG hi (Eventually.of_forall hn) he hF
  obtain ⟨N₀,hN₀,hbound⟩ := hmay.2.2.1 B u hB hu0
  refine ⟨N₀,hN₀,?_⟩
  intro ε hε
  let Gε := if ε=0 then G else HeatSemigroup d ε G
  have hreg : Measurable Gε ∧ Integrable Gε m ∧ (∀x,0≤Gε x) ∧
      (∀x,Gε (-x)=Gε x) ∧ (∫x,Gε x∂m)=c ∧
      (∀k:Fin d→ℤ,0≤∫x,Gε x*(mFourier k x).re∂m) := by
    by_cases hε0 : ε=0
    · simpa only [Gε,hε0,if_pos] using And.intro hG ⟨hi,hn,he,rfl,hF⟩
    · have hεp : 0<ε := lt_of_le_of_ne hε (Ne.symm hε0)
      simpa only [Gε,if_neg hε0] using heat_preserves ε hεp G hG hi hn he hF
  refine ⟨hreg.1,hreg.2.1,hreg.2.2.1,hreg.2.2.2.1,hreg.2.2.2.2.1,hreg.2.2.2.2.2,?_⟩
  intro N hN l β q hβ hβB f hf
  have hN2 : 2≤N := hN₀.trans hN
  have hNp : 0<(N:ℝ) := by exact_mod_cast (by omega : 0<N)
  have hNne : (N:ℝ)≠0 := ne_of_gt hNp
  let P := CanonicalLaw (N:=N) Gε q.density β
  haveI : IsProbabilityMeasure P := (JumpConditionalBalance d N hN2 l u β q hβ Gε hreg.1 hreg.2.1 hreg.2.2.1 hreg.2.2.2.1).1
  obtain ⟨L,hL,hUni⟩ := JumpL2Extension d N hN2 l u β q hβ Gε hreg.1 hreg.2.1 hreg.2.2.1 hreg.2.2.2.1
  let δ := Real.exp (-B*u*c)/2
  have hδ : 0<δ := by dsimp [δ]; positivity
  let A := Real.exp (-β*u*c)-2*u*(β*c/N+N*MayerDefect m Gε (β/N))
  have hthreshold : 2*u*(β*c/N+N*MayerDefect m Gε (β/N)) ≤ Real.exp (-B*u*c)/2 :=
    hbound N hN β ε hβ hβB hε
  have hex : Real.exp (-B*u*c) ≤ Real.exp (-β*u*c) := Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hu0 hc])
  have hδA : δ≤A := by dsimp [δ,A]; linarith
  have hinner (g : Configuration d N→ℝ) (hg : MemLp g 2 P) :
      inner ℝ (hg.toLp g) (L (hg.toLp g)) = ∫X,g X*JumpOperator Gε q.density β g X∂P := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp,(hL.2.2.2 g hg).2.1] with X hx hLX
    simp [hx,hLX,mul_comm]
  have hnorm (g : Configuration d N→ℝ) (hg : MemLp g 2 P) :
      ‖L (hg.toLp g)‖^2 = ∫X,(JumpOperator Gε q.density β g X)^2∂P := by
    rw [←real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hL.2.2.2 g hg).2.1] with X hx
    simp [hx,pow_two]
  have hpos : ∀v,0≤-inner ℝ v (L v) := by
    intro v
    have hh := (hL.2.2.2 v (Lp.memLp v)).2.2.2.2.2.1
    simpa only [Lp.toLp_coeFn] using hh
  have hquad : ∀v,δ*(-inner ℝ v (L v)) ≤ ‖L v‖^2 := by
    intro v
    have hh := ReplacementCoercivity d N hN2 l u β β q hβ hβ (le_refl β) Gε hreg.1 hreg.2.1
      hreg.2.2.1 hreg.2.2.2.1 hreg.2.2.2.2.2 v (Lp.memLp v)
    have hid : β*(MayerDefect m Gε (β/N)/(β/N))=N*MayerDefect m Gε (β/N) := by
      by_cases hβ0:β=0
      · simp [hβ0,MayerDefect]
      · field_simp
    change (Real.exp (-β*u*(∫x,Gε x∂m))-2*u*(β*(∫x,Gε x∂m)/N+β*(MayerDefect m Gε (β/N)/(β/N))))*
      (-(∫X,v X*JumpOperator Gε q.density β v X∂P)) ≤ ∫X,(JumpOperator Gε q.density β v X)^2∂P at hh
    rw [hreg.2.2.2.2.1,hid,←hinner v (Lp.memLp v),←hnorm v (Lp.memLp v),Lp.toLp_coeFn] at hh
    exact (mul_le_mul_of_nonneg_right hδA (hpos v)).trans hh
  have hgap := probability_gap P L δ hδ hL.2.1 hpos hquad hL.2.2.1 f hf
  rw [hinner f hf] at hgap
  have hfactor : (2*Real.exp (B*u*c))*δ=1 := by
    dsimp [δ]
    rw [show -B*u*c = -(B*u*c) by ring,Real.exp_neg]
    field_simp
  have hh := mul_le_mul_of_nonneg_left hgap (show 0≤2*Real.exp (B*u*c) by positivity)
  simpa only [←mul_assoc,hfactor,one_mul] using hh

