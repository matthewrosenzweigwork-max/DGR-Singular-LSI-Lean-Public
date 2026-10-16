module

public import Tablet.Preamble
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section
open MeasureTheory
-- [TABLET NODE: GLZEvenMomentToTail]
/-- Four-regime Markov optimization; sharp moment hypothesis stays explicit. -/
theorem GLZEvenMomentToTail (K : ℝ) (hK : 1≤K) :
    ∃L : ℝ,1≤L ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
      (A B C D : ℝ),0<A → 0<B → 0<C → 0<D →
      (∀m : ℕ,1≤m → Integrable (fun x=>(X x)^(2*m)) μ ∧
        (∫x,(X x)^(2*m) ∂μ)≤
          (K*((m:ℝ)*C^2+(m:ℝ)^2*D^2+(m:ℝ)^3*B^2+(m:ℝ)^4*A^2))^m) →
      ∀t : ℝ,0<t → μ.real {x | t≤|X x|}≤
        L*Real.exp (-(1/L)*min (min (t^2/C^2) (t/D))
          (min ((t^2/B^2)^((3:ℝ)⁻¹)) ((t/A)^((2:ℝ)⁻¹)))) := by
-- BODY
  let z := 16*K
  let L := max (2*z/Real.log 4) (Real.exp (2*z))
  have hKp : 0<K := zero_lt_one.trans_le hK
  have hzp : 0<z := by dsimp[z];positivity
  have hlog : 0<Real.log 4 := Real.log_pos (by norm_num)
  have hL1 : 1≤L := (Real.one_le_exp_iff.mpr (by positivity : 0≤2*z)).trans (le_max_right _ _)
  have hLp : 0<L := zero_lt_one.trans_le hL1
  refine ⟨L,hL1,?_⟩
  intro Ω _ μ _ X A B C D hA hB hC hD hmoment t ht
  have moment_markov (μ : Measure Ω)
      (X : Ω → ℝ) (m : ℕ) (t C : ℝ) (ht : 0<t) (hC : 0≤C)
      (hi : Integrable (fun x=>(X x)^(2*m)) μ)
      (hm : (∫x,(X x)^(2*m) ∂μ)≤C^m) :
      μ.real {x | t≤|X x|}≤(C/t^2)^m := by
    have hev : Even (2*m) := even_two_mul m
    have hh := (hi.div_const (t^(2*m))).measure_le_integral
      (Filter.Eventually.of_forall fun x=>div_nonneg (hev.pow_nonneg _) (pow_nonneg ht.le _))
      (s:={x | t≤|X x|}) (fun x hx=>by
        rw[le_div_iff₀ (pow_pos ht _),one_mul]
        have hp:=pow_le_pow_left₀ ht.le hx (2*m)
        rwa[hev.pow_abs] at hp)
    have hb : (∫x,(X x)^(2*m)/t^(2*m) ∂μ)≤(C/t^2)^m := by
      rw[integral_div]
      calc
        _≤C^m/t^(2*m) := div_le_div_of_nonneg_right hm (by positivity)
        _=_ := by rw[pow_mul,div_pow]
    have hh' := hh.trans (ENNReal.ofReal_le_ofReal hb)
    have hx:=ENNReal.toReal_mono ENNReal.ofReal_ne_top hh'
    simpa only[Measure.real,ENNReal.toReal_ofReal (by positivity : 0≤(C/t^2)^m)] using hx
  have four_regime_moment_base (K t A B C D r z : ℝ) (m : ℕ)
      (hK : 1≤K) (ht : 0<t) (hA : 0<A) (hB : 0<B) (hC : 0<C) (hD : 0<D)
      (hr : 0≤r) (hz : z=16*K) (hm : z*(m:ℝ)≤r)
      (hrC : r≤t^2/C^2) (hrD : r≤t/D)
      (hrB : r≤(t^2/B^2)^((3:ℝ)⁻¹)) (hrA : r≤(t/A)^((2:ℝ)⁻¹)) :
      K*((m:ℝ)*C^2+(m:ℝ)^2*D^2+(m:ℝ)^3*B^2+(m:ℝ)^4*A^2)/t^2≤1/4 := by
    have hKp : 0<K := zero_lt_one.trans_le hK
    have hz1 : 1≤z := by rw[hz];linarith
    have hzm : 0≤z*(m:ℝ) := by positivity
    have h1 : z*(m:ℝ)*C^2≤t^2 := by
      have hc:=(le_div_iff₀ (sq_pos_of_pos hC)).mp hrC
      exact (mul_le_mul_of_nonneg_right hm (sq_nonneg C)).trans hc
    have h2 : z^2*(m:ℝ)^2*D^2≤t^2 := by
      have hd:=(le_div_iff₀ hD).mp hrD
      have hdd : z*(m:ℝ)*D≤t := (mul_le_mul_of_nonneg_right hm hD.le).trans hd
      have hs:=pow_le_pow_left₀ (by positivity : 0≤z*(m:ℝ)*D) hdd 2
      simpa only[mul_pow] using hs
    have h3 : z^3*(m:ℝ)^3*B^2≤t^2 := by
      have hroot : ((t^2/B^2)^((3:ℝ)⁻¹))^3=t^2/B^2 :=
        Real.rpow_inv_natCast_pow (by positivity) (by decide : (3:ℕ)≠0)
      have hs:=pow_le_pow_left₀ hzm (hm.trans hrB) 3
      rw[hroot,mul_pow] at hs
      exact (le_div_iff₀ (sq_pos_of_pos hB)).mp hs
    have h4 : z^4*(m:ℝ)^4*A^2≤t^2 := by
      have hroot : ((t/A)^((2:ℝ)⁻¹))^2=t/A :=
        Real.rpow_inv_natCast_pow (by positivity) (by decide : (2:ℕ)≠0)
      have hs:=pow_le_pow_left₀ hzm (hm.trans hrA) 2
      rw[hroot] at hs
      have ha:=(le_div_iff₀ hA).mp hs
      have hp:=pow_le_pow_left₀ (by positivity : 0≤(z*(m:ℝ))^2*A) ha 2
      have he : ((z*(m:ℝ))^2*A)^2=z^4*(m:ℝ)^4*A^2 := by ring
      rwa[he] at hp
    have hz2 : z≤z^2 := by simpa using pow_le_pow_right₀ hz1 (by norm_num : (1:ℕ)≤2)
    have hz3 : z≤z^3 := by simpa using pow_le_pow_right₀ hz1 (by norm_num : (1:ℕ)≤3)
    have hz4 : z≤z^4 := by simpa using pow_le_pow_right₀ hz1 (by norm_num : (1:ℕ)≤4)
    have g2 := (mul_le_mul_of_nonneg_right hz2 (by positivity : 0≤(m:ℝ)^2*D^2)).trans (by simpa only[mul_assoc] using h2)
    have g3 := (mul_le_mul_of_nonneg_right hz3 (by positivity : 0≤(m:ℝ)^3*B^2)).trans (by simpa only[mul_assoc] using h3)
    have g4 := (mul_le_mul_of_nonneg_right hz4 (by positivity : 0≤(m:ℝ)^4*A^2)).trans (by simpa only[mul_assoc] using h4)
    apply (div_le_iff₀ (sq_pos_of_pos ht)).mpr
    rw[hz] at h1 g2 g3 g4
    nlinarith only[h1,g2,g3,g4]
  let r := min (min (t^2/C^2) (t/D))
    (min ((t^2/B^2)^((3:ℝ)⁻¹)) ((t/A)^((2:ℝ)⁻¹)))
  have hr : 0≤r := by dsimp[r];positivity
  have hrC : r≤t^2/C^2 := (min_le_left _ _).trans (min_le_left _ _)
  have hrD : r≤t/D := (min_le_left _ _).trans (min_le_right _ _)
  have hrB : r≤(t^2/B^2)^((3:ℝ)⁻¹) := (min_le_right _ _).trans (min_le_left _ _)
  have hrA : r≤(t/A)^((2:ℝ)⁻¹) := (min_le_right _ _).trans (min_le_right _ _)
  change μ.real {x | t≤|X x|}≤L*Real.exp (-(1/L)*r)
  by_cases hlarge : 2*z≤r
  · let m := Nat.floor (r/z)
    have hquot : 2≤r/z := (le_div_iff₀ hzp).mpr (by nlinarith)
    have hm : 1≤m := Nat.floor_pos.mpr (by linarith)
    have hmu : z*(m:ℝ)≤r := by
      have hh:=Nat.floor_le (by positivity : 0≤r/z)
      simpa only[m,mul_comm] using (le_div_iff₀ hzp).mp hh
    have hml : r/(2*z)≤(m:ℝ) := by
      have hh:=Nat.lt_floor_add_one (r/z)
      have hh' : r<((m:ℝ)+1)*z := (div_lt_iff₀ hzp).mp hh
      apply (div_le_iff₀ (by positivity : 0<2*z)).mpr
      have hmreal : 1≤(m:ℝ) := by exact_mod_cast hm
      nlinarith
    obtain ⟨hi,hb⟩:=hmoment m hm
    let P := K*((m:ℝ)*C^2+(m:ℝ)^2*D^2+(m:ℝ)^3*B^2+(m:ℝ)^4*A^2)
    have hp : 0≤P := by dsimp[P];positivity
    have hbase:=four_regime_moment_base K t A B C D r z m hK ht hA hB hC hD hr rfl hmu hrC hrD hrB hrA
    have hmark:=moment_markov μ X m t P ht hp hi hb
    have hLlower : 2*z/Real.log 4≤L := le_max_left _ _
    have hcoeff : 1/L≤Real.log 4/(2*z) := by
      apply (div_le_div_iff₀ hLp (by positivity : 0<2*z)).mpr
      have hh:=(div_le_iff₀ hlog).mp hLlower
      nlinarith
    calc
      _≤(P/t^2)^m := hmark
      _≤(1/4:ℝ)^m := pow_le_pow_left₀ (by positivity) hbase _
      _=Real.exp (-(m:ℝ)*Real.log 4) := by
        rw[←Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num)]
        congr 1
        rw[Real.log_div (by norm_num : (1:ℝ)≠0) (by norm_num : (4:ℝ)≠0),Real.log_one]
        ring
      _≤Real.exp (-r/(2*z)*Real.log 4) := Real.exp_le_exp.mpr (by
        have hh:=mul_le_mul_of_nonneg_right hml hlog.le
        simpa only[neg_mul,neg_div] using neg_le_neg hh)
      _≤Real.exp (-(1/L)*r) := by
        apply Real.exp_le_exp.mpr
        have hh:=mul_le_mul_of_nonneg_right hcoeff hr
        have he : -r/(2*z)*Real.log 4 = -(Real.log 4/(2*z)*r) := by ring
        rw[he]
        simpa only[neg_mul] using neg_le_neg hh
      _≤L*Real.exp (-(1/L)*r) := by
        have hh:=mul_le_mul_of_nonneg_right hL1 (Real.exp_pos (-(1/L)*r)).le
        simpa using hh
  · have hm : μ.real {x | t≤|X x|}≤1 := by
      have hh : μ {x | t≤|X x|}≤μ Set.univ := measure_mono (Set.subset_univ _)
      have ht:=ENNReal.toReal_mono (measure_ne_top μ _) hh
      simpa using ht
    have hLE : Real.exp (2*z)≤L := le_max_right _ _
    have hdiv : r/L≤r := (div_le_self hr hL1)
    have hsmall : 1≤Real.exp (2*z-r) := Real.one_le_exp_iff.mpr (by linarith)
    have he : Real.exp (-r)≤Real.exp (-(1/L)*r) := Real.exp_le_exp.mpr (by
      have he : -(1/L)*r= -(r/L) := by ring
      rw[he]
      exact neg_le_neg hdiv)
    calc
      _≤1 := hm
      _≤Real.exp (2*z-r) := hsmall
      _=Real.exp (2*z)*Real.exp (-r) := by rw[←Real.exp_add];rfl
      _≤L*Real.exp (-(1/L)*r) := mul_le_mul hLE he (Real.exp_pos _).le hLp.le
