import Tablet.Preamble
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Integral.Bochner.Set
open MeasureTheory
-- [TABLET NODE: DGRConditionalMasterLayerCake]
/-- Faithful conditional DGR master implication. Sharp GLZ is an explicit premise. -/
theorem DGRConditionalMasterLayerCake {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xi : Ω → ℝ) (hXi : Measurable Xi)
    (R : ℝ → Ω → ℝ) (A F H D m : ℝ → ℝ) (N L U : ℝ)
    (hN : 0 < N) (hL : 1 ≤ L) (hU : 1 ≤ U)
    (hpos : ∀ u, U ≤ u → 0 < A u ∧ 0 < F u ∧ 0 < H u ∧ 0 < D u)
    (hM1 : ∀ u, U ≤ u → ∀ᵐ x ∂μ, u ≤ Xi x → u ≤ -R u x/(2*N))
    (hM2 : ∀ u, U ≤ u → ∀ᵐ x ∂μ, -R u x/(2*N) ≤ m u)
    (hM3 : ∀ u, U ≤ u → (F u)^2 ≤ 1/L ∧ (H u)^2 ≤ 1/L ∧ D u ≤ 1/L)
    (hgrowth : ∀ u, U ≤ u → 2*L^2*min u (m u)*(1+A u) ≤ N)
    (hGLZ : ∀ u, U ≤ u → μ.real {x | 2*N*u ≤ |R u x|} ≤
      L*Real.exp (-(1/L)*min (min (4*u^2/(H u)^2) (2*u/D u))
        (min ((4*N*u^2/(F u)^2)^((3:ℝ)⁻¹)) ((2*N*u/A u)^((2:ℝ)⁻¹))))) :
    (∀ u, U ≤ u → μ.real {x | u ≤ Xi x} ≤ L*Real.exp (-2*u)) ∧
    Integrable (fun x => Real.exp (Xi x)) μ ∧
    (∫ x, Real.exp (Xi x) ∂μ) ≤ Real.exp U+L := by
-- BODY
  have four_regime_rate (L N u A F H D:ℝ)(hL:1≤L)(hN:0<N)(hu:1≤u)
      (hA:0<A)(hF:0<F)(hH:0<H)(hD:0<D)
      (hFn:F^2≤1/L)(hHn:H^2≤1/L)(hDn:D≤1/L)
      (hgrowth:2*L^2*u*(1+A)≤N) :
      2*L*u≤min (min (4*u^2/H^2) (2*u/D))
        (min ((4*N*u^2/F^2)^((3:ℝ)⁻¹)) ((2*N*u/A)^((2:ℝ)⁻¹))) := by
    have hLp:0<L := zero_lt_one.trans_le hL
    have hup:0<u := zero_lt_one.trans_le hu
    have hLF:L*F^2≤1 := by have ht:=(le_div_iff₀ hLp).mp hFn;nlinarith
    have hLH:L*H^2≤1 := by have ht:=(le_div_iff₀ hLp).mp hHn;nlinarith
    have hLD:L*D≤1 := by have ht:=(le_div_iff₀ hLp).mp hDn;nlinarith
    have hNu:2*L^2*u≤N := by
      have hpos:0≤2*L^2*u*A := by positivity
      nlinarith
    have hNA:2*L^2*u*A≤N := by
      have hpos:0≤2*L^2*u := by positivity
      nlinarith
    have hfirst:2*L*u≤4*u^2/H^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hH)).mpr
      have ht:=mul_le_mul_of_nonneg_left hLH (by positivity : 0≤2*u)
      nlinarith
    have hsecond:2*L*u≤2*u/D := by
      apply (le_div_iff₀ hD).mpr
      have ht:=mul_le_mul_of_nonneg_left hLD (by positivity : 0≤2*u)
      nlinarith
    have hthird:2*L*u≤(4*N*u^2/F^2)^((3:ℝ)⁻¹) := by
      have hbase:0≤4*N*u^2/F^2 := by positivity
      have hroot:( (4*N*u^2/F^2)^((3:ℝ)⁻¹))^3=4*N*u^2/F^2 :=
        Real.rpow_inv_natCast_pow hbase (by decide : (3:ℕ)≠0)
      apply (pow_le_pow_iff_left₀ (by positivity) (Real.rpow_nonneg hbase _) (by decide : (3:ℕ)≠0)).mp
      rw [hroot]
      apply (le_div_iff₀ (sq_pos_of_pos hF)).mpr
      have ht:=mul_le_mul_of_nonneg_left hLF (by positivity : 0≤8*L^2*u^3)
      have hn:=mul_le_mul_of_nonneg_left hNu (by positivity : 0≤4*u^2)
      nlinarith
    have hfourth:2*L*u≤(2*N*u/A)^((2:ℝ)⁻¹) := by
      have hbase:0≤2*N*u/A := by positivity
      have hroot:((2*N*u/A)^((2:ℝ)⁻¹))^2=2*N*u/A :=
        Real.rpow_inv_natCast_pow hbase (by decide : (2:ℕ)≠0)
      apply (pow_le_pow_iff_left₀ (by positivity) (Real.rpow_nonneg hbase _) (by decide : (2:ℕ)≠0)).mp
      rw [hroot]
      apply (le_div_iff₀ hA).mpr
      have ht:=mul_le_mul_of_nonneg_left hNA (by positivity : 0≤2*u)
      nlinarith
    exact le_min (le_min hfirst hsecond) (le_min hthird hfourth)
  have exponential_from_prefactored_tail
      (μ : Measure Ω) [IsProbabilityMeasure μ] (E : Ω → ℝ) (hm : Measurable E)
      (P C U L T : ℝ) (hP : 0 ≤ P) (hU : 0 ≤ U) (hT : 0 ≤ T) (hLT : T < L)
      (hcap : ∀ᵐ x ∂μ,-C ≤ E x)
      (htail : ∀ v : ℝ,U ≤ v → μ.real {x | E x ≤ -v} ≤ P*Real.exp (-L*v)) :
      ∀ t : ℝ,0 ≤ t → t ≤ T →
        Integrable (fun x => Real.exp (-t*E x)) μ ∧
        (∫x,Real.exp (-t*E x) ∂μ) ≤
          Real.exp (T*U) + P*(Real.exp T-1)*Real.exp (T*U-L*U)/(1-Real.exp (T-L)) := by
    classical
    intro t ht htT
    let M := Nat.ceil (max 0 C)+1
    let A := fun n : ℕ => {x : Ω | E x ≤ -(U+(n:ℝ))}
    let b := fun n : ℕ => (Real.exp T-1)*Real.exp (T*(U+(n:ℝ)))
    let F := fun x => Real.exp (-t*E x)
    let H := fun x => Real.exp (T*U)+∑n ∈ Finset.range M,(A n).indicator (fun _ => b n) x
    have hA (n : ℕ) : MeasurableSet (A n) := measurableSet_le hm measurable_const
    have hb (n : ℕ) : 0 ≤ b n := mul_nonneg (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hT)) (Real.exp_pos _).le
    have htel (n : ℕ) : Real.exp (T*U)+∑j ∈ Finset.range (n+1),b j =
        Real.exp (T*(U+(n:ℝ)+1)) := by
      have he (j : ℕ) : b j = Real.exp (T*U)*(Real.exp T)^j*(Real.exp T-1) := by
        have hx : Real.exp (T*(U+(j:ℝ)))=Real.exp (T*U)*(Real.exp T)^j := by
          rw [←Real.exp_nat_mul,←Real.exp_add]
          congr 1;ring
        dsimp [b]
        rw [hx]
        ring
      simp_rw [he,←Finset.sum_mul,←Finset.mul_sum]
      rw [mul_assoc,geom_sum_mul]
      calc
        _ = Real.exp (T*U)*(Real.exp T)^(n+1) := by ring
        _ = Real.exp (T*U+((n+1:ℕ):ℝ)*T) := by rw [←Real.exp_nat_mul,←Real.exp_add]
        _ = _ := by congr 1;push_cast;ring
    have hi : Integrable F μ := by
      apply (integrable_const (Real.exp (T*max 0 C))).mono' (hm.const_mul (-t)).exp.aestronglyMeasurable
      filter_upwards [hcap] with x hx
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have h1 := mul_le_mul_of_nonneg_left (show -E x ≤ max 0 C by linarith [le_max_right (0:ℝ) C]) ht
      have h2 := mul_le_mul_of_nonneg_right htT (le_max_left (0:ℝ) C)
      change -t*E x ≤ T*max 0 C
      nlinarith only [h1,h2]
    have hH : Integrable H μ := (integrable_const _).add
      (integrable_finset_sum _ fun n _ => (integrable_const (b n)).indicator (hA n))
    have hnon (n : ℕ) (x : Ω) : 0 ≤ (A n).indicator (fun _ => b n) x := by
      by_cases hx : x ∈ A n <;> simp [Set.indicator,hx,hb n]
    have hFH : F ≤ᵐ[μ] H := by
      filter_upwards [hcap] with x hx
      by_cases hlow : -E x ≤ U
      · have h1 := mul_le_mul_of_nonneg_left hlow ht
        have h2 := mul_le_mul_of_nonneg_right htT hU
        have he : F x ≤ Real.exp (T*U) := Real.exp_le_exp.mpr (by nlinarith only [h1,h2])
        have hs := Finset.sum_nonneg (fun n (_ : n ∈ Finset.range M) => hnon n x)
        dsimp [H]
        linarith
      · have hpos : 0 ≤ -E x-U := by linarith
        let n := Nat.floor (-E x-U)
        have hnlo : (n:ℝ) ≤ -E x-U := Nat.floor_le hpos
        have hnhi : -E x-U < (n:ℝ)+1 := Nat.lt_floor_add_one _
        have hnM : n ∈ Finset.range M := by
          rw [Finset.mem_range]
          have hn : n ≤ Nat.ceil (max 0 C) := Nat.floor_le_of_le (by
            have hh := Nat.le_ceil (max 0 C)
            linarith [le_max_right (0:ℝ) C])
          exact Nat.lt_succ_of_le hn
        have hxA : x ∈ A n := by dsimp [A];linarith
        have h1 := mul_le_mul_of_nonneg_right htT (show 0 ≤ -E x by linarith)
        have h2 := mul_le_mul_of_nonneg_left hnhi.le hT
        have he : F x ≤ Real.exp (T*(U+(n:ℝ)+1)) := Real.exp_le_exp.mpr (by nlinarith only [h1,h2])
        have hp : (∑j ∈ Finset.range (n+1),(A j).indicator (fun _=>b j) x)=∑j ∈ Finset.range (n+1),b j := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjn : j≤n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
          have hcast : (j:ℝ)≤n := by exact_mod_cast hjn
          have hxj : x∈A j := by dsimp[A];linarith
          exact Set.indicator_of_mem hxj _
        have hs := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (Nat.succ_le_of_lt (Finset.mem_range.mp hnM)))
          (fun j _ _=>hnon j x)
        rw [hp] at hs
        have htelv:=htel n
        dsimp [H]
        linarith
    have hHval : (∫x,H x ∂μ) = Real.exp (T*U)+∑n ∈ Finset.range M,μ.real (A n)*b n := by
      rw [integral_add (integrable_const _) (integrable_finset_sum _ fun n _ => (integrable_const (b n)).indicator (hA n)),
        integral_finset_sum _ fun n _ => (integrable_const (b n)).indicator (hA n)]
      simp only [integral_const,probReal_univ,one_smul]
      congr 1
      apply Finset.sum_congr rfl
      intro n _
      simpa only [smul_eq_mul] using integral_indicator_const (b n) (hA n)
    have htailn (n : ℕ) : μ.real (A n)*b n ≤ P*Real.exp (-L*(U+(n:ℝ)))*b n := by
      exact mul_le_mul_of_nonneg_right (htail _ (le_add_of_nonneg_right (Nat.cast_nonneg n))) (hb n)
    let r := Real.exp (T-L)
    let a := P*(Real.exp T-1)*Real.exp (T*U-L*U)
    have hcoef (n : ℕ) : P*Real.exp (-L*(U+(n:ℝ)))*b n = a*r^n := by
      dsimp [a,r,b]
      rw [←Real.exp_nat_mul]
      have he : Real.exp (-L*(U+(n:ℝ)))*Real.exp (T*(U+(n:ℝ))) =
          Real.exp (T*U-L*U)*Real.exp ((T-L)*(n:ℝ)) := by
        rw [←Real.exp_add,←Real.exp_add]
        congr 1;ring
      calc
        _ = P*(Real.exp T-1)*(Real.exp (-L*(U+(n:ℝ)))*Real.exp (T*(U+(n:ℝ)))) := by ring
        _ = _ := by rw [he];ring
    have hr0 : 0 ≤ r := (Real.exp_pos _).le
    have hr1 : r < 1 := by dsimp [r];rw [Real.exp_lt_one_iff];linarith
    have hd : 0 < 1-r := by linarith
    have hgeom : (∑n ∈ Finset.range M,r^n) ≤ 1/(1-r) := by
      apply (le_div_iff₀ hd).mpr
      rw [geom_sum_mul_neg]
      linarith [pow_nonneg hr0 M]
    have hs : (∑n ∈ Finset.range M,μ.real (A n)*b n) ≤ a/(1-r) := by
      calc
        _ ≤ ∑n ∈ Finset.range M,a*r^n := Finset.sum_le_sum fun n _ => by rw [← hcoef];exact htailn n
        _ = a*(∑n ∈ Finset.range M,r^n) := (Finset.mul_sum _ _ _).symm
        _ ≤ a*(1/(1-r)) := mul_le_mul_of_nonneg_left hgeom (by dsimp[a];exact mul_nonneg (mul_nonneg hP (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hT))) (Real.exp_pos _).le)
        _ = a/(1-r) := by ring
    refine ⟨hi,?_⟩
    have he := integral_mono_ae hi hH hFH
    rw [hHval] at he
    change (∫x,F x ∂μ) ≤ Real.exp (T*U)+a/(1-r)
    linarith
  have hLp : 0<L := zero_lt_one.trans_le hL
  have htail : ∀ u, U ≤ u → μ.real {x | u ≤ Xi x} ≤ L*Real.exp (-2*u) := by
    intro u hu
    obtain ⟨hA,hF,hH,hD⟩:=hpos u hu
    by_cases hum : u ≤ m u
    · have hg:=hgrowth u hu
      rw [min_eq_left hum] at hg
      obtain ⟨hFn,hHn,hDn⟩:=hM3 u hu
      have hr:=four_regime_rate L N u (A u) (F u) (H u) (D u) hL hN
        (hU.trans hu) hA hF hH hD hFn hHn hDn hg
      have hsub : ∀ᵐ x ∂μ, x ∈ {x | u ≤ Xi x} → x ∈ {x | 2*N*u ≤ |R u x|} := by
        filter_upwards [hM1 u hu] with x hx hxu
        have ht:=(le_div_iff₀ (by positivity : 0<2*N)).mp (hx hxu)
        have hab:=neg_le_abs (R u x)
        change 2*N*u≤|R u x|
        nlinarith
      have hm := measure_mono_ae hsub
      have hreal : μ.real {x | u ≤ Xi x} ≤ μ.real {x | 2*N*u ≤ |R u x|} :=
        ENNReal.toReal_mono (measure_ne_top μ _) hm
      have he : Real.exp (-(1/L)*min (min (4*u^2/(H u)^2) (2*u/D u))
        (min ((4*N*u^2/(F u)^2)^((3:ℝ)⁻¹)) ((2*N*u/A u)^((2:ℝ)⁻¹)))) ≤
          Real.exp (-2*u) := by
        apply Real.exp_le_exp.mpr
        have ht:=mul_le_mul_of_nonneg_left hr (show 0≤1/L by positivity)
        have hc : (1/L)*(2*L*u)=2*u := by field_simp
        rw [hc] at ht
        nlinarith
      exact hreal.trans ((hGLZ u hu).trans (mul_le_mul_of_nonneg_left he hLp.le))
    · have hzero : μ {x | u ≤ Xi x}=0 := by
        apply measure_eq_zero_iff_ae_notMem.mpr
        filter_upwards [hM1 u hu,hM2 u hu] with x h1 h2
        change ¬u≤Xi x
        intro hx
        exact hum ((h1 hx).trans h2)
      rw [measureReal_def,hzero,ENNReal.toReal_zero]
      positivity
  let C := U+N/(2*L^2)+1
  have hCU : U≤C := by
    have hn:0≤N/(2*L^2) := by positivity
    dsimp[C];linarith
  have hcap : ∀ᵐ x ∂μ, Xi x ≤ C := by
    filter_upwards [hM1 C hCU,hM2 C hCU] with x h1 h2
    by_contra hx
    have hc : C≤Xi x := (lt_of_not_ge hx).le
    have hCm : C≤m C := (h1 hc).trans h2
    have hg:=hgrowth C hCU
    rw [min_eq_left hCm] at hg
    have hA:0<A C := (hpos C hCU).1
    have hCpos:0<C := zero_lt_one.trans_le (hU.trans hCU)
    have hsmall : 2*L^2*C≤N := by
      have ht : 0≤2*L^2*C*A C := by positivity
      nlinarith
    have hdiv : C≤N/(2*L^2) := (le_div_iff₀ (by positivity : 0<2*L^2)).mpr (by nlinarith)
    dsimp[C] at hdiv
    linarith
  have he := exponential_from_prefactored_tail μ (fun x=>-Xi x) hXi.neg
    L C U 2 1 hLp.le (zero_le_one.trans hU) (by norm_num) (by norm_num)
    (show ∀ᵐ x ∂μ, -C≤-Xi x from by filter_upwards[hcap] with x hx;linarith)
    (by intro v hv;simpa only [neg_le_neg_iff] using htail v hv)
    1 (by norm_num) (by norm_num)
  have heq : L*(Real.exp 1-1)*Real.exp (1*U-2*U)/(1-Real.exp (1-2))=
      L*Real.exp (1-U) := by
    have hp:Real.exp 1≠0 := (Real.exp_pos _).ne'
    have hn:Real.exp 1-1≠0 := by
      have hh:1<Real.exp 1 := by rw[Real.one_lt_exp_iff];norm_num
      linarith
    have hx : Real.exp (-U)=Real.exp (1-U)*Real.exp (-1) := by
      rw[←Real.exp_add];congr 1;ring
    have hh:1*U-2*U= -U := by ring
    have ho:(1:ℝ)-2= -1 := by norm_num
    rw[hh,ho,hx,Real.exp_neg]
    field_simp
  have hbound : L*Real.exp (1-U)≤L := by
    have hx:Real.exp (1-U)≤1 := Real.exp_le_one_iff.mpr (by linarith)
    simpa using mul_le_mul_of_nonneg_left hx hLp.le
  refine ⟨htail,?_,?_⟩
  · simpa using he.1
  · have hv:=he.2
    rw[heq] at hv
    have hs : (∫x,Real.exp (Xi x) ∂μ)≤Real.exp U+L*Real.exp (1-U) := by simpa using hv
    linarith
