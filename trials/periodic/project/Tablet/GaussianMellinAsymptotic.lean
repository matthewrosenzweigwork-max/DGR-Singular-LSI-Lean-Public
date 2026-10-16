import Tablet.Preamble
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Separation.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open MeasureTheory Set Filter
open scoped Topology Interval
-- [TABLET NODE: GaussianMellinAsymptotic]
theorem GaussianMellinAsymptotic (d : ℕ) (s : ℝ) (hs : 0≤s) :
    ∃ b C : ℝ, 0<b ∧ 0≤C ∧ ∀ r : ℝ, 0<r → r<1/4 →
      IntegrableOn (fun t : ℝ => t^(((d:ℝ)-s)/2-1)*
        (4*Real.pi*t)^(-(d:ℝ)/2)*Real.exp (-r^2/(4*t))) (Ioc 0 1) volume ∧
      |(∫t in Ioc 0 1, t^(((d:ℝ)-s)/2-1)*
        (4*Real.pi*t)^(-(d:ℝ)/2)*Real.exp (-r^2/(4*t))) -
        (if s=0 then b*Real.log (1/r) else b*r^(-s))| ≤ C := by
-- BODY
  classical
  have inverse_gaussian_integrable (β c : ℝ) (hc : 0 < c) :
      IntegrableOn (fun t : ℝ => t^β*Real.exp (-c/t)) (Ioc 0 1) volume := by
    classical
    let f := fun t : ℝ => t^β*Real.exp (-c/t)
    have hlim : Tendsto f (𝓝[>] 0) (𝓝 0) := by
      have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-β) c hc).comp
        (tendsto_inv_nhdsGT_zero)
      apply h.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      change 0 < t at ht
      dsimp [f]
      rw [Real.inv_rpow ht.le,← Real.rpow_neg ht.le]
      congr 2
      ring
    have hc : ContinuousOn (Function.update f 0 0) (Icc 0 1) := by
      rw [continuousOn_update_iff]
      refine ⟨?_,fun _ => hlim.mono_left (nhdsWithin_mono _ ?_)⟩
      · intro t ht
        have ht0 : t ≠ 0 := by simpa using ht.2
        have htpos : 0 < t := lt_of_le_of_ne ht.1.1 (Ne.symm ht0)
        exact ((Real.continuousAt_rpow_const t β (Or.inl ht0)).mul
          (Real.continuous_exp.continuousAt.comp
            (continuousAt_const.div continuousAt_id ht0))).continuousWithinAt
      · intro t ht
        have ht0 : t ≠ 0 := by simpa using ht.2
        exact lt_of_le_of_ne ht.1.1 (Ne.symm ht0)
    have hi : IntegrableOn (Function.update f 0 0) (Icc 0 1) volume := hc.integrableOn_Icc
    have hi' := hi.mono_set Ioc_subset_Icc_self
    apply hi'.congr_fun _ measurableSet_Ioc
    intro t ht
    rw [Function.update_of_ne (ne_of_gt ht.1)]

  have laplace_integrable (α c : ℝ) (hα : 0 < α) (hc : 0 < c) :
      IntegrableOn (fun u : ℝ => u^(α-1)*Real.exp (-c*u)) (Ioi 0) volume := by
    have hi := (integrableOn_Ioi_comp_mul_left_iff
      (fun u : ℝ => Real.exp (-u)*u^(α-1)) 0 hc).mpr
        (by simpa using Real.GammaIntegral_convergent hα)
    have hj := hi.const_mul (c^(-(α-1)))
    apply IntegrableOn.congr_fun hj _ measurableSet_Ioi
    intro u hu
    dsimp only
    rw [Real.mul_rpow hc.le hu.le]
    calc
      _ = (c^(-(α-1))*c^(α-1))*(u^(α-1)*Real.exp (-c*u)) := by simp only [neg_mul]; ring
      _ = _ := by rw [←Real.rpow_add hc]; simp

  have inverse_mellin_full (α c : ℝ) (hα : 0 < α) (hc : 0 < c) :
      IntegrableOn (fun t : ℝ => t^(-α-1)*Real.exp (-c/t)) (Ioi 0) volume ∧
        (∫ t in Ioi 0, t^(-α-1)*Real.exp (-c/t)) = (1/c)^α*Real.Gamma α := by
    let g := fun u : ℝ => u^(α-1)*Real.exp (-c*u)
    have hi := laplace_integrable α c hα hc
    have hcng (t : ℝ) (ht : 0 < t) :
        (|(-1:ℝ)| *t^((-1:ℝ)-1))*g (t^(-1:ℝ)) = t^(-α-1)*Real.exp (-c/t) := by
      dsimp [g]
      norm_num only [abs_neg,abs_one,one_mul]
      rw [← Real.rpow_mul ht.le]
      rw [← mul_assoc,← Real.rpow_add ht]
      congr 2
      · ring
      · rw [Real.rpow_neg_one]
        ring
    constructor
    · have hx := (integrableOn_Ioi_comp_rpow_iff g (by norm_num : (-1:ℝ) ≠ 0)).mpr hi
      apply hx.congr_fun _ measurableSet_Ioi
      intro t ht
      simpa only [smul_eq_mul] using hcng t ht
    · have h := integral_comp_rpow_Ioi g (by norm_num : (-1:ℝ) ≠ 0)
      have he : (∫ t in Ioi 0, (|(-1:ℝ)| *t^((-1:ℝ)-1))*g (t^(-1:ℝ))) =
          ∫ t in Ioi 0, t^(-α-1)*Real.exp (-c/t) :=
        setIntegral_congr_fun measurableSet_Ioi (fun t ht => hcng t ht)
      simp only [smul_eq_mul] at h
      rw [he] at h
      rw [h]
      simpa only [g, neg_mul] using Real.integral_rpow_mul_exp_neg_mul_Ioi hα hc

  have inverse_mellin_power (α c : ℝ) (hα : 0 < α) (hc : 0 < c) :
      IntegrableOn (fun t : ℝ => t^(-α-1)*Real.exp (-c/t)) (Ioc 0 1) volume ∧
        |(∫ t in Ioc 0 1, t^(-α-1)*Real.exp (-c/t)) - (1/c)^α*Real.Gamma α| ≤ 1/α := by
    let f := fun t : ℝ => t^(-α-1)*Real.exp (-c/t)
    obtain ⟨hi, he⟩ := inverse_mellin_full α c hα hc
    have hs : IntegrableOn f (Ioc 0 1) volume := hi.mono_set (fun t ht => ht.1)
    have ht : IntegrableOn f (Ioi 1) volume := by
      apply hi.mono_set
      intro t ht
      change (1:ℝ)<t at ht
      change (0:ℝ)<t
      linarith
    have hn : ∀ t ∈ Ioi (0:ℝ), 0 ≤ f t := by
      intro t h; exact mul_nonneg (Real.rpow_nonneg h.le _) (Real.exp_pos _).le
    have hu : ∀ t ∈ Ioi (1:ℝ), f t ≤ t^(-α-1) := by
      intro t h
      have hpos : 0 < t := lt_trans zero_lt_one h
      calc
        _ ≤ t^(-α-1)*1 := mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.mpr (by exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) hpos.le)) (Real.rpow_nonneg hpos.le _)
        _ = _ := mul_one _
    have hg : IntegrableOn (fun t : ℝ => t^(-α-1)) (Ioi 1) volume :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    have hbound := setIntegral_mono_on ht hg measurableSet_Ioi hu
    have hval : (∫ t : ℝ in Ioi 1, t^(-α-1)) = 1/α := by
      rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
      simp
    rw [hval] at hbound
    have hnint : 0 ≤ ∫t in Ioi 1, f t := setIntegral_nonneg measurableSet_Ioi
      (fun t h => hn t (by change (1:ℝ)<t at h; change (0:ℝ)<t; linarith))
    have hd : Disjoint (Ioc (0:ℝ) 1) (Ioi 1) := by
      apply Set.disjoint_left.mpr
      intro t h h'; exact (not_lt_of_ge h.2) h'
    have hadd := setIntegral_union hd measurableSet_Ioi hs ht
    rw [Ioc_union_Ioi_eq_Ioi (by norm_num)] at hadd
    change (∫t in Ioi 0, f t) = _ at he
    rw [he] at hadd
    constructor
    · exact hs
    · change |(∫t in Ioc 0 1, f t) - _| ≤ _
      rw [show (∫t in Ioc 0 1, f t) - (1/c)^α*Real.Gamma α = -(∫t in Ioi 1, f t) by linarith,
        abs_neg, abs_of_nonneg hnint]
      exact hbound

  have gaussian_mellin_factor (d : ℕ) (s t r : ℝ) (ht : 0 < t) :
      t^(((d:ℝ)-s)/2-1)*(4*Real.pi*t)^(-(d:ℝ)/2)*Real.exp (-r^2/(4*t)) =
        (4*Real.pi)^(-(d:ℝ)/2)*(t^(-(s/2)-1)*Real.exp (-(r^2/4)/t)) := by
    rw [Real.mul_rpow (by positivity : 0≤4*Real.pi) ht.le]
    calc
      _ = (4*Real.pi)^(-(d:ℝ)/2)*
          ((t^(((d:ℝ)-s)/2-1)*t^(-(d:ℝ)/2))*Real.exp (-r^2/(4*t))) := by ring
      _ = _ := by
        rw [←Real.rpow_add ht]
        congr 2
        · congr 1; ring
        · congr 1; field_simp

  have gaussian_mellin_power (d : ℕ) (s : ℝ) (hs : 0<s) :
      ∃ b C : ℝ, 0<b ∧ 0≤C ∧ ∀ r : ℝ, 0<r → r<1/4 →
        IntegrableOn (fun t : ℝ => t^(((d:ℝ)-s)/2-1)*
          (4*Real.pi*t)^(-(d:ℝ)/2)*Real.exp (-r^2/(4*t))) (Ioc 0 1) volume ∧
        |(∫t in Ioc 0 1, t^(((d:ℝ)-s)/2-1)*
          (4*Real.pi*t)^(-(d:ℝ)/2)*Real.exp (-r^2/(4*t))) - b*r^(-s)| ≤ C := by
    let B := (4*Real.pi)^(-(d:ℝ)/2)
    let b := B*4^(s/2)*Real.Gamma (s/2)
    have hB : 0<B := Real.rpow_pos_of_pos (by positivity) _
    have ha : 0<s/2 := by linarith
    have hb : 0<b := mul_pos (mul_pos hB (by positivity)) (Real.Gamma_pos_of_pos ha)
    refine ⟨b,B*(1/(s/2)),hb,by positivity,?_⟩
    intro r hr _
    have hc : 0<r^2/4 := by positivity
    obtain ⟨hi, he⟩ := inverse_mellin_power (s/2) (r^2/4) ha hc
    have hf (t:ℝ) (ht:t∈Ioc (0:ℝ) 1) := gaussian_mellin_factor d s t r ht.1
    have hmain : B*((1/(r^2/4))^(s/2)*Real.Gamma (s/2)) = b*r^(-s) := by
      have hrpow : (1/(r^2/4))^(s/2) = 4^(s/2)*r^(-s) := by
        rw [show (1/(r^2/4):ℝ) = 4/(r^2) by field_simp]
        rw [Real.div_rpow (by norm_num : 0≤(4:ℝ)) (sq_nonneg r)]
        rw [←Real.rpow_natCast_mul hr.le]
        rw [div_eq_mul_inv,←Real.rpow_neg hr.le]
        congr 1
        congr 1
        norm_num
        ring
      rw [hrpow]
      dsimp [b];ring
    constructor
    · apply IntegrableOn.congr_fun (hi.const_mul B) _ measurableSet_Ioc
      intro t ht
      exact (hf t ht).symm
    · rw [setIntegral_congr_fun measurableSet_Ioc hf,integral_const_mul]
      change |B*(∫t in Ioc 0 1,t^(-(s/2)-1)*Real.exp (-(r^2/4)/t)) - b*r^(-s)| ≤ _
      rw [←hmain,←mul_sub,abs_mul,abs_of_pos hB]
      exact mul_le_mul_of_nonneg_left he hB.le

  let ml_integrand (r t:ℝ) : ℝ := t^(-1:ℝ)*Real.exp (-r^2/(4*t))

  have ml_integrable (r:ℝ) (hr:0<r) :
      IntegrableOn (ml_integrand r) (Ioc 0 1) volume := by
    have hi:=inverse_gaussian_integrable (-1) (r^2/4) (by positivity)
    apply hi.congr_fun _ measurableSet_Ioc
    intro t ht
    dsimp [ml_integrand]
    congr 2
    ring

  have ml_low_scale (r:ℝ) (hr:0<r) :
      (∫t in (0:ℝ)..r^2,ml_integrand r t) =
        ∫t in (0:ℝ)..1,t^(-1:ℝ)*Real.exp (-(1/4)/t) := by
    have hscale:=intervalIntegral.smul_integral_comp_mul_left (a:=0) (b:=1) (ml_integrand r) (r^2)
    simp only [smul_eq_mul,mul_zero,mul_one] at hscale
    rw [←hscale,←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    by_cases hz:t=0
    · subst t
      simp [ml_integrand,Real.rpow_neg_one]
    · have he : -r^2/(4*(r^2*t))=-(1/4)/t := by field_simp <;> ring
      dsimp [ml_integrand]
      rw [Real.rpow_neg_one,Real.rpow_neg_one,he,mul_inv_rev]
      field_simp

  have ml_error_pointwise (r t:ℝ) (hr:0<r) (ht:0<t) :
      0≤t⁻¹-ml_integrand r t ∧
      t⁻¹-ml_integrand r t≤(r^2/4)*t^(-2:ℝ) := by
    have hu : 0≤r^2/(4*t) := by positivity
    have hupper : Real.exp (-r^2/(4*t))≤1 := Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg r)) (by positivity))
    have hlower : 1-r^2/(4*t)≤Real.exp (-r^2/(4*t)) := by
      have h:=Real.add_one_le_exp (-r^2/(4*t))
      rw [neg_div] at h ⊢
      linarith
    have hi : 0≤t⁻¹ := by positivity
    have hlow := mul_le_mul_of_nonneg_left hupper hi
    have hhigh := mul_le_mul_of_nonneg_left hlower hi
    have hid : (r^2/4)*t^(-2:ℝ)=t⁻¹*(r^2/(4*t)) := by
      rw [Real.rpow_neg ht.le,Real.rpow_two]
      field_simp
    dsimp [ml_integrand]
    rw [Real.rpow_neg_one,hid]
    constructor <;> nlinarith

  have ml_logarithmic_bound :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r < 1/4 →
        IntegrableOn (ml_integrand r) (Ioc 0 1) volume ∧
        |(∫t in Ioc (0:ℝ) 1,ml_integrand r t)-2*Real.log (1/r)|≤C := by
    let A:=∫t in (0:ℝ)..1,t^(-1:ℝ)*Real.exp (-(1/4)/t)
    have hA : 0≤A := by
      apply intervalIntegral.integral_nonneg (by norm_num)
      intro t ht
      exact mul_nonneg (Real.rpow_nonneg ht.1 _) (Real.exp_nonneg _)
    refine ⟨A+1/4,by positivity,?_⟩
    intro r hr hrsmall
    have hr2 : 0<r^2 := sq_pos_of_pos hr
    have hr21 : r^2≤1 := by nlinarith
    have hi:=ml_integrable r hr
    refine ⟨hi,?_⟩
    have hii : IntervalIntegrable (ml_integrand r) volume 0 1 :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr hi
    have hlow : IntervalIntegrable (ml_integrand r) volume 0 (r^2) :=
      hii.mono_set (by rw [uIcc_of_le (by norm_num : (0:ℝ)≤1),uIcc_of_le hr2.le];exact Icc_subset_Icc le_rfl hr21)
    have hhigh : IntervalIntegrable (ml_integrand r) volume (r^2) 1 :=
      hii.mono_set (by rw [uIcc_of_le (by norm_num : (0:ℝ)≤1),uIcc_of_le hr21];exact Icc_subset_Icc hr2.le le_rfl)
    have hinv : IntervalIntegrable (fun t:ℝ=>t⁻¹) volume (r^2) 1 := by
      apply ContinuousOn.intervalIntegrable
      apply continuousOn_inv₀.mono
      intro t ht
      exact ne_of_gt (hr2.trans_le ((uIcc_of_le hr21 ▸ ht).1))
    have hpow : IntervalIntegrable (fun t:ℝ=>t^(-2:ℝ)) volume (r^2) 1 :=
      intervalIntegral.intervalIntegrable_rpow (Or.inr (notMem_uIcc_of_lt hr2 (by norm_num)))
    let E:=∫t in r^2..1,t⁻¹-ml_integrand r t
    have hE : 0≤E := by
      apply intervalIntegral.integral_nonneg hr21
      intro t ht
      exact (ml_error_pointwise r t hr (hr2.trans_le ht.1)).1
    have hEB : E≤1/4 := by
      calc
        _ ≤ ∫t in r^2..1,(r^2/4)*t^(-2:ℝ) :=
          intervalIntegral.integral_mono_on hr21 (hinv.sub hhigh) (hpow.const_mul _)
            (fun t ht=>(ml_error_pointwise r t hr (hr2.trans_le ht.1)).2)
        _ = (r^2/4)*((r^2)⁻¹-1) := by
          rw [intervalIntegral.integral_const_mul,integral_rpow
            (Or.inr ⟨by norm_num,notMem_uIcc_of_lt hr2 (by norm_num)⟩)]
          norm_num only [show (-2:ℝ)+1=-1 by norm_num,Real.rpow_neg_one,inv_one]
          ring
        _ ≤ 1/4 := by
          have he : (r^2/4)*((r^2)⁻¹-1)=1/4-r^2/4 := by field_simp
          rw [he]
          linarith [sq_nonneg r]
    have hlog : (∫t in r^2..1,t⁻¹)=2*Real.log (1/r) := by
      rw [integral_inv_of_pos hr2 (by norm_num),one_div,Real.log_inv,Real.log_pow,
        one_div,Real.log_inv]
      norm_num
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hlow hhigh
    have hloweq := ml_low_scale r hr
    have herror : (∫t in r^2..1,ml_integrand r t)=2*Real.log (1/r)-E := by
      dsimp [E]
      rw [intervalIntegral.integral_sub hinv hhigh,hlog]
      ring
    rw [←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),←hsplit,hloweq,herror]
    change |A+(2*Real.log (1/r)-E)-2*Real.log (1/r)|≤A+1/4
    have heq : A+(2*Real.log (1/r)-E)-2*Real.log (1/r)=A-E := by ring
    rw [heq]
    exact (abs_sub _ _).trans (by rw [abs_of_nonneg hA,abs_of_nonneg hE];linarith)

  have ml_gaussian_logarithmic_bound (d:ℕ) :
      ∃ b C : ℝ, 0 < b ∧ 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r < 1/4 →
        IntegrableOn (fun t:ℝ => t^((d:ℝ)/2-1)*(4*Real.pi*t)^(-(d:ℝ)/2)*
          Real.exp (-r^2/(4*t))) (Ioc 0 1) volume ∧
        |(∫t in Ioc (0:ℝ) 1,t^((d:ℝ)/2-1)*(4*Real.pi*t)^(-(d:ℝ)/2)*
          Real.exp (-r^2/(4*t)))-b*Real.log (1/r)|≤C := by
    obtain ⟨C,hC,hbound⟩:=ml_logarithmic_bound
    let c:ℝ:=(4*Real.pi)^(-(d:ℝ)/2)
    have hc : 0<c := Real.rpow_pos_of_pos (by positivity) _
    refine ⟨2*c,c*C,by positivity,by positivity,?_⟩
    intro r hr hrs
    obtain ⟨hi,herr⟩:=hbound r hr hrs
    have heq (t:ℝ) (ht:0<t) :
        t^((d:ℝ)/2-1)*(4*Real.pi*t)^(-(d:ℝ)/2)*Real.exp (-r^2/(4*t))=
          c*ml_integrand r t := by
      rw [Real.mul_rpow (by positivity : 0≤4*Real.pi) ht.le]
      dsimp only [c,ml_integrand]
      calc
        _ = (4*Real.pi)^(-(d:ℝ)/2)*(t^((d:ℝ)/2-1)*t^(-(d:ℝ)/2))*
          Real.exp (-r^2/(4*t)) := by ring
        _ = _ := by
          rw [←Real.rpow_add ht]
          have hsum : (d:ℝ)/2-1+(-(d:ℝ)/2)=(-1:ℝ) := by ring
          rw [hsum]
          ring
    constructor
    · have hcint : IntegrableOn (fun t=>c*ml_integrand r t) (Ioc 0 1) volume := hi.const_mul c
      apply hcint.congr_fun _ measurableSet_Ioc
      intro t ht
      exact (heq t ht.1).symm
    · have hint : (∫t in Ioc (0:ℝ) 1,t^((d:ℝ)/2-1)*(4*Real.pi*t)^(-(d:ℝ)/2)*
          Real.exp (-r^2/(4*t))) = c*(∫t in Ioc (0:ℝ) 1,ml_integrand r t) := by
        rw [←integral_const_mul]
        exact setIntegral_congr_fun measurableSet_Ioc (fun t ht=>heq t ht.1)
      rw [hint]
      have hfac : c*(∫t in Ioc (0:ℝ) 1,ml_integrand r t)-(2*c)*Real.log (1/r)=
          c*((∫t in Ioc (0:ℝ) 1,ml_integrand r t)-2*Real.log (1/r)) := by ring
      rw [hfac,abs_mul,abs_of_pos hc]
      exact mul_le_mul_of_nonneg_left herr hc.le
  by_cases hz:s=0
  · subst s
    obtain ⟨b,C,hb,hC,h⟩ := ml_gaussian_logarithmic_bound d
    exact ⟨b,C,hb,hC,by simpa using h⟩
  · obtain ⟨b,C,hb,hC,h⟩ := gaussian_mellin_power d s (lt_of_le_of_ne hs (Ne.symm hz))
    exact ⟨b,C,hb,hC,by simpa [hz] using h⟩
