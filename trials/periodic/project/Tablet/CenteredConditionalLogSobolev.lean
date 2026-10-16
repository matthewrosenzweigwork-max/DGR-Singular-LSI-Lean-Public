import Tablet.HolesLogSobolev
import Tablet.ConditionalPotential
import Mathlib.MeasureTheory.Group.Integral
open MeasureTheory
open scoped ContDiff
-- [TABLET NODE: CenteredConditionalLogSobolev]
theorem CenteredConditionalLogSobolev (d:ℕ)(hd:2≤d)(s a B qlo qhi H:ℝ)
    (hs:0≤s)(hsd:s≤(d:ℝ)-2)(hL:s<(d:ℝ)/2)(ha:0<a)(hB:0≤B)
    (hqlo:0<qlo)(hqhi:0<qhi)(hH:0≤H) :
    ∃σ:ℝ,0<σ ∧ ∀(q h:UnitAddTorus (Fin d)→ℝ),Measurable q→Measurable h→
      (∀ᵐx,qlo≤q x ∧ q x≤qhi)→(∀ᵐx,|h x|≤H)→
      ∀(N:ℕ),2≤N→∀β:ℝ,0≤β→β≤B→∀ε:ℝ,0<ε→
      ∀(X:Configuration d N)(i:Fin N),
      let ν:=NormalizedTilt volume (fun z=>q z*Real.exp (-β*h z/(N:ℝ))*
        Real.exp (-ConditionalPotential (RieszKernel d s a ε) β X i z))
      ∀f:UnitAddTorus (Fin d)→ℝ,TorusSmooth f→
        Entropy ν (fun z=>f z^2)≤(2/σ)*(∫z,‖TorusGradient f z‖^2∂ν) := by
-- BODY
  classical
  obtain ⟨ρ,hρ,hHoles⟩:=HolesLogSobolev d hd s a B hs hsd hL ha hB
  let l:=qlo*Real.exp (-(B*H/2))
  let u:=qhi*Real.exp (B*H/2)
  let σ:=(qlo/qhi)*Real.exp (-B*H)*ρ
  have hσ:0<σ:=mul_pos (mul_pos (div_pos hqlo hqhi) (Real.exp_pos _)) hρ
  refine ⟨σ,hσ,?_⟩
  intro q h hqm hhm hqb hhb N hN β hβ hβB ε hε X i
  dsimp only
  intro f hf
  have hNreal:2≤(N:ℝ):=by exact_mod_cast hN
  have hNpos:0<(N:ℝ):=by linarith
  have hβN:0≤β/(N:ℝ):=div_nonneg hβ hNpos.le
  have hβNB:β/(N:ℝ)≤B/2:=by
    apply (div_le_iff₀ hNpos).mpr
    have hBN:=mul_le_mul_of_nonneg_left hNreal hB
    nlinarith
  let b:=fun z=>q z*Real.exp (-β*h z/(N:ℝ))
  have hbm:Measurable b:=hqm.mul (((hhm.const_mul (-β)).div_const (N:ℝ)).exp)
  have hl:0<l:=mul_pos hqlo (Real.exp_pos _)
  have hb:∀ᵐz,l≤b z ∧ b z≤u:=by
    filter_upwards [hqb,hhb] with z hz hzh
    have helo:Real.exp (-(B*H/2))≤Real.exp (-β*h z/(N:ℝ)):=by
      apply Real.exp_le_exp.mpr
      have h1:=mul_le_mul_of_nonneg_left (abs_le.mp hzh).2 hβN
      have h2:=mul_le_mul_of_nonneg_right hβNB hH
      calc
        -(B*H/2)≤-(β/(N:ℝ)*h z):=by nlinarith
        _ = -β*h z/(N:ℝ):=by ring
    have hehi:Real.exp (-β*h z/(N:ℝ))≤Real.exp (B*H/2):=by
      apply Real.exp_le_exp.mpr
      have h1:=mul_le_mul_of_nonneg_left (abs_le.mp hzh).1 hβN
      have h2:=mul_le_mul_of_nonneg_right hβNB hH
      calc
        -β*h z/(N:ℝ)=-(β/(N:ℝ)*h z):=by ring
        _ ≤ B*H/2:=by nlinarith
    exact ⟨mul_le_mul hz.1 helo (Real.exp_pos _).le (hqlo.le.trans hz.1),
      mul_le_mul hz.2 hehi (Real.exp_pos _).le (hqhi.le)⟩
  let w:Fin N→ℝ:=fun j=>if j=i then 0 else β/(N:ℝ)
  have hw:∀j,0≤w j:=by intro j;dsimp[w];split <;> positivity
  have hmass:(∑j,w j)≤B:=by
    have hsum:(∑j,w j)≤∑j:Fin N,β/(N:ℝ):=by
      apply Finset.sum_le_sum
      intro j hj
      dsimp[w]
      split <;> linarith
    have hc:(∑j:Fin N,β/(N:ℝ))=β:=by
      simp [Finset.sum_const, nsmul_eq_mul]
      field_simp
    rw[hc] at hsum
    exact hsum.trans hβB
  have hpot:AtomicPotential (RieszKernel d s a ε) w X=
      ConditionalPotential (RieszKernel d s a ε) β X i:=by
    funext z
    unfold AtomicPotential ConditionalPotential
    rw[Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp[w]
    by_cases hj : j=i
    · simp only [hj,if_true,if_false,zero_mul,mul_zero]
    · simp only [hj,if_false,if_true]
  have hlocal:Entropy (NormalizedTilt volume (fun z=>b z*Real.exp
      (-ConditionalPotential (RieszKernel d s a ε) β X i z))) (fun z=>f z^2)≤
        (u/l)*(2/ρ)*(∫z,‖TorusGradient f z‖^2∂NormalizedTilt volume (fun z=>b z*Real.exp
          (-ConditionalPotential (RieszKernel d s a ε) β X i z))):=by
    have hloc:=(hHoles N w X hw hmass ε hε).2 b l u hbm hl hb f hf
    rwa[hpot] at hloc
  have hfactor:(u/l)*(2/ρ)=2/σ:=by
    have hexp:Real.exp (B*H/2)/Real.exp (-(B*H/2))=Real.exp (B*H):=by
      rw[←Real.exp_sub]
      congr 1
      ring
    dsimp [u,l,σ]
    rw[mul_div_mul_comm,hexp]
    rw [show -B*H=-(B*H) by ring,Real.exp_neg]
    field_simp [hρ.ne',hqlo.ne',hqhi.ne',Real.exp_ne_zero]
    <;> ring
  rwa[hfactor] at hlocal
