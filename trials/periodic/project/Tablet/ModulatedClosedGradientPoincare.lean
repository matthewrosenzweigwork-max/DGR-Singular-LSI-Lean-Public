module

public import Tablet.UniformClosedGradientPoincare
public import Tablet.CanonicalGradientCoreEquality
public import Tablet.RieszModulatedBackground
public import Tablet.ModulatedPotentialLawRewrite
public import Tablet.BackgroundPotential
public import Tablet.BackgroundPairMean

@[expose] public section
open MeasureTheory ProbabilityTheory Set
-- [TABLET NODE: ModulatedClosedGradientPoincare]
theorem ModulatedClosedGradientPoincare (d:ℕ)(hd:2≤d)(s a B l u:ℝ)
    (hs:0≤s)(hsd:s≤(d:ℝ)-2) (ha:0<a)(hB:0≤B)(hl:0<l)(hl1:l≤1)(hu:1≤u) :
    ∃rate:ℝ,0<rate ∧ ∀N:ℕ,2≤N→∀β:ℝ,0≤β→β≤B→
      ∀ε:ℝ,0≤ε→∀r:BoundedBackground d l u,
      let g:=RieszKernel d s a ε
      let h:=BackgroundPotential g r.density
      let J:=BackgroundPairMean g r.density
      let P:=NormalizedTilt (volume:Measure (Configuration d N))
        (fun X=>Real.exp (-β*(PairEnergy g X-(∑i:Fin N,h (X i))+(N:ℝ)*(J/2)))*ProductDensity r.density X)
      GradientGraphClosure P false=GradientGraphClosure P true ∧
      GradientFormDomain P false=GradientFormDomain P true ∧
      (∀f:Lp ℝ 2 P,f∈GradientFormDomain P false→
        ∃!v:Lp (EuclideanSpace ℝ (Fin N×Fin d)) 2 P,(f,v)∈GradientGraphClosure P false) ∧
      (∀(f:Lp ℝ 2 P)(v:Lp (EuclideanSpace ℝ (Fin N×Fin d)) 2 P),
        (f,v)∈GradientGraphClosure P false→
        variance (f:Configuration d N→ℝ) P≤rate⁻¹*ClosedGradientEnergy v) :=by
-- BODY
  have hsd':s<(d:ℝ):=by linarith
  obtain ⟨H,hH,hmod⟩:=RieszModulatedBackground d hd s a l u B hs hsd' ha hl hl1 hu hB
  have hlo:0<l*Real.exp (-2*B*H):=mul_pos hl (Real.exp_pos _)
  have hlo1:l*Real.exp (-2*B*H)≤1:=by
    have he:Real.exp (-2*B*H)≤1:=Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hB hH])
    exact (mul_le_mul_of_nonneg_left he hl.le).trans (by simpa using hl1)
  have hhi1:1≤u*Real.exp (2*B*H):=by
    have he:1≤Real.exp (2*B*H):=Real.one_le_exp_iff.mpr (by positivity)
    exact hu.trans (by simpa using mul_le_mul_of_nonneg_left he (zero_le_one.trans hu))
  obtain ⟨rate,hrate,hPI⟩:=UniformClosedGradientPoincare d hd s a B
    (l*Real.exp (-2*B*H)) (u*Real.exp (2*B*H)) hs hsd ha hB hlo hlo1 hhi1
  refine ⟨rate,hrate,?_⟩
  intro N hN β hβ hβB ε hε r
  obtain ⟨q,hq⟩:=hmod ε hε r β hβ hβB
  let h:=BackgroundPotential (RieszKernel d s a ε) r.density
  let Z:=∫y,r.density y*Real.exp (β*h y)
  have hdef : h = (fun x => ∫ y, RieszKernel d s a ε (x-y)*r.density y) := by
    funext x
    simp only [h, BackgroundPotential, convolution, ContinuousLinearMap.mul_apply', mul_comm]
  have hqd:q.density=(fun x=>r.density x*Real.exp (β*h x)/Z):=by
    dsimp [Z]
    rw [hdef]
    exact funext hq
  have hZn:0≤Z:=by
    apply integral_nonneg_of_ae
    filter_upwards [r.bounds] with x hx
    exact mul_nonneg (hl.le.trans hx.1) (Real.exp_pos _).le
  have hZne:Z≠0:=by
    intro hz
    have hzero:q.density=(fun _=>0):=by
      rw [hqd]
      funext x
      simp [hz]
    have hm:=q.mass
    rw [hzero,integral_zero] at hm
    norm_num at hm
  have hZ:0<Z:=lt_of_le_of_ne hZn (Ne.symm hZne)
  have heq:=ModulatedPotentialLawRewrite d N (RieszKernel d s a ε) r.density h β
    (BackgroundPairMean (RieszKernel d s a ε) r.density/2) Z hZ
  rw [←hqd] at heq
  dsimp only
  rw [heq]
  have hc:=CanonicalGradientCoreEquality d N hd hN s a _ _ β hs hsd' ha q hβ ε hε
  exact ⟨hc.1,hc.2.1,hc.2.2,hPI N hN β hβ hβB q ε hε⟩
