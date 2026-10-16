import Tablet.GenericSmoothCapacitaryCutoff
import Tablet.CoulombOriginDivergence
import Tablet.RieszHeatSource
import Tablet.ConfigurationPairPotential
import Tablet.CollisionFreeCore
open MeasureTheory Set Filter
open scoped ContDiff Topology
-- [TABLET NODE: CollisionFreeSmoothCutoff]
theorem CollisionFreeSmoothCutoff (d N:ℕ)(hd:2≤d)(hN:2≤N) :
    ∃C:ℝ,0<C ∧ ∀T:ℝ,0<T→∃χ:Configuration d N→ℝ,
      χ∈CollisionFreeCore d N ∧ (∀X,0≤χ X ∧ χ X≤1) ∧
      (∫X,(χ X-1)^2)+(∫X,‖CoordinateGradient χ X‖^2)≤C/T := by
-- BODY
  classical
  have quotient (d : ℕ) : IsOpenQuotientMap (TorusLift d) := by
      have hc : IsOpenQuotientMap ((↑) : ℝ → AddCircle (1 : ℝ)) :=
        QuotientAddGroup.isOpenQuotientMap_mk
      have hp : IsOpenQuotientMap
          (Pi.map (fun _ : Fin d => ((↑) : ℝ → AddCircle (1 : ℝ)))) :=
        IsOpenQuotientMap.piMap (fun _ => hc)
      exact hp.comp (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isOpenQuotientMap
  have torus_smooth_continuous {d : ℕ} {f : UnitAddTorus (Fin d) → ℝ}
        (hf : TorusSmooth f) : Continuous f := by
      apply (quotient d).continuous_comp_iff.mp
      exact hf.continuous

  have hdr : (2:ℝ)≤(d:ℝ) := by exact_mod_cast hd
  have hNr : (2:ℝ)≤(N:ℝ) := by exact_mod_cast hN
  have hs : 0≤(d:ℝ)-2 := by linarith
  have hsd : (d:ℝ)-2<(d:ℝ) := by linarith
  obtain ⟨c,hc,hall⟩ := RieszL1Foundation d hd ((d:ℝ)-2) 1 hs hsd zero_lt_one
  obtain ⟨M,hM,_,_,hsource⟩ := RieszHeatSource d hd ((d:ℝ)-2) 1 1 hs
    (le_refl _) zero_lt_one zero_lt_one
  obtain ⟨ψ,D,hD,hψ,hcut⟩ := GenericSmoothCapacitaryCutoff
  let K : ℝ := (N:ℝ)*((N:ℝ)-1)*c/2
  let L : ℝ := (N:ℝ)*((N:ℝ)-1)*M
  have hNm1 : 0≤(N:ℝ)-1 := by linarith
  have hK : 0≤K := by dsimp[K];positivity
  have hL : 0≤L := by dsimp[L];positivity
  let C : ℝ := 4*K+D^2*L+1
  have hC : 0<C := by dsimp[C];positivity
  refine ⟨C,hC,?_⟩
  intro T hT
  have horigin : ∀ᶠε:ℝ in 𝓝[>]0,2*T-c<RieszKernel d ((d:ℝ)-2) 1 ε 0 :=
    (CoulombOriginDivergence d hd).eventually (eventually_gt_atTop (2*T-c))
  have hpositive : ∀ᶠ ε:ℝ in 𝓝[>]0,0<ε := self_mem_nhdsWithin
  obtain ⟨ε,hε,hlarge⟩ := (hpositive.and horigin).exists
  have hεpos : 0<ε := hε
  let g := RieszKernel d ((d:ℝ)-2) 1 ε
  let G := fun x=>g x+c
  have hgi : Integrable g volume := (hall ε hεpos.le).2.1
  have hg0 : (∫x,g x)=0 := (hall ε hεpos.le).2.2.1
  have hGn : ∀x,0≤G x := by
    intro x
    have hh := (hall ε hεpos.le).2.2.2.2.1 x
    dsimp[G,g]
    linarith
  have hGs : TorusSmooth G := by
    exact ((RieszLocalStructure d hd ((d:ℝ)-2) 1 hs hsd zero_lt_one).2.1 ε hεpos).add contDiff_const
  have hGmean : (∫x,G x)=c := by
    have hprob : IsProbabilityMeasure (volume : Measure (AddCircle (1:ℝ))) := by
      rw [AddCircle.volume_eq_smul_haarAddCircle]
      simp
      infer_instance
    letI := hprob
    dsimp[G]
    rw [integral_add hgi (integrable_const c),hg0,zero_add]
    simp
  have hGΔ : ∀x,TorusLaplacian G x≤M := by
    intro x
    have heq : TorusLaplacian G x=TorusLaplacian g x := by
      unfold TorusLaplacian
      dsimp[G]
      simp_rw [fderiv_add_const]
    rw [heq]
    exact (hsource ε hεpos).2.2.2 x
  let V := fun X:Configuration d N=>(N:ℝ)*PairEnergy G X
  let Vf := fun x=>V ((ConfigurationFlatten d N).symm x)
  have hp := ConfigurationPairPotential d N hN G hGs hGn M (N:ℝ) hM (by positivity) hGΔ
  have hV : V∈SmoothCore d N := hp.1
  have hVfs : TorusSmooth Vf := hp.2.1
  have hVp : ∀X,0≤V X := hp.2.2.1
  have hmean : (∫X,V X)=K := by
    have hh := hp.2.2.2.1
    rw [hGmean] at hh
    exact hh
  have hLap : ∀x,TorusLaplacian Vf x≤L := hp.2.2.2.2.2
  have hcalc := ConfigurationCalculus d N
  let e : Configuration d N ≃ᵐ UnitAddTorus (Fin (N*d)) :=
    {toEquiv:=ConfigurationFlatten d N,measurable_toFun:=hcalc.1,measurable_invFun:=hcalc.2.1}
  have hmp : MeasurePreserving e volume volume := ⟨hcalc.1,hcalc.2.2.1⟩
  have hmeanf : (∫x,Vf x)≤K := by
    have hi := hmp.integral_comp' Vf
    simp [e,Vf] at hi
    rw [←hi,hmean]
  have hposf : ∀x,0≤Vf x := fun x=>hVp _
  have hχf := hcut (N*d) Vf hVfs K L hK hL hposf hmeanf hLap T hT
  let χ := fun X:Configuration d N=>ψ (V X/T)
  let χf := fun x=>ψ (Vf x/T)
  have hVl : ContDiff ℝ ∞ (fun y=>V (ConfigurationLift d N y)) := hV
  have hχs : χ∈SmoothCore d N := hψ.comp (hVl.div_const T)
  have hχbd : ∀X,0≤χ X ∧ χ X≤1 := by
    intro X
    simpa only [Vf,χ,Equiv.symm_apply_apply] using hχf.2.1 (ConfigurationFlatten d N X)
  have hVsum (X:Configuration d N) : V X=∑i:Fin N,∑j:Fin N,if i<j then G (X i-X j) else 0 := by
    have hNz : (N:ℝ)≠0 := by exact_mod_cast (by omega : N≠0)
    dsimp[V,PairEnergy]
    field_simp
  have hcollision : ∀X∈CollisionSet d N,T<V X := by
    intro X hX
    obtain ⟨i,j,hij,heq⟩ := hX
    have hterm (i j:Fin N) : 0≤(if i<j then G (X i-X j) else (0:ℝ)) := by
      split_ifs
      · exact hGn _
      · norm_num
    have hj := Finset.single_le_sum (fun k _=>hterm i k) (Finset.mem_univ j)
    have hi : (∑ l:Fin N,if i<l then G (X i-X l) else 0) ≤
        ∑ k:Fin N,∑ l:Fin N,if k<l then G (X k-X l) else 0 :=
      Finset.single_le_sum (fun k _=>Finset.sum_nonneg (fun l _=>hterm k l)) (Finset.mem_univ i)
    have hdiffzero : X i-X j=0 := sub_eq_zero.mpr heq
    rw [if_pos hij,hdiffzero] at hj
    have hh : G 0≤V X := by rw[hVsum];exact hj.trans hi
    dsimp[G,g] at hh
    linarith
  have hflatc : Continuous (ConfigurationFlatten d N) := by
    apply continuous_pi
    intro k
    exact (continuous_apply (finProdFinEquiv.symm k).2).comp
      (continuous_apply (finProdFinEquiv.symm k).1)
  have hVcont : Continuous V := by
    have hh := (torus_smooth_continuous hVfs).comp hflatc
    simpa only [Vf,Function.comp_def,Equiv.symm_apply_apply] using hh
  have hzero (X)(hx:T≤V X) : χ X=0 := by
    simpa only [Vf,χ,Equiv.symm_apply_apply] using hχf.2.2.2.1 (ConfigurationFlatten d N X) (by simpa only [Vf,Equiv.symm_apply_apply] using hx)
  have hsupport : tsupport χ⊆{X|V X≤T} := by
    apply closure_minimal _ (isClosed_le hVcont continuous_const)
    intro X hx
    by_contra hh
    exact hx (hzero X (le_of_not_ge hh))
  have hdisj : Disjoint (tsupport χ) (CollisionSet d N) := by
    apply Set.disjoint_left.mpr
    intro X hx hcol
    exact (not_le_of_gt (hcollision X hcol)) (hsupport hx)
  have hdefect : (∫X,(χ X-1)^2)≤4*K/T := by
    have hi := hmp.integral_comp' (fun x=>(χf x-1)^2)
    simp [e,χf,Vf] at hi
    exact hi.trans_le hχf.2.2.2.2.1
  have henergy : (∫X,‖CoordinateGradient χ X‖^2)≤D^2*L/T := by
    have hnorm := (hcalc.2.2.2 χ hχs).2.2.2.2.2.1
    have hi := hmp.integral_comp' (fun x=>‖TorusGradient χf x‖^2)
    change (∫X,‖TorusGradient (fun x=>χ ((ConfigurationFlatten d N).symm x)) (ConfigurationFlatten d N X)‖^2)=_ at hi
    simp_rw [hnorm] at hi
    exact hi.trans_le hχf.2.2.2.2.2
  refine ⟨χ,⟨hχs,hdisj⟩,hχbd,?_⟩
  have hh := add_le_add hdefect henergy
  have he : 4*K/T+D^2*L/T=(4*K+D^2*L)/T := by ring
  rw [he] at hh
  exact hh.trans (div_le_div_of_nonneg_right (by dsimp[C];linarith) hT.le)

