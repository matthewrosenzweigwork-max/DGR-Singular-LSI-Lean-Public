import Tablet.HeatReplacementGap
import Tablet.JumpPhysicalComparison
import Tablet.FiniteParticlePoincare
import Tablet.RieszFourierCoefficients
open MeasureTheory Filter Set UnitAddTorus
set_option maxHeartbeats 1500000
-- [TABLET NODE: UniformRegularizedPoincare]
theorem UniformRegularizedPoincare (d : ℕ) (hd : 2 ≤ d)
    (s a B l u : ℝ) (hs : 0 ≤ s) (hsd : s ≤ (d : ℝ) - 2)
    (ha : 0 < a) (hB : 0 ≤ B) (hl : 0 < l) (hl1 : l ≤ 1) (hu : 1 ≤ u) :
    ∃ rate : ℝ, 0 < rate ∧ ∀ (N : ℕ), 2 ≤ N →
      ∀ (β : ℝ), 0 ≤ β → β ≤ B → ∀ (q : BoundedBackground d l u),
      ∀ (ε : ℝ), 0 < ε → ∀ (f : Configuration d N → ℝ),
      f ∈ SmoothCore d N →
        ProbabilityTheory.variance f
          (CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β) ≤
        rate⁻¹ * PhysicalEnergy
          (CanonicalLaw (N := N) (RieszKernel d s a ε) q.density β) f := by
-- BODY
  have tilt_scale {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (w : Ω→ℝ) (t : ℝ) (ht : t≠0) :
      NormalizedTilt μ (fun x=>t*w x)=NormalizedTilt μ w := by
    unfold NormalizedTilt
    simp only [integral_const_mul]
    congr 1
    funext x
    congr 1
    exact mul_div_mul_left _ _ ht

  have canonical_shift {d N : ℕ} (G q : UnitAddTorus (Fin d)→ℝ) (β c : ℝ) :
      CanonicalLaw (N:=N) (fun x=>G x+c) q β=CanonicalLaw (N:=N) G q β := by
    classical
    let C : ℝ := (N:ℝ)⁻¹*∑i:Fin N,∑j:Fin N,if i<j then c else 0
    have hp (X : Configuration d N) : PairEnergy (fun x=>G x+c) X=PairEnergy G X+C := by
      have hh i j : (if i<j then G (X i-X j)+c else (0:ℝ)) =
        (if i<j then G (X i-X j) else 0)+(if i<j then c else 0) := by split_ifs <;>ring
      unfold PairEnergy
      simp_rw [hh,Finset.sum_add_distrib]
      dsimp [C]
      ring
    unfold CanonicalLaw
    have he : GibbsWeight (N:=N) (fun x=>G x+c) q β=fun X=>Real.exp (-β*C)*GibbsWeight G q β X := by
      funext X
      unfold GibbsWeight
      rw [hp,show -β*(PairEnergy G X+C) = -β*C + -β*PairEnergy G X by ring,Real.exp_add]
      ring
    rw [he]
    exact tilt_scale _ _ _ (ne_of_gt (Real.exp_pos _))

  have heat_add_const (d : ℕ) (t : ℝ) (ht : 0<t) (G : UnitAddTorus (Fin d)→ℝ)
      (hi : Integrable G volume) (c : ℝ) :
      HeatSemigroup d t (fun x=>G x+c)=fun x=>HeatSemigroup d t G x+c := by
    have hK := HeatKernelFacts d t ht
    obtain ⟨C,hC⟩ := (isCompact_univ : IsCompact (univ : Set (UnitAddTorus (Fin d)))).exists_bound_of_continuousOn hK.1.continuousOn
    have hKb : ∀ᵐx∂(volume : Measure (UnitAddTorus (Fin d))), ‖HeatKernel d t x‖≤C := Eventually.of_forall fun x => hC x (mem_univ x)
    have hKi : Integrable (HeatKernel d t) volume := Integrable.of_bound hK.1.measurable.aestronglyMeasurable C hKb
    funext x
    have hp := (hi.comp_sub_left x).bdd_mul hK.1.measurable.aestronglyMeasurable hKb
    dsimp [HeatSemigroup]
    simp only [mul_add]
    rw [integral_add hp (hKi.mul_const c),integral_mul_const,hK.2.2.2.1,one_mul]

  have char_norm {d : ℕ} (k : Fin d→ℤ) (x : UnitAddTorus (Fin d)) : ‖mFourier k x‖=1 := by
    simp only [mFourier,ContinuousMap.coe_mk,norm_prod,fourier_apply,Circle.norm_coe,Finset.prod_const_one]

  have char_mean_zero {d : ℕ} (k : Fin d→ℤ) (hk : k≠0) : ∫x,(mFourier k x).re=0 := by
    have hvol : (volume : Measure (UnitAddTorus (Fin d))) = Measure.pi (fun _:Fin d=>AddCircle.haarAddCircle) := by
      change Measure.pi _ = _
      congr 1
      funext i
      rw [AddCircle.volume_eq_smul_haarAddCircle]
      simp
    have ho := (orthonormal_iff_ite.mp (orthonormal_mFourier (d:=Fin d))) 0 k
    simp only [ContinuousMap.inner_toLp,mFourier_zero,ContinuousMap.one_apply,map_one,mul_one] at ho
    change (∫x,mFourier k x∂Measure.pi (fun _:Fin d=>AddCircle.haarAddCircle)) = _ at ho
    rw [←hvol] at ho
    have ho' : (∫x,mFourier k x∂(volume : Measure (UnitAddTorus (Fin d))))=0 := by simpa [Ne.symm hk] using ho
    have hi : Integrable (mFourier k) (volume : Measure (UnitAddTorus (Fin d))) :=
      (mFourier k).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    simpa [ho'] using integral_re hi

  have shifted_fourier (d : ℕ) (hd : 2≤d) (s a c : ℝ) (hs : 0≤s) (hsd : s<(d:ℝ)) (ha : 0<a) (hc : 0≤c)
      (hi : Integrable (RieszKernel d s a 0) volume) (hmean : ∫x,RieszKernel d s a 0 x=0) :
      ∀k:Fin d→ℤ,0≤∫x,(RieszKernel d s a 0 x+c)*(mFourier k x).re := by
    haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1:ℝ))) := by
      rw [AddCircle.volume_eq_smul_haarAddCircle]; simp; infer_instance
    intro k
    by_cases hk:k=0
    · subst k
      simp only [mFourier_zero,ContinuousMap.one_apply,Complex.one_re,mul_one]
      rw [integral_add hi (integrable_const c),hmean]
      simpa using hc
    · have hmi : Integrable (fun x=>RieszKernel d s a 0 x*(mFourier k x).re) volume :=
        hi.mul_bdd ((Complex.measurable_re.comp (mFourier k).continuous.measurable).aestronglyMeasurable)
          (Eventually.of_forall fun x=>by
            rw [Real.norm_eq_abs]
            exact (Complex.abs_re_le_norm _).trans_eq (char_norm k x))
      have hci : Integrable (fun x=>c*(mFourier k x).re) volume :=
        ((Complex.continuous_re.comp (mFourier k).continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul c
      simp only [add_mul]
      rw [integral_add hmi hci,integral_const_mul,char_mean_zero k hk,mul_zero,add_zero,
        RieszFourierCoefficients d hd s a 0 hs hsd ha (le_refl 0) k hk]
      exact mul_nonneg (mul_nonneg ha.le (Real.rpow_nonneg (by positivity) _)) (Real.exp_pos _).le
  classical
  haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1:ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp; infer_instance
  let m : Measure (UnitAddTorus (Fin d)) := volume
  have hsd' : s<(d:ℝ) := by linarith
  obtain ⟨c,hc,hR⟩ := RieszL1Foundation d hd s a hs hsd' ha
  have hR0 := hR 0 (le_refl 0)
  let G := fun x=>RieszKernel d s a 0 x+c
  have hG : Measurable G := hR0.1.add_const c
  have hi : Integrable G m := hR0.2.1.add (integrable_const c)
  have hn : ∀x,0≤G x := fun x=>by dsimp [G]; linarith [hR0.2.2.2.2.1 x]
  have he : ∀x,G (-x)=G x := fun x=>by dsimp [G]; rw [hR0.2.2.2.1]
  have hF : ∀k:Fin d→ℤ,0≤∫x,G x*(mFourier k x).re∂m :=
    shifted_fourier d hd s a c hs hsd' ha hc hR0.2.1 hR0.2.2.1
  have hmean : ∫x,G x∂m=c := by
    rw [integral_add hR0.2.1 (integrable_const c),hR0.2.2.1]
    simp
  obtain ⟨N₀,hN₀,hgap⟩ := HeatReplacementGap d G hG hi hn he hF B u hB hu
  obtain ⟨r,hRpos,hphys⟩ := JumpPhysicalComparison d hd s a B hs hsd ha hB
  let Clarge := 2*Real.exp (B*u*c)*(u/l)*r⁻¹
  have hClarge : 0<Clarge := by dsimp [Clarge]; positivity
  have hlarge : ∀N:ℕ,N₀≤N→∀β:ℝ,0≤β→β≤B→∀q:BoundedBackground d l u,
      ∀ε:ℝ,0<ε→∀f:Configuration d N→ℝ,f∈SmoothCore d N→
        ProbabilityTheory.variance f (CanonicalLaw (N:=N) (RieszKernel d s a ε) q.density β) ≤
          Clarge*PhysicalEnergy (CanonicalLaw (N:=N) (RieszKernel d s a ε) q.density β) f := by
    intro N hN β hβ hβB q ε hε f hfs
    have hN2 := hN₀.trans hN
    have hRe := hR ε hε.le
    have hGs : (if ε=0 then G else HeatSemigroup d ε G) = fun x=>RieszKernel d s a ε x+c := by
      rw [if_neg (ne_of_gt hε),heat_add_const d ε hε (RieszKernel d s a 0) hR0.2.1 c]
      funext x
      rw [hRe.2.2.2.2.2.2 hε x]
    have hge := hgap ε hε.le
    dsimp only at hge
    rw [hGs] at hge
    let P := CanonicalLaw (N:=N) (fun x=>RieszKernel d s a ε x+c) q.density β
    haveI : IsProbabilityMeasure P := (JumpConditionalBalance d N hN2 l u β q hβ
      (fun x=>RieszKernel d s a ε x+c) hge.1 hge.2.1 hge.2.2.1 hge.2.2.2.1).1
    have hcal := (ConfigurationCalculus d N).2.2.2 f hfs
    obtain ⟨C,hC⟩ := hcal.2.2.1
    have hmem : MemLp f 2 P := MemLp.of_bound hcal.2.1.aestronglyMeasurable C
      (Eventually.of_forall fun X=>by simpa only [Real.norm_eq_abs] using hC X)
    have hv := hge.2.2.2.2.2.2 N hN l β q hβ hβB f hmem
    rw [hmean] at hv
    have hp := hphys N hN2 l u β ε c q hβ hβB hε hc hRe.2.2.2.2.1 f hfs
    have hh := hv.trans (mul_le_mul_of_nonneg_left hp (show 0≤2*Real.exp (B*u*c) by positivity))
    rw [canonical_shift (RieszKernel d s a ε) q.density β c] at hh
    simpa only [Clarge,mul_assoc] using hh
  have hfinite : ∀N:ℕ,∃r:ℝ,0<r ∧ ∀hN:2≤N,∀β:ℝ,0≤β→β≤B→∀q:BoundedBackground d l u,
      ∀ε:ℝ,0<ε→∀f:Configuration d N→ℝ,f∈SmoothCore d N→
        ProbabilityTheory.variance f (CanonicalLaw (N:=N) (RieszKernel d s a ε) q.density β) ≤
          r⁻¹*PhysicalEnergy (CanonicalLaw (N:=N) (RieszKernel d s a ε) q.density β) f := by
    intro N
    by_cases hN:2≤N
    · obtain ⟨r,hr,hbound⟩ := FiniteParticlePoincare d N hd hN s a B l u hs hsd ha hB hl hl1 hu
      exact ⟨r,hr,fun _ β hβ hβB q ε hε f hfs=>hbound β ε hβ hβB hε q f hfs⟩
    · exact ⟨1,by norm_num,fun h=>False.elim (hN h)⟩
  choose rs hrs hsmall using hfinite
  let C := Clarge+(∑n:Fin N₀,(rs n)⁻¹)+1
  have hsum : 0≤∑n:Fin N₀,(rs n)⁻¹ := Finset.sum_nonneg fun n _=>(inv_pos.mpr (hrs n)).le
  have hC : 0<C := by dsimp [C]; linarith
  have hClargele : Clarge≤C := by dsimp [C]; linarith
  refine ⟨C⁻¹,inv_pos.mpr hC,?_⟩
  intro N hN β hβ hβB q ε hε f hfs
  simp only [inv_inv]
  have hE : 0≤PhysicalEnergy (CanonicalLaw (N:=N) (RieszKernel d s a ε) q.density β) f := integral_nonneg fun X=>sq_nonneg _
  by_cases hNl:N₀≤N
  · exact (hlarge N hNl β hβ hβB q ε hε f hfs).trans (mul_le_mul_of_nonneg_right hClargele hE)
  · have hNlt:N<N₀ := Nat.lt_of_not_ge hNl
    have hle : (rs N)⁻¹≤C := by
      have hh : (rs N)⁻¹≤∑n:Fin N₀,(rs n)⁻¹ := by
        exact Finset.single_le_sum (f:=fun n:Fin N₀=>(rs n)⁻¹) (a:=⟨N,hNlt⟩) (fun n _=>(inv_pos.mpr (hrs n)).le) (Finset.mem_univ _)
      dsimp [C]
      linarith
    exact (hsmall N hN β hβ hβB q ε hε f hfs).trans (mul_le_mul_of_nonneg_right hle hE)

