import Tablet.NativeGibbsJumpVariance
import Tablet.AtomicOneSitePI
import Tablet.ParticleInsertionCalculus
import Tablet.CompactGradientCalculus
import Tablet.PhysicalEnergy
open MeasureTheory Filter Set
open scoped ENNReal BigOperators ContDiff
set_option autoImplicit false
set_option maxHeartbeats 2000000

-- [TABLET NODE: GibbsJumpPhysicalComparison]
theorem GibbsJumpPhysicalComparison (d : ℕ) (hd : 3 ≤ d) (s B κ L : ℝ)
    (hs : 0 < s) (hsd : s ≤ (d:ℝ)-2) (hB : 0 ≤ B) (hκ : 0 < κ) (hL : 1 ≤ L)
    (Ca Mloc : ℝ → ℝ) :
    ∃ σ : ℝ, 0 < σ ∧
    ∀ V : OneParticle d → ℝ, PotentialBounds d κ V →
      (∀ x, V 0 ≤ V x) →
      (∀ R : ℝ, 0 < R → ∀ x, ‖x‖ ≤ R → V x-V 0 ≤ Mloc R) →
      (∀ a : ℝ, 0 < a → ∀ x, EuclideanLaplacian V x ≤
        a*‖EuclideanGradient V x‖^(2/(s+1))+Ca a) →
    ∀ b : OneParticle d → ℝ, BoundedMultiplier d L b →
    ∀ N : ℕ, 2 ≤ N → ∀ coupling ε : ℝ, 0 ≤ coupling → coupling ≤ B → 0 < ε →
      let μ := ReferenceLaw V b
      let P := GibbsLaw (N:=N) μ s coupling ε
      let U := fun (X : ParticleConfig d N) (i : Fin N) (z : OneParticle d) =>
        ∑ j ∈ Finset.univ.erase i, (coupling/(N:ℝ))*RieszKernel s ε (z-ParticlePosition X j)
      let J := fun i => (P.prod μ).withDensity
        (fun q => ENNReal.ofReal (Real.exp (-U q.1 i q.2)))
      ∀ f : ParticleConfig d N → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
        σ*((1/2:ℝ)*∑ i : Fin N,
          ∫ q, (f (ParticleInsertion q.1 i q.2)-f q.1)^2 ∂J i) ≤ PhysicalEnergy P f := by
-- BODY
  classical
  obtain ⟨σ,hσ,hone⟩ := AtomicOneSitePI d hd s B κ L hs hsd hB hκ hL Ca Mloc
  refine ⟨σ,hσ,?_⟩
  intro V hV hmin hM hgrowth b hb N hN coupling ε hc hcB hε
  dsimp only
  let μ := ReferenceLaw V b
  let P := GibbsLaw (N:=N) μ s coupling ε
  let U := fun (X : ParticleConfig d N) (i : Fin N) (z : OneParticle d) =>
    ∑ j ∈ Finset.univ.erase i, (coupling/(N:ℝ))*RieszKernel s ε (z-ParticlePosition X j)
  let r := fun i (q : ParticleConfig d N × OneParticle d) => Real.exp (-U q.1 i q.2)
  let J := fun i => (P.prod μ).withDensity (fun q => ENNReal.ofReal (r i q))
  let Z := fun X i => ∫ z, r i (X,z) ∂μ
  let ν := fun X i => ReferenceLaw (fun z => V z+U X i z) b
  obtain ⟨a,_,huniq,_,hq,_⟩ := (HessianMinimizer V κ hκ hV).2
  have hz : (0 : OneParticle d) = a := huniq 0 hmin
  subst a
  have hquad (x) : κ/2*‖x‖^2 ≤ V x-V 0 := by
    have h := hq x
    simp only [sub_zero] at h
    linarith
  have hlocal := hM 1 (by norm_num)
  haveI : IsProbabilityMeasure μ := (ConvexReferenceNormalization V b κ L hκ hV hb).2.2
  haveI : IsProbabilityMeasure P := (SoftGibbsNormalization μ s coupling ε hs hc hε).2.2
  obtain ⟨C,hC,hsite⟩ := GibbsInsertionReference d hd s B κ L (Mloc 1) hs hsd hB hκ hL
  have hdata (X : ParticleConfig d N) (i : Fin N) :=
    hsite V b hV.regularity.continuous hb hquad hlocal N hN coupling ε hc hcB hε X i
  have hUn (X : ParticleConfig d N) (i : Fin N) (z : OneParticle d) : 0 ≤ U X i z := by
    dsimp [U]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (div_nonneg hc (Nat.cast_nonneg N))
      ((RieszKernelBounds s ε hs hε.le).1 _)
  have hrm (i : Fin N) : Measurable (r i) := by
    have hm : Measurable (fun q : ParticleConfig d N × OneParticle d => U q.1 i q.2) := by
      dsimp [U]
      apply Finset.measurable_sum
      intro j hj
      apply Measurable.const_mul
      unfold RieszKernel
      simp only [ne_of_gt hε,if_false]
      unfold ParticlePosition
      fun_prop
    exact hm.neg.exp
  have hZ (X : ParticleConfig d N) (i : Fin N) : 0 < Z X i :=
    (Real.exp_pos _).trans_le (hdata X i).2.2.2.2.1
  have hrpos (i : Fin N) (q : ParticleConfig d N × OneParticle d) : 0 ≤ r i q :=
    Real.exp_nonneg _
  have htilt (X : ParticleConfig d N) (i : Fin N) :
      ν X i=μ.withDensity (fun z => ENNReal.ofReal ((Z X i)⁻¹*r i (X,z))) :=
    (hdata X i).2.2.2.2.2.2.2.1
  have hbalance (i : Fin N) := NativeGibbsReplacementBalance d N μ s coupling ε hs hc hε i
  have hinsmeas (i : Fin N) : Measurable
      (fun q : ParticleConfig d N × OneParticle d => ParticleInsertion q.1 i q.2) :=
    measurable_fst.comp (hbalance i).1.measurable
  intro f hf hfc
  have hfLp : MemLp f 2 P := hf.continuous.memLp_of_hasCompactSupport hfc
  have hvar := (NativeGibbsJumpVariance d hd s B κ L (Mloc 1) hs hsd hB hκ hL
    V b hV.regularity.continuous hb hquad hlocal N hN coupling ε hc hcB hε).2 f hfLp
  let g := fun i (X : ParticleConfig d N) => ‖ParticlePosition (EuclideanGradient f X) i‖^2
  have hg (i : Fin N) : Integrable (g i) P := by
    have hgrad := CompactGradientCalculus f hf hfc
    have hgm : Continuous (fun X => ParticlePosition (EuclideanGradient f X) i) := by
      have hp : Continuous (fun Y : ParticleConfig d N => ParticlePosition Y i) := by
        unfold ParticlePosition
        fun_prop
      exact hp.comp hgrad.1
    have hgc : HasCompactSupport (fun X => ParticlePosition (EuclideanGradient f X) i) :=
      hgrad.2.1.comp_left (g:=fun Y => ParticlePosition Y i) (by ext k; rfl)
    have hsupp : HasCompactSupport (fun X => ‖ParticlePosition (EuclideanGradient f X) i‖^2) := by
      exact hgc.comp_left (g:=fun z : OneParticle d => ‖z‖^(2:ℕ)) (by simp)
    exact (hgm.norm.pow 2).integrable_of_hasCompactSupport hsupp
  have hrow (i : Fin N) :
      Integrable (fun X => Z X i*(∫ z,g i (ParticleInsertion X i z) ∂ν X i)) P ∧
      (∫ X,Z X i*(∫ z,g i (ParticleInsertion X i z) ∂ν X i) ∂P)
        ≤ ∫ X,g i X ∂P := by
    let t := fun q : ParticleConfig d N × OneParticle d => ParticleInsertion q.1 i q.2
    have hmap := (hg i).mono_measure (hbalance i).2.2
    have hj : Integrable (fun q => g i (t q)) (J i) :=
      (integrable_map_measure hmap.1 (hinsmeas i).aemeasurable).mp hmap
    have hfin : ∀ᵐ q ∂P.prod μ, ENNReal.ofReal (r i q)<⊤ :=
      Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
    have hi := (integrable_withDensity_iff_integrable_smul' (hrm i).ennreal_ofReal hfin).mp hj
    simp only [ENNReal.toReal_ofReal (hrpos i _),smul_eq_mul] at hi
    have he (X : ParticleConfig d N) :
        Z X i*(∫ z,g i (ParticleInsertion X i z) ∂ν X i) =
          ∫ z,r i (X,z)*g i (ParticleInsertion X i z) ∂μ := by
      have hm : Measurable (fun z => ENNReal.ofReal ((Z X i)⁻¹*r i (X,z))) :=
        (((hrm i).comp (measurable_const.prodMk measurable_id)).const_mul
          ((Z X i)⁻¹)).ennreal_ofReal
      have hfin : ∀ᵐ z ∂μ, ENNReal.ofReal ((Z X i)⁻¹*r i (X,z))<⊤ :=
        Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
      rw [htilt X i,integral_withDensity_eq_integral_toReal_smul hm hfin]
      simp only [ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.mpr (hZ X i).le)
        (hrpos i _)),smul_eq_mul,mul_assoc,integral_const_mul]
      rw [← mul_assoc, mul_inv_cancel₀ (hZ X i).ne',one_mul]
    refine ⟨hi.integral_prod_left.congr (Eventually.of_forall fun X => (he X).symm),?_⟩
    calc
      _ = ∫ q,g i (t q) ∂J i := by
        simp_rw [he]
        rw [integral_withDensity_eq_integral_toReal_smul (hrm i).ennreal_ofReal hfin]
        simp only [ENNReal.toReal_ofReal (hrpos i _),smul_eq_mul]
        exact (integral_prod _ hi).symm
      _ = ∫ X,g i X ∂(J i).map t := by
        exact (integral_map (hinsmeas i).aemeasurable hmap.1).symm
      _ ≤ ∫ X,g i X ∂P := integral_mono_measure (hbalance i).2.2
        (Eventually.of_forall fun X => sq_nonneg _) (hg i)
  have hlabel (i : Fin N) :
      σ*(∫ X,Z X i*ProbabilityTheory.variance
        (fun z => f (ParticleInsertion X i z)) (ν X i) ∂P) ≤ ∫ X,g i X ∂P := by
    apply le_trans _ (hrow i).2
    rw [← integral_const_mul]
    apply integral_mono (hvar.2.1 i |>.const_mul σ) (hrow i).1
    intro X
    have hfibre := (ParticleInsertionCalculus.2 f hf hfc).1 X i
    have hm : ∑ j ∈ Finset.univ.erase i, coupling/(N:ℝ) ≤ B := by
      simpa only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm] using (hdata X i).2.1
    have hpi := hone V hV hmin hM hgrowth (Finset.univ.erase i)
      (fun _ => coupling/(N:ℝ)) (fun j => ParticlePosition X j) ε
      (fun _ _ => div_nonneg hc (Nat.cast_nonneg N)) hm hε b hb
      (fun z => f (ParticleInsertion X i z)) (hfibre.1.of_le (by simp)) 0
      (by simpa only [sub_zero] using hfibre.2.1)
    have he : (∫ z,‖EuclideanGradient (fun w => f (ParticleInsertion X i w)) z‖^2 ∂ν X i) =
        ∫ z,g i (ParticleInsertion X i z) ∂ν X i := by
      simp_rw [hfibre.2.2]
      rfl
    change σ*ProbabilityTheory.variance _ (ν X i) ≤ _ at hpi
    rw [he] at hpi
    have h := mul_le_mul_of_nonneg_left hpi (hZ X i).le
    nlinarith only [h]
  change σ*((1/2:ℝ)*∑ i : Fin N, ∫ q,
    (f (ParticleInsertion q.1 i q.2)-f q.1)^2 ∂J i) ≤ _
  rw [hvar.2.2,integral_finsetSum _ (fun i _ => hvar.2.1 i),Finset.mul_sum]
  calc
    _ ≤ ∑ i : Fin N, ∫ X,g i X ∂P := Finset.sum_le_sum fun i _ => hlabel i
    _ = ∫ X,∑ i : Fin N,g i X ∂P :=
      (integral_finsetSum _ (fun i _ => hg i)).symm
    _ = PhysicalEnergy P f := by
      unfold PhysicalEnergy
      apply integral_congr_ae
      exact Eventually.of_forall fun X =>
        ((ParticleGradientEnergyIdentity P f).1 (EuclideanGradient f X)).symm
