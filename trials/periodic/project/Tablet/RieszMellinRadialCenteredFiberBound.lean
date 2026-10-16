module

public import Tablet.RieszMellinRadialSquaredTailBound
public import Tablet.TorusCosineSeriesParseval
public import Tablet.BoundedCenteredCanonicalKernel
public import Mathlib.Tactic

@[expose] public section
open MeasureTheory Set Filter UnitAddTorus
open scoped Topology BigOperators ComplexConjugate
-- [TABLET NODE: RieszMellinRadialCenteredFiberBound]
theorem RieszMellinRadialCenteredFiberBound (d:ℕ) (s a:ℝ) (hL:s<(d:ℝ)/2) (ha:0<a) :
    ∃C:ℝ,0<C ∧ ∀δ ε κ:ℝ,0<δ → 0≤ε → 1≤κ →
    ∀K:Finset (Fin d→ℤ),(∀k,k∈K↔(∑j,(k j:ℝ)^2)≤κ^2) →
    ∀r:UnitAddTorus (Fin d)→ℝ,Measurable r → ∀M:ℝ,1≤M →
      (∀ᵐx∂(volume:Measure (UnitAddTorus (Fin d))),0≤r x ∧ r x≤M) →
      (∫x,r x∂volume)=1 →
    let v:=fun x:UnitAddTorus (Fin d)=>RieszMellinLong d s a δ ε x-
      ∑k∈K,RieszMellinCoefficient d s a δ ε k*(mFourier k x).re
    let μ:Measure (UnitAddTorus (Fin d)):=volume.withDensity (fun x=>ENNReal.ofReal (r x))
    Integrable (fun x=>v x^2) volume ∧ (∫x,v x^2∂volume)≤C*κ^(2*s-(d:ℝ)) ∧
      (∀x,∫y,(CenteredKernel v r x y)^2∂μ≤C*M*κ^(2*s-(d:ℝ))) ∧
      (∀y,∫x,(CenteredKernel v r x y)^2∂μ≤C*M*κ^(2*s-(d:ℝ))) := by
-- BODY
  have character_inverse {d:ℕ} (k:Fin d→ℤ) (x:UnitAddTorus (Fin d)) :
      mFourier k (-x)=conj (mFourier k x) := by
    simp only [mFourier,ContinuousMap.coe_mk,Pi.neg_apply,fourier_apply,smul_neg,
      fourier_neg',map_prod]

  have representation (d:ℕ) (s a δ ε:ℝ) (hsd:s<(d:ℝ)) (ha:0<a)
      (hδ:0<δ) (hε:0≤ε) (K:Finset (Fin d→ℤ)) (x:UnitAddTorus (Fin d)) :
      RieszMellinLong d s a δ ε x-∑k∈K,RieszMellinCoefficient d s a δ ε k*(mFourier k x).re =
      ∑'k:Fin d→ℤ,(if k∈K then 0 else RieszMellinCoefficient d s a δ ε k)*(mFourier k x).re := by
    classical
    let c:=RieszMellinCoefficient d s a δ ε
    have hc:=RieszMellinCoefficientBounds d s a hsd ha δ ε hδ hε
    have hf:=RieszMellinFourier d s a hsd ha δ ε hδ hε
    have hchar(k:Fin d→ℤ):‖mFourier k x‖=1 := by
      simp only [mFourier,ContinuousMap.coe_mk,fourier_apply,norm_prod,Circle.norm_coe,Finset.prod_const_one]
    have hsum:Summable (fun k:Fin d→ℤ=>c k*(mFourier k x).re) := by
      apply summable_norm_iff.mp
      apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _) _ hc.1
      intro k
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hc.2.2 k).1]
      exact mul_le_of_le_one_right (hc.2.2 k).1 ((Complex.abs_re_le_norm _).trans_eq (hchar k))
    have he:=hsum.sum_add_tsum_compl (s:=K)
    rw [hf.2.1,←he]
    change (∑k∈K,c k*(mFourier k x).re)+(∑'k:{k//k∉K},c k*(mFourier k x).re)-(∑k∈K,c k*(mFourier k x).re)=_
    rw [add_sub_cancel_left]
    have hs:=tsum_subtype {k:Fin d→ℤ|k∉K} (fun k=>c k*(mFourier k x).re)
    simp only [Set.indicator_apply,Set.mem_setOf_eq] at hs
    have hs':(∑'k:{k//k∉K},c k*(mFourier k x).re)=
        ∑'k:Fin d→ℤ,if k∉K then c k*(mFourier k x).re else 0 := by
      convert! hs using 1
    rw [hs']
    apply tsum_congr
    intro k
    split_ifs <;>simp_all [c]

  classical
  obtain ⟨C,hC,hbound⟩:=RieszMellinRadialSquaredTailBound d s a hL ha
  refine ⟨16*C,by positivity,?_⟩
  intro δ ε κ hδ hε hκ K hK r hr M hM hrb hmass
  let c:=RieszMellinCoefficient d s a δ ε
  let b:=fun k:Fin d→ℤ=>if k∈K then 0 else c k
  let v:=fun x:UnitAddTorus (Fin d)=>RieszMellinLong d s a δ ε x-
    ∑k∈K,c k*(mFourier k x).re
  have hsd:s<(d:ℝ) := by linarith [(Nat.cast_nonneg d : (0:ℝ)≤d)]
  have hc:=RieszMellinCoefficientBounds d s a hsd ha δ ε hδ hε
  have hf:=RieszMellinFourier d s a hsd ha δ ε hδ hε
  have hb:∀k,0≤b k := by intro k;dsimp [b];split_ifs;exact le_rfl;exact (hc.2.2 k).1
  have hbs:Summable b := by
    convert! hc.1.indicator (↑K:Set (Fin d→ℤ))ᶜ using 1
    funext k
    simp [b,c,Set.indicator,ite_not]
  have hbe:∀k,b (-k)=b k := by
    intro k
    dsimp [b]
    have hks:k∈K↔-k∈K := by
      rw [hK k,hK (-k)]
      simp only [Pi.neg_apply,Int.cast_neg,neg_sq]
    have he:c (-k)=c k := hc.2.1 k
    simp only [←hks,he]
  have hrep:∀x,v x=∑'k:Fin d→ℤ,b k*(mFourier k x).re :=
    representation d s a δ ε hsd ha hδ hε K
  have hv:Continuous v := hf.2.2.2.sub
    (continuous_finsetSum K (fun k _=>continuous_const.mul (Complex.continuous_re.comp (mFourier k).continuous)))
  have hve:∀x,v (-x)=v x := by
    intro x
    rw [hrep,hrep]
    apply tsum_congr
    intro k
    rw [character_inverse]
    simp
  have hP:=TorusCosineSeriesParseval d b hb hbs hbe v hv hrep
  have hsum:(∑'k:Fin d→ℤ,b k^2)=∑'k:Fin d→ℤ,
      if κ^2<∑j,(k j:ℝ)^2 then c k^2 else 0 := by
    apply tsum_congr
    intro k
    have hk:=hK k
    dsimp [b]
    by_cases h:κ^2<∑j,(k j:ℝ)^2
    · have hn:k∉K := by rw [hk];exact not_le.mpr h
      simp [h,hn]
    · have hn:k∈K := by rw [hk];exact le_of_not_gt h
      simp [h,hn]
  have hH:(∫x:UnitAddTorus (Fin d),v x^2)≤C*κ^(2*s-(d:ℝ)) := by
    rw [hP.2,hsum]
    exact (hbound δ ε κ hδ hε hκ).2
  obtain ⟨A,hA⟩:=(isCompact_univ:IsCompact (Set.univ:Set (UnitAddTorus (Fin d)))).exists_bound_of_continuousOn hv.continuousOn
  have hAb:∀x,|v x|≤|A|+1 := by
    intro x
    have h:=hA x (mem_univ x)
    rw [Real.norm_eq_abs] at h
    linarith [le_abs_self A]
  have hF:=BoundedCenteredCanonicalKernel d v r hv.measurable hve hr M (|A|+1)
    (C*κ^(2*s-(d:ℝ))) hM (by positivity) hrb hmass hAb hP.1 hH
  dsimp only
  refine ⟨hP.1,hH.trans ?_,?_,?_⟩
  · have hp:0≤κ^(2*s-(d:ℝ)) := Real.rpow_nonneg (by linarith) _
    nlinarith
  · intro x
    have h:=(hF.2.2.2.2.1 x)
    convert! h using 1 <;> ring
  · intro y
    have h:=(hF.2.2.2.2.2 y)
    convert! h using 1 <;> ring

