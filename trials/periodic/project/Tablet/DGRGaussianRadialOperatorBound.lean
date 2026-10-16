import Tablet.DGRGaussianTruncationIdentification
import Tablet.RieszCenteredFourierTailOperator
import Tablet.RieszRadialMultiplierBound
open MeasureTheory Filter
open scoped BigOperators
-- [TABLET NODE: DGRGaussianRadialOperatorBound]
theorem DGRGaussianRadialOperatorBound (d : ℕ) (hd : 2≤d) (s a M t : ℝ)
    (hs : 0≤s) (hL : s<(d:ℝ)/2) (ha : 0<a) (hM : 1≤M) (ht : 0<t) :
    ∃CD : ℝ,0<CD ∧ ∀κ : ℝ,1≤κ →
      ∀K : Finset (Fin d→ℤ),(∀k,k∈K↔(∑j,(k j:ℝ)^2)≤κ^2) →
      ∀η : ℝ,0<η → η≤1 → ∀r : UnitAddTorus (Fin d)→ℝ,Measurable r →
        (∀ᵐx∂volume,0≤r x ∧ r x≤M) → (∫x,r x=1) →
      let V := fun x => DGRGaussianPhysicalLong d s a η x-
        ∑k∈K,RieszMellinCoefficient d s a (η^2) 0 k*(UnitAddTorus.mFourier k x).re
      let μ := volume.withDensity (fun x => ENNReal.ofReal (r x))
      let q := fun x y => 2*t*CenteredKernel V r x y
      (∀f g : UnitAddTorus (Fin d)→ℝ,Measurable f → Measurable g →
        ∀hf : MemLp f 2 μ,∀hg : MemLp g 2 μ,
        |∫x,∫y,q x y*f x*g y∂μ∂μ|≤CD*κ^(s-(d:ℝ))*‖hf.toLp f‖*‖hg.toLp g‖) := by
-- BODY
  have hdp : 0<(d:ℝ) := by exact_mod_cast (show 0<d by omega)
  have hsd : s<(d:ℝ) := by linarith
  obtain ⟨CD,hCD,hmult⟩ := RieszRadialMultiplierBound d s a hsd ha
  refine ⟨2*t*M*CD,by positivity,?_⟩
  intro κ hκ K hK η hη hη1 r hr hrb hrmass
  let μ := volume.withDensity (fun x => ENNReal.ofReal (r x))
  let V := fun x => DGRGaussianPhysicalLong d s a η x-
    ∑k∈K,RieszMellinCoefficient d s a (η^2) 0 k*(UnitAddTorus.mFourier k x).re
  let q := fun x y => 2*t*CenteredKernel V r x y
  have hδ : 0<η^2 := sq_pos_of_pos hη
  have hlong := (DGRGaussianTruncationIdentification d s a η hη).2.1
  have hKs : ∀k,k∈K↔-k∈K := by
    intro k
    rw [hK k,hK (-k)]
    simp only [Pi.neg_apply,Int.cast_neg,neg_sq]
  have hκp : 0<κ := zero_lt_one.trans_le hκ
  have hσ : 0≤CD*κ^(s-(d:ℝ)) := by positivity
  have hout (k) (hk : k∉K) : (if k=0 then 0 else
      a*(4*Real.pi^2*∑j,(k j:ℝ)^2)^(-((d:ℝ)-s)/2))≤CD*κ^(s-(d:ℝ)) :=
    hmult κ hκ k (lt_of_not_ge fun hh => hk ((hK k).mpr hh))
  have hop := RieszCenteredFourierTailOperator d s a hsd ha (η^2) 0 hδ le_rfl K hKs
    (CD*κ^(s-(d:ℝ))) hσ hout r hr M (zero_le_one.trans hM) hrb hrmass
  dsimp only at hop
  rw [←hlong] at hop
  dsimp only
  intro f g hfm hgm hf hg
  change |∫x,∫y,(2*t*CenteredKernel V r x y)*f x*g y∂μ∂μ|≤_
  simp_rw [show ∀x y,(2*t*CenteredKernel V r x y)*f x*g y=
    (2*t)*(CenteredKernel V r x y*f x*g y) by intro x y; ring]
  simp_rw [integral_const_mul]
  rw [abs_mul,abs_of_pos (show 0<2*t by positivity)]
  have hh := mul_le_mul_of_nonneg_left (hop f g hfm hgm hf hg) (show 0≤2*t by positivity)
  nlinarith only [hh]
