import Tablet.BoundedCenteredCanonicalKernel
import Tablet.CenteredDeletionEnergySum
open MeasureTheory
open scoped BigOperators
-- [TABLET NODE: ScaledBoundedCenteredCanonicalKernel]
theorem ScaledBoundedCenteredCanonicalKernel (d N : ℕ)
    (g r : UnitAddTorus (Fin d)→ℝ) (hg : Measurable g) (he : ∀x,g (-x)=g x)
    (hr : Measurable r) (M A J t : ℝ) (hM : 1≤M) (hA : 0<A) (ht : 0<t)
    (hrb : ∀ᵐx∂volume,0≤r x ∧ r x≤M) (hrmass : ∫x,r x=1)
    (hgb : ∀x,|g x|≤A) (hg2 : Integrable (fun x=>g x^2) volume) (hJ : (∫x,g x^2)≤J) :
    let μ := volume.withDensity (fun x => ENNReal.ofReal (r x))
    let q := fun x y => 2*t*CenteredKernel g r x y
    let R := fun X : Configuration d N => ∑i,∑j,if i=j then (0:ℝ) else q (X i) (X j)
    Measurable (fun p : UnitAddTorus (Fin d)×UnitAddTorus (Fin d) => q p.1 p.2) ∧
    (∀x y,|q x y|≤8*t*A) ∧ (∀x,∫y,q x y∂μ=0) ∧ (∀y,∫x,q x y∂μ=0) ∧
    (∀x,∫y,(q x y)^2∂μ≤64*t^2*M*J) ∧ (∀y,∫x,(q x y)^2∂μ≤64*t^2*M*J) ∧
    (∀X,R X/(2*(N:ℝ))=2*t*CenteredPairEnergy g r X) := by
-- BODY
  let μ := volume.withDensity (fun x => ENNReal.ofReal (r x))
  let q := fun x y => 2*t*CenteredKernel g r x y
  let R := fun X : Configuration d N => ∑i,∑j,if i=j then (0:ℝ) else q (X i) (X j)
  have hcan := BoundedCenteredCanonicalKernel d g r hg he hr M A J hM hA hrb hrmass hgb hg2 hJ
  rcases hcan with ⟨hqm,hqb,hqr,hqc,hqfr,hqfc⟩
  have hUStat (X : Configuration d N) : CenteredPairEnergy g r X = ((∑i,∑j,if i=j then (0:ℝ) else CenteredKernel g r (X i) (X j))/(N:ℝ))/2 := by
    have h:=(CenteredDeletionEnergySum g r he X 1).1
    have hi (i j:Fin N):
        (if j≠i then CenteredKernel g r (X i) (X j) else 0)=
        (if i=j then (0:ℝ) else CenteredKernel g r (X i) (X j)) := by
      by_cases he:i=j
      · subst j; simp
      · simp [he,Ne.symm he]
    simp_rw [hi,←Finset.mul_sum] at h
    simp only [one_div] at h
    simp only [div_eq_mul_inv]
    norm_num at h ⊢
    nlinarith only [h]
  have hid (X : Configuration d N) : R X/(2*(N:ℝ))=2*t*CenteredPairEnergy g r X := by
    have hterm (i j : Fin N) : (if i=j then (0:ℝ) else q (X i) (X j))=
      2*t*(if i=j then 0 else CenteredKernel g r (X i) (X j)) := by
      dsimp [q]; split_ifs <;> ring
    dsimp [R]
    simp_rw [hterm,← Finset.mul_sum]
    rw [hUStat X]
    ring
  refine ⟨measurable_const.mul hqm,?_,?_,?_,?_,?_,hid⟩
  · intro x y
    change |2*t*CenteredKernel g r x y|≤_
    rw [abs_mul,abs_of_pos (show 0<2*t by positivity)]
    have hh := mul_le_mul_of_nonneg_left (hqb x y) (show 0≤2*t by positivity)
    nlinarith only [hh]
  · intro x; change (∫y,2*t*CenteredKernel g r x y∂μ)=0
    rw [integral_const_mul,hqr,mul_zero]
  · intro y; change (∫x,2*t*CenteredKernel g r x y∂μ)=0
    rw [integral_const_mul,hqc,mul_zero]
  · intro x
    change (∫y,(2*t*CenteredKernel g r x y)^2∂μ)≤_
    simp_rw [mul_pow]
    rw [integral_const_mul]
    have hh := mul_le_mul_of_nonneg_left (hqfr x) (sq_nonneg (2*t))
    nlinarith only [hh]
  · intro y
    change (∫x,(2*t*CenteredKernel g r x y)^2∂μ)≤_
    simp_rw [mul_pow]
    rw [integral_const_mul]
    have hh := mul_le_mul_of_nonneg_left (hqfc y) (sq_nonneg (2*t))
    nlinarith only [hh]
