import Tablet.DGRGaussianPowerMasterGrowth
import Tablet.DGRGaussianLogMasterGrowth
open scoped BigOperators
-- [TABLET NODE: DGRGaussianMasterGrowth]
theorem DGRGaussianMasterGrowth (d : ℕ) (hd : 2≤d) (s a M t : ℝ)
    (hs : 0≤s) (hL : s<(d:ℝ)/2) (ha : 0<a) (hM : 1≤M) (ht : 0<t) :
    ∃C : ℝ,0<C ∧ ∀N : ℕ,1≤N → ∀u : ℝ,1≤u → ∀K : Finset (Fin d→ℤ),
      let b := (a/Real.Gamma (((d:ℝ)-s)/2))/(((d:ℝ)-s)/2)
      let η := min 1 ((u/(8*t*(N:ℝ)*M*b))^(1/((d:ℝ)-s)))
      let V := fun x => DGRGaussianPhysicalLong d s a η x-
        ∑k∈K,RieszMellinCoefficient d s a (η^2) 0 k*(UnitAddTorus.mFourier k x).re
      min u (4*t*V 0)*(1+8*t*(V 0+1))≤
        C*(if s=0 then (Real.log (Real.exp 1+(N:ℝ)))^2 else (N:ℝ)^(2*s/(d:ℝ))) := by
-- BODY
  by_cases hz : s=0
  · subst s
    simpa using DGRGaussianLogMasterGrowth d hd a M t ha hM ht
  · simpa only [if_neg hz] using DGRGaussianPowerMasterGrowth d hd s a M t
      (lt_of_le_of_ne hs (Ne.symm hz)) hL ha hM ht
