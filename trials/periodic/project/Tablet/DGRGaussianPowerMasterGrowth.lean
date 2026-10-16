import Tablet.DGRGaussianDiagonalProfile
import Tablet.DGRPhysicalPowerEnvelope
import Tablet.DGRCappedPowerGrowth
open scoped BigOperators
-- [TABLET NODE: DGRGaussianPowerMasterGrowth]
theorem DGRGaussianPowerMasterGrowth (d : ℕ) (hd : 2≤d) (s a M t : ℝ)
    (hs : 0<s) (hL : s<(d:ℝ)/2) (ha : 0<a) (hM : 1≤M) (ht : 0<t) :
    ∃C : ℝ,0<C ∧ ∀N : ℕ,1≤N → ∀u : ℝ,1≤u → ∀K : Finset (Fin d→ℤ),
      let α := ((d:ℝ)-s)/2
      let b := (a/Real.Gamma α)/α
      let η := min 1 ((u/(8*t*(N:ℝ)*M*b))^(1/((d:ℝ)-s)))
      let V := fun x => DGRGaussianPhysicalLong d s a η x-
        ∑k∈K,RieszMellinCoefficient d s a (η^2) 0 k*(UnitAddTorus.mFourier k x).re
      min u (4*t*V 0)*(1+8*t*(V 0+1))≤C*(N:ℝ)^(2*s/(d:ℝ)) := by
-- BODY
  have hdp : 0<(d:ℝ) := by exact_mod_cast (show 0<d by omega)
  have hsd : s<(d:ℝ) := by linarith
  let α := ((d:ℝ)-s)/2
  let b := (a/Real.Gamma α)/α
  let θ := s/((d:ℝ)-s)
  let c := 8*t*M*b
  have hds : 0<(d:ℝ)-s := by linarith
  have hb : 0<b := div_pos (div_pos ha (Real.Gamma_pos_of_pos (by dsimp [α]; linarith)))
    (by dsimp [α]; linarith)
  have hc : 0<c := by dsimp [c]; positivity
  have hθ : 0<θ := div_pos hs hds
  have hθ1 : θ<1 := (div_lt_one hds).mpr (by linarith)
  obtain ⟨A,hA,hprofile⟩ := DGRGaussianDiagonalProfile d hd s a hs.le hsd ha
  let C := 1+8*t*(A*(1+c^θ)+1)
  have hC : 1≤C := by
    dsimp [C]
    linarith [show 0≤8*t*(A*(1+c^θ)+1) by positivity]
  have hCp : 0<C := zero_lt_one.trans_le hC
  refine ⟨6*C^2,by positivity,?_⟩
  intro N hN u hu K
  have hNr : 1≤(N:ℝ) := by exact_mod_cast hN
  have hNp : 0<(N:ℝ) := zero_lt_one.trans_le hNr
  have hup : 0<u := zero_lt_one.trans_le hu
  let η := min 1 ((u/(c*(N:ℝ)))^(1/((d:ℝ)-s)))
  let V := fun x => DGRGaussianPhysicalLong d s a η x-
    ∑k∈K,RieszMellinCoefficient d s a (η^2) 0 k*(UnitAddTorus.mFourier k x).re
  have hη : 0<η := lt_min (by norm_num) (Real.rpow_pos_of_pos (by positivity) _)
  have hη1 : η≤1 := min_le_left _ _
  obtain ⟨hV0,hVb⟩ := hprofile η hη hη1 K
  change 0≤V 0 at hV0
  change V 0≤A*(if s=0 then 1+|Real.log (η^2)| else η^(-s)) at hVb
  rw [if_neg hs.ne'] at hVb
  have hpower := DGRPhysicalPowerEnvelope ((d:ℝ)-s) s c (N:ℝ) u hds hs hc hNr hu
  change η^(-s)≤1+c^θ*((N:ℝ)/u)^θ at hpower
  have hVupper := hVb.trans (mul_le_mul_of_nonneg_left hpower hA.le)
  let z := ((N:ℝ)/u)^θ
  have hz : 0≤z := by dsimp [z]; positivity
  have hcθ : 0≤c^θ := Real.rpow_nonneg hc.le _
  have hcoef0 : 8*t*(A+1)≤C := by dsimp [C]; nlinarith only [ht,hA,hcθ,mul_nonneg hA.le hcθ]
  have hcoef1 : 8*t*A*c^θ≤C := by dsimp [C]; nlinarith only [ht,hA]
  have hcoefz := mul_le_mul_of_nonneg_right hcoef1 hz
  have hAb : 8*t*(V 0+1)≤C*(1+z) := by
    change V 0≤A*(1+c^θ*z) at hVupper
    have hh := mul_le_mul_of_nonneg_left hVupper (show 0≤8*t by positivity)
    nlinarith only [hh,hcoef0,hcoefz]
  have hmb : 4*t*V 0≤C*(1+z) := by
    have hh : 4*t*V 0≤8*t*(V 0+1) := by nlinarith only [ht,hV0]
    exact hh.trans hAb
  have hg := DGRCappedPowerGrowth (N:ℝ) θ C u (4*t*V 0) (8*t*(V 0+1))
    hNr hθ hθ1 hC hu (by positivity) (by positivity) hmb hAb
  have he : 2*θ/(1+θ)=2*s/(d:ℝ) := by dsimp [θ]; field_simp; ring
  rw [he] at hg
  dsimp only
  have hden : 8*t*(N:ℝ)*M*((a/Real.Gamma (((d:ℝ)-s)/2))/(((d:ℝ)-s)/2))=c*(N:ℝ) := by
    dsimp [c,b,α]; ring
  rw [hden]
  exact hg
