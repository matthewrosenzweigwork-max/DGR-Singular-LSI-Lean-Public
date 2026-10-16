module

public import Tablet.DGRGaussianDiagonalProfile
public import Tablet.DGRPhysicalLogEnvelope
public import Tablet.DGRCappedLogGrowth

@[expose] public section
open scoped BigOperators
-- [TABLET NODE: DGRGaussianLogMasterGrowth]
theorem DGRGaussianLogMasterGrowth (d : ℕ) (hd : 2≤d) (a M t : ℝ)
    (ha : 0<a) (hM : 1≤M) (ht : 0<t) :
    ∃C : ℝ,0<C ∧ ∀N : ℕ,1≤N → ∀u : ℝ,1≤u → ∀K : Finset (Fin d→ℤ),
      let b := (a/Real.Gamma ((d:ℝ)/2))/((d:ℝ)/2)
      let η := min 1 ((u/(8*t*(N:ℝ)*M*b))^(1/(d:ℝ)))
      let V := fun x => DGRGaussianPhysicalLong d 0 a η x-
        ∑k∈K,RieszMellinCoefficient d 0 a (η^2) 0 k*(UnitAddTorus.mFourier k x).re
      min u (4*t*V 0)*(1+8*t*(V 0+1))≤C*(Real.log (Real.exp 1+(N:ℝ)))^2 := by
-- BODY
  have hdp : 0<(d:ℝ) := by exact_mod_cast (show 0<d by omega)
  let b := (a/Real.Gamma ((d:ℝ)/2))/((d:ℝ)/2)
  let c := 8*t*M*b
  have hb : 0<b := div_pos (div_pos ha (Real.Gamma_pos_of_pos (by linarith))) (by linarith)
  have hc : 0<c := by dsimp [c]; positivity
  obtain ⟨A,hA,hprofile⟩ := DGRGaussianDiagonalProfile d hd 0 a le_rfl hdp ha
  let B := 1+(2/(d:ℝ))*(|Real.log c|+1)
  let C := 1+8*t*(A*B+1)
  have hB : 0<B := by dsimp [B]; positivity
  have hC : 1≤C := by
    dsimp [C]
    linarith [show 0≤8*t*(A*B+1) by positivity]
  refine ⟨8*C^2,by positivity,?_⟩
  intro N hN u hu K
  have hNr : 1≤(N:ℝ) := by exact_mod_cast hN
  have hNp : 0<(N:ℝ) := zero_lt_one.trans_le hNr
  have hup : 0<u := zero_lt_one.trans_le hu
  have hlogN : 0≤Real.log (N:ℝ) := Real.log_nonneg hNr
  let η := min 1 ((u/(c*(N:ℝ)))^(1/(d:ℝ)))
  let V := fun x => DGRGaussianPhysicalLong d 0 a η x-
    ∑k∈K,RieszMellinCoefficient d 0 a (η^2) 0 k*(UnitAddTorus.mFourier k x).re
  have hη : 0<η := lt_min (by norm_num) (Real.rpow_pos_of_pos (by positivity) _)
  have hη1 : η≤1 := min_le_left _ _
  obtain ⟨hV0,hVb⟩ := hprofile η hη hη1 K
  change 0≤V 0 at hV0
  change V 0≤A*(if (0:ℝ)=0 then 1+|Real.log (η^2)| else η^(-(0:ℝ))) at hVb
  rw [if_pos rfl] at hVb
  have hlog := DGRPhysicalLogEnvelope (d:ℝ) c (N:ℝ) u hdp hc hNr hu
  change |Real.log (η^2)|≤(2/(d:ℝ))*(|Real.log c|+Real.log (N:ℝ)) at hlog
  have hprofileB : 1+|Real.log (η^2)|≤B*(1+Real.log (N:ℝ)) := by
    dsimp [B]
    have hh := mul_nonneg (show 0≤2/(d:ℝ) by positivity)
      (mul_nonneg (abs_nonneg (Real.log c)) hlogN)
    nlinarith only [hlog,hlogN,hh,show 0≤2/(d:ℝ) by positivity]
  have hVupper := hVb.trans (mul_le_mul_of_nonneg_left hprofileB hA.le)
  have hAb : 8*t*(V 0+1)≤C*(1+Real.log (N:ℝ)) := by
    have h1 : 1≤1+Real.log (N:ℝ) := by linarith only [hlogN]
    have hh := mul_le_mul_of_nonneg_left hVupper (show 0≤8*t by positivity)
    have hC' : 8*t*(A*B+1)≤C := by dsimp [C]; linarith
    have hh' := mul_le_mul_of_nonneg_right hC' (show 0≤1+Real.log (N:ℝ) by linarith)
    nlinarith only [hh,hh',h1,ht]
  have hmb : 4*t*V 0≤C*(1+Real.log (N:ℝ)) := by
    have hh : 4*t*V 0≤8*t*(V 0+1) := by nlinarith only [ht,hV0]
    exact hh.trans hAb
  have hg := DGRCappedLogGrowth (N:ℝ) C u (4*t*V 0) (8*t*(V 0+1))
    hNr hC hu (by positivity) (by positivity) hmb hAb
  dsimp only
  have hden : 8*t*(N:ℝ)*M*((a/Real.Gamma ((d:ℝ)/2))/((d:ℝ)/2))=c*(N:ℝ) := by
    dsimp [c,b]; ring
  rw [hden]
  exact hg
