import Tablet.DGRGaussianCenteredTruncation
import Tablet.CenteredProductMean
import Tablet.Preamble
open MeasureTheory
-- [TABLET NODE: DGRGaussianFiniteMasterCap]
theorem DGRGaussianFiniteMasterCap (d : ℕ) (hd : 2≤d) (s a M t : ℝ)
    (hs : 0≤s) (hsd : s<(d:ℝ)) (ha : 0<a) (hM : 1≤M) (ht : 0≤t) (N₀ : ℕ) :
    ∃C : ℝ,1≤C ∧ ∀N : ℕ,2≤N → N≤N₀ →
      ∀r : UnitAddTorus (Fin d)→ℝ,Measurable r →
        (∀ᵐx∂volume,0≤r x ∧ r x≤M) → (∫x,r x=1) →
      let μ := volume.withDensity (fun x => ENNReal.ofReal (r x))
      let ν := Measure.pi (fun _:Fin N=>μ)
      let Xi := fun X : Configuration d N => -t*CenteredPairEnergy (RieszKernel d s a 0) r X
      Integrable (fun X => Real.exp (Xi X)) ν ∧ (∫X,Real.exp (Xi X)∂ν)≤C := by
-- BODY
  let b := (a/Real.Gamma (((d:ℝ)-s)/2))/(((d:ℝ)-s)/2)
  let B := (N₀:ℝ)*M*b+2*DGRGaussianPhysicalLong d s a 1 0
  let C := max 1 (Real.exp (t*B))
  refine ⟨C,le_max_left _ _,?_⟩
  intro N hN hN0 r hr hrb hrmass
  dsimp only
  let μ := volume.withDensity (fun x => ENNReal.ofReal (r x))
  let ν := Measure.pi (fun _:Fin N=>μ)
  let Xi := fun X : Configuration d N => -t*CenteredPairEnergy (RieszKernel d s a 0) r X
  have hri : Integrable r volume := Integrable.of_bound hr.aestronglyMeasurable M (by
    filter_upwards [hrb] with x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2)
  haveI : IsProbabilityMeasure μ := by
    apply isProbabilityMeasure_iff.mpr
    rw [withDensity_apply _ MeasurableSet.univ]
    simp only [Measure.restrict_univ]
    rw [←ofReal_integral_eq_lintegral_ofReal hri (hrb.mono fun _ hx => hx.1), hrmass]
    simp
  haveI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  obtain ⟨c,hc,hg⟩ := RieszL1Foundation d hd s a hs hsd ha
  obtain ⟨hgm,hgi,_,_,hgl,_,_⟩ := hg 0 le_rfl
  have hEm := (CenteredProductMean d N (RieszKernel d s a 0) r hgm hgi hr M c hM hc hrb hrmass hgl).1
  have hXm : Measurable (fun X => Real.exp (Xi X)) := Real.measurable_exp.comp (measurable_const.mul hEm)
  have hw := DGRGaussianCenteredTruncation d hd s a 1 M hs hsd ha (by norm_num) le_rfl hM r hr hrb hrmass
  dsimp only at hw
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,he⟩ := hw
  obtain ⟨hnear,hlong,hdecomp⟩ := he N (by omega)
  have hb : 0<b := div_pos (div_pos ha (Real.Gamma_pos_of_pos (by linarith))) (by linarith)
  have hMb : 0≤M*b := mul_nonneg (zero_le_one.trans hM) hb.le
  have hNN : (N:ℝ)-1≤(N₀:ℝ) := by exact_mod_cast (show (N:ℤ)-1≤(N₀:ℤ) by omega)
  have hcap : ∀ᵐX∂ν,Xi X≤t*B := by
    filter_upwards [hdecomp] with X hx
    have hn := hnear X
    have hl := hlong X
    simp only [Real.one_rpow,mul_one] at hn
    change -((N:ℝ)-1)*M*b≤CenteredPairEnergy (DGRGaussianPhysicalNear d s a 1) r X at hn
    have hh := mul_le_mul_of_nonneg_right hNN hMb
    change CenteredPairEnergy (RieszKernel d s a 0) r X=_ at hx
    have hEl : -B≤CenteredPairEnergy (RieszKernel d s a 0) r X := by
      dsimp [B]
      rw [hx]
      nlinarith only [hn,hl,hh]
    have htE := mul_le_mul_of_nonneg_left hEl ht
    dsimp [Xi]
    nlinarith only [htE]
  have hexpcap : ∀ᵐX∂ν,Real.exp (Xi X)≤C := hcap.mono fun X hx =>
    (Real.exp_le_exp.mpr hx).trans (le_max_right _ _)
  have hi : Integrable (fun X => Real.exp (Xi X)) ν := Integrable.of_bound hXm.aestronglyMeasurable C (by
    filter_upwards [hexpcap] with X hx
    simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hx)
  refine ⟨hi,?_⟩
  calc
    (∫X,Real.exp (Xi X)∂ν)≤∫_X,C∂ν := integral_mono_ae hi (integrable_const _) hexpcap
    _=C := by simp
