import Tablet.CenteredDeletionPotential
import Tablet.CenteredKernelBounds
import Tablet.TiltNormalization
import Tablet.BoundedBackground
import Mathlib.MeasureTheory.Constructions.Pi
open MeasureTheory

-- [TABLET NODE: CenteredDeletionPotentialControls]
theorem CenteredDeletionPotentialControls (d N : ℕ) (l u C β : ℝ)
    (r : BoundedBackground d l u) (g : UnitAddTorus (Fin d) → ℝ)
    (hg : Measurable g) (hgi : Integrable g volume) (heven : ∀ z, g (-z)=g z)
    (hC : 0 ≤ C) (hgb : ∀ z, |g z| ≤ C) :
    let μ := (volume : Measure (UnitAddTorus (Fin d))).withDensity (fun z => ENNReal.ofReal (r.density z))
    let H := u * ∫ z, |g z| ∂volume
    IsProbabilityMeasure μ ∧
      (∀ i : Fin N, Measurable (CenteredDeletionPotential g r.density β i)) ∧
      (∀ (i : Fin N) p, |CenteredDeletionPotential g r.density β i p| ≤ |β/(N:ℝ)| *(N:ℝ)*(C+3*H)) ∧
      (∀ (i : Fin N) x, (∫ y, CenteredDeletionPotential g r.density β i (x,y)
        ∂Measure.pi (fun _ : ({i} : Finset (Fin N)) => μ))=0) := by
-- BODY
  classical
  let μ := (volume : Measure (UnitAddTorus (Fin d))).withDensity (fun z => ENNReal.ofReal (r.density z))
  have hp : IsProbabilityMeasure μ := by
      apply isProbabilityMeasure_iff.mpr
      rw [withDensity_apply _ MeasurableSet.univ]
      simp only [Measure.restrict_univ]
      rw [← ofReal_integral_eq_lintegral_ofReal (integrable_of_integral_eq_one r.mass)
        (r.bounds.mono fun _ hx => r.lower_pos.le.trans hx.1), r.mass]
      simp
  haveI := hp
  let H := u * ∫ z,|g z|∂volume
  let L := C+3*H
  have hu : 0 ≤ u := zero_le_one.trans r.one_le_upper
  have hL : 0 ≤ L := by
    dsimp [L,H]
    positivity
  have hkernel :
    let μ := (volume : Measure (UnitAddTorus (Fin d))).withDensity (fun z => ENNReal.ofReal (r.density z))
    let H := u * ∫ z, |g z| ∂volume
    Measurable (fun p : UnitAddTorus (Fin d) × UnitAddTorus (Fin d) => CenteredKernel g r.density p.1 p.2) ∧
      (∀ x y, |CenteredKernel g r.density x y| ≤ C+3*H) ∧
      (∀ x y, CenteredKernel g r.density x y = CenteredKernel g r.density y x) ∧
      (∀ y, Integrable (fun z => CenteredKernel g r.density z y) μ ∧
        (∫ z, CenteredKernel g r.density z y ∂μ)=0) := by
    have hrb : ∀ᵐ z ∂(volume : Measure (UnitAddTorus (Fin d))), 0 ≤ r.density z ∧ r.density z ≤ u :=
      r.bounds.mono fun z hz => ⟨r.lower_pos.le.trans hz.1,hz.2⟩
    have hgl : ∀ z, -C ≤ g z := fun z => (abs_le.mp (hgb z)).1
    obtain ⟨hmh,hbh,_,hbJ,hmK,hf,_⟩ := CenteredKernelBounds d g r.density hg hgi r.measurable
      u C r.one_le_upper hC hrb r.mass hgl
    let H := u * ∫ z,|g z|∂volume
    have hsub (a b : ℝ) : |a-b| ≤ |a|+|b| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le a (-b)
    have hK (x y : UnitAddTorus (Fin d)) : |CenteredKernel g r.density x y| ≤ C+3*H := by
      unfold CenteredKernel
      calc
        _ ≤ |g (x-y)-BackgroundPotential g r.density x-BackgroundPotential g r.density y|+|BackgroundPairMean g r.density| := abs_add_le _ _
        _ ≤ |g (x-y)-BackgroundPotential g r.density x|+|BackgroundPotential g r.density y|+|BackgroundPairMean g r.density| := by
          linarith only [hsub (g (x-y)-BackgroundPotential g r.density x) (BackgroundPotential g r.density y)]
        _ ≤ |g (x-y)|+|BackgroundPotential g r.density x|+|BackgroundPotential g r.density y|+|BackgroundPairMean g r.density| := by
          linarith only [hsub (g (x-y)) (BackgroundPotential g r.density x)]
        _ ≤ C+3*H := by linarith [hgb (x-y),(hbh x).2,(hbh y).2]
    have hs (x y : UnitAddTorus (Fin d)) : CenteredKernel g r.density x y = CenteredKernel g r.density y x := by
      have hh := heven (y-x)
      rw [neg_sub] at hh
      unfold CenteredKernel
      rw [hh]
      ring
    have hn : ∀ᵐ z ∂(volume : Measure (UnitAddTorus (Fin d))), 0 ≤ r.density z :=
      r.bounds.mono fun _ hz => r.lower_pos.le.trans hz.1
    obtain ⟨_,hmμ⟩ := TiltNormalization (volume : Measure (UnitAddTorus (Fin d))) r.density
      r.measurable hn (integrable_of_integral_eq_one r.mass) (by rw [r.mass]; norm_num)
    have htilt : NormalizedTilt volume r.density = μ := by
      simp only [NormalizedTilt,r.mass,div_one,μ]
    rw [htilt] at hmμ
    refine ⟨hmK,hK,hs,fun y => ?_⟩
    have hm : Measurable (fun z => CenteredKernel g r.density y z) :=
      hmK.comp (measurable_const.prodMk measurable_id)
    obtain ⟨hi,he⟩ := hmμ _ hm (hf y).1
    have heq : (fun z => CenteredKernel g r.density y z) = (fun z => CenteredKernel g r.density z y) :=
      funext fun z => hs y z
    rw [heq] at hi he
    have he0 : (∫ z, CenteredKernel g r.density z y ∂μ) = ∫ z, CenteredKernel g r.density y z * r.density z ∂volume := by
      simpa only [r.mass,div_one] using he
    exact ⟨hi, he0.trans (hf y).2⟩
  obtain ⟨hmK,hbK,_,hfK⟩ := hkernel
  have hm (i : Fin N) : Measurable (CenteredDeletionPotential g r.density β i) := by
    unfold CenteredDeletionPotential
    apply measurable_const.mul
    apply Finset.measurable_fun_sum
    intro j _
    have h1 : Measurable (fun p : (((Finset.univ : Finset (Fin N)).erase i → UnitAddTorus (Fin d)) × (({i} : Finset (Fin N)) → UnitAddTorus (Fin d))) => p.2 ⟨i,Finset.mem_singleton_self i⟩) :=
      (measurable_pi_apply (⟨i,Finset.mem_singleton_self i⟩ : ({i} : Finset (Fin N)))).comp measurable_snd
    have h2 : Measurable (fun p : (((Finset.univ : Finset (Fin N)).erase i → UnitAddTorus (Fin d)) × (({i} : Finset (Fin N)) → UnitAddTorus (Fin d))) => p.1 j) :=
      (measurable_pi_apply j).comp measurable_fst
    exact hmK.comp (h1.prodMk h2)
  have hb (i : Fin N) (p) : |CenteredDeletionPotential g r.density β i p| ≤ |β/(N:ℝ)| *(N:ℝ)*L := by
    unfold CenteredDeletionPotential
    rw [abs_mul]
    have hs := Finset.abs_sum_le_sum_abs
      (fun j : (Finset.univ : Finset (Fin N)).erase i => CenteredKernel g r.density (p.2 ⟨i,Finset.mem_singleton_self i⟩) (p.1 j)) Finset.univ
    have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
      hbK (p.2 ⟨i,Finset.mem_singleton_self i⟩) (p.1 j))
    have hc : ((Fintype.card ((Finset.univ : Finset (Fin N)).erase i) : ℕ) : ℝ) ≤ (N:ℝ) := by
      rw [Fintype.card_coe]
      exact_mod_cast (show ((Finset.univ : Finset (Fin N)).erase i).card ≤ N by
        simpa only [Finset.card_univ,Fintype.card_fin] using (Finset.card_erase_le (s := (Finset.univ : Finset (Fin N))) (a := i)))
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
    have htotal : |∑ j : (Finset.univ : Finset (Fin N)).erase i,
        CenteredKernel g r.density (p.2 ⟨i,Finset.mem_singleton_self i⟩) (p.1 j)| ≤ (N:ℝ)*L :=
      hs.trans (hh.trans (mul_le_mul_of_nonneg_right hc hL))
    exact (mul_le_mul_of_nonneg_left htotal (abs_nonneg _)).trans_eq (by ring)
  refine ⟨hp,hm,hb,fun i x => ?_⟩
  let j0 : ({i} : Finset (Fin N)) := ⟨i,Finset.mem_singleton_self i⟩
  let η := Measure.pi (fun _ : ({i} : Finset (Fin N)) => μ)
  have mp := measurePreserving_eval (fun _ : ({i} : Finset (Fin N)) => μ) j0
  have hji (j : (Finset.univ : Finset (Fin N)).erase i) :
      Integrable (fun y : ({i} : Finset (Fin N)) → UnitAddTorus (Fin d) => CenteredKernel g r.density (y j0) (x j)) η := by
    have hmj : Measurable (fun y : ({i} : Finset (Fin N)) → UnitAddTorus (Fin d) => CenteredKernel g r.density (y j0) (x j)) :=
      hmK.comp ((measurable_pi_apply j0).prodMk (measurable_const : Measurable (fun _ : ({i} : Finset (Fin N)) → UnitAddTorus (Fin d) => x j)))
    apply (integrable_const L).mono' hmj.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hbK (y j0) (x j)
  have hzero (j : (Finset.univ : Finset (Fin N)).erase i) :
      (∫ y : ({i} : Finset (Fin N)) → UnitAddTorus (Fin d), CenteredKernel g r.density (y j0) (x j) ∂η)=0 := by
    have hmz : Measurable (fun z => CenteredKernel g r.density z (x j)) :=
      hmK.comp (measurable_id.prodMk measurable_const)
    calc
      _ = ∫ z,CenteredKernel g r.density z (x j)∂μ := by
        rw [← mp.map_eq]
        exact (integral_map mp.measurable.aemeasurable hmz.aestronglyMeasurable).symm
      _ = 0 := (hfK (x j)).2
  unfold CenteredDeletionPotential
  rw [integral_const_mul,integral_finsetSum _ (fun j _ => hji j)]
  simp_rw [hzero]
  simp
