import Tablet.EntropyFiniteCentering
import Mathlib.Tactic
open MeasureTheory
-- [TABLET NODE: EntropyDefectRemoval]
theorem EntropyDefectRemoval {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : (Ω → ℝ) → Prop) (E : (Ω → ℝ) → ℝ)
    (A B P : ℝ) (hA:0≤A) (hB:0≤B) (hP:0<P)
    (hdata : ∀f,D f→Measurable f ∧ ∃C:ℝ,∀ᵐ x∂μ,|f x|≤C)
    (hcenter : ∀f,D f→D (fun x=>f x-∫ y,f y∂μ))
    (hE : ∀f,D f→E (fun x=>f x-∫ y,f y∂μ)=E f)
    (hdef : ∀f,D f→Entropy μ (fun x=>f x^2) ≤ A*E f+B*(∫ x,f x^2∂μ))
    (hpi : ∀f,D f→(∫ x,(f x-∫ y,f y∂μ)^2∂μ)≤P*E f) :
    let ρ:=2/(16*A+(16*B+48)*P)
    0<ρ ∧ ∀f,D f→Entropy μ (fun x=>f x^2) ≤ (2/ρ)*E f := by
-- BODY
  have hcoef : 0<16*A+(16*B+48)*P := by nlinarith
  have hrho : 0<2/(16*A+(16*B+48)*P) := div_pos (by norm_num) hcoef
  refine ⟨hrho,?_⟩
  intro f hf
  obtain ⟨hfm,C,hC⟩:=hdata f hf
  let a:=∫ y,f y∂μ
  let g:=fun x=>f x-a
  have hgb:∃C:ℝ,∀ᵐ x∂μ,|g x|≤C := by
    refine ⟨C+|a|,hC.mono fun x hx=>?_⟩
    calc
      |f x-a| ≤ |f x|+|a| := by simpa [sub_eq_add_neg] using abs_add_le (f x) (-a)
      _ ≤ C+|a| := by linarith
  have hcen:=EntropyFiniteCentering μ g (hfm.sub measurable_const) hgb a
  have hfun:(fun x=>(g x+a)^2)=(fun x=>f x^2):=by funext x;dsimp [g];ring
  rw [hfun] at hcen
  have hdg:=hdef g (hcenter f hf)
  have heg:E g=E f:=hE f hf
  rw [heg] at hdg
  have hpg:(∫x,g x^2∂μ)≤P*E f:=hpi f hf
  have hbound:Entropy μ (fun x=>f x^2) ≤
    (16*A+(16*B+48)*P)*E f := by
    have hmult:=mul_le_mul_of_nonneg_left hpg (by linarith : 0≤16*B+48)
    nlinarith
  have hrate:2/(2/(16*A+(16*B+48)*P))=16*A+(16*B+48)*P := by
    field_simp
  rw [hrate]
  exact hbound
