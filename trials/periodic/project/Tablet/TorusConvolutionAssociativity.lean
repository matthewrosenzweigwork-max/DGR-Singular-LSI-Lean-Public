import Tablet.HeatOperatorBounds
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.Prod
open MeasureTheory
-- [TABLET NODE: TorusConvolutionAssociativity]
theorem TorusConvolutionAssociativity (d : ℕ)
    (f g r : UnitAddTorus (Fin d)→ℝ) (R : ℝ)
    (hf : Integrable f volume) (hg : Integrable g volume) (hr : Measurable r)
    (hrb : ∀ᵐ x∂volume,‖r x‖≤R) :
    ∀ x, convolution (convolution f g (ContinuousLinearMap.mul ℝ ℝ) volume) r
      (ContinuousLinearMap.mul ℝ ℝ) volume x =
      convolution f (convolution g r (ContinuousLinearMap.mul ℝ ℝ) volume)
        (ContinuousLinearMap.mul ℝ ℝ) volume x := by
-- BODY
  classical
  let T := UnitAddTorus (Fin d)
  let m := (volume : Measure T)
  let L := ContinuousLinearMap.mul ℝ ℝ
  have hgr (x:T) : ConvolutionExistsAt (fun y=>‖g y‖) (fun y=>‖r y‖) x L m := by
    have hb : ∀ᵐ y∂m,‖‖r (x-y)‖‖≤R :=
      by
        have hshift : ∀ᵐ y∂m,‖r (x-y)‖≤R := (quasiMeasurePreserving_sub_left_of_right_invariant m x).tendsto_ae hrb
        filter_upwards [hshift] with y hy
        simpa only [norm_norm] using hy
    exact hg.norm.mul_bdd ((hr.norm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable) hb
  let G : T→ℝ := convolution (fun y=>‖g y‖) (fun y=>‖r y‖) L m
  have hGm : AEStronglyMeasurable G m := by
    have hj : AEStronglyMeasurable (fun p:T×T=>‖g p.2‖*‖r (p.1-p.2)‖) (m.prod m) :=
      (hg.norm.aestronglyMeasurable.comp_snd).mul ((hr.norm.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable)
    exact hj.integral_prod_right'
  have hGbound (x:T) : ‖G x‖≤R*(∫y,‖g y‖∂m) := by
    have hgint := hgr x
    have hh := norm_integral_le_integral_norm (fun y=>‖g y‖*‖r (x-y)‖) (μ:=m)
    have hb : ∀ᵐ y∂m,‖r (x-y)‖≤R :=
      (quasiMeasurePreserving_sub_left_of_right_invariant m x).tendsto_ae hrb
    have hupper : (∫y,‖‖g y‖*‖r (x-y)‖‖∂m)≤R*(∫y,‖g y‖∂m) := by
      rw [←integral_const_mul]
      apply integral_mono_ae hgint.norm (hg.norm.const_mul R)
      filter_upwards [hb] with y hy
      change ‖‖g y‖*‖r (x-y)‖‖≤R*‖g y‖
      simp only [norm_mul,norm_norm]
      exact (mul_le_mul_of_nonneg_left hy (norm_nonneg _)).trans_eq (mul_comm _ _)
    exact hh.trans hupper
  have hfgk (x:T) : ConvolutionExistsAt (fun y=>‖f y‖) G x L m := by
    have hem := hGm.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left_of_right_invariant m x)
    have hb : ∀ᵐ y∂m,‖G (x-y)‖≤R*(∫y,‖g y‖∂m) := Filter.Eventually.of_forall fun y=>hGbound _
    exact hf.norm.mul_bdd hem hb
  intro x
  exact convolution_assoc L L L L (by intros; simp only [L,ContinuousLinearMap.mul_apply'];ring)
    hf.aestronglyMeasurable hg.aestronglyMeasurable hr.aestronglyMeasurable
    (hf.ae_convolution_exists L hg) (Filter.Eventually.of_forall hgr) (hfgk x)
