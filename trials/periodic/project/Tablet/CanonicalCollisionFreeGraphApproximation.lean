import Tablet.CollisionFreeSmoothCutoff
import Tablet.GradientGraphClosure
import Tablet.CanonicalLawUniformBounds
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.L2Space
open MeasureTheory Set Filter
open scoped ContDiff Topology
-- [TABLET NODE: CanonicalCollisionFreeGraphApproximation]
theorem CanonicalCollisionFreeGraphApproximation (d N:ℕ)(hd:2≤d)(hN:2≤N)
    (s a l u β:ℝ)(hs:0≤s)(hsd:s<(d:ℝ))(ha:0<a)
    (q:BoundedBackground d l u)(hβ:0≤β)(ε:ℝ)(hε:0≤ε) :
    let P := CanonicalLaw (N:=N) (RieszKernel d s a ε) q.density β
    ∀f:Configuration d N→ℝ, f∈SmoothCore d N →
      ∀(hf:MemLp f 2 P)(hD:MemLp (CoordinateGradient f) 2 P),
        (hf.toLp f,hD.toLp (CoordinateGradient f))∈GradientGraphClosure P true := by
-- BODY
  classical
  have configurationLift_quotient (d N : ℕ) :
      IsOpenQuotientMap (ConfigurationLift d N) := by
    have hc : IsOpenQuotientMap ((↑) : ℝ → AddCircle (1 : ℝ)) :=
      QuotientAddGroup.isOpenQuotientMap_mk
    have hp : IsOpenQuotientMap
        (Pi.map (fun _ : Fin N × Fin d => ((↑) : ℝ → AddCircle (1 : ℝ)))) :=
      IsOpenQuotientMap.piMap (fun _ => hc)
    have he := (PiLp.homeomorph 2 (fun _ : Fin N × Fin d => ℝ)).isOpenQuotientMap
    have hh := (Homeomorph.piCurry (X := Fin N) (Y := Fin d)
      (Z := AddCircle (1 : ℝ))).isOpenQuotientMap
    exact hh.comp (hp.comp he)
  
  have smoothCore_continuous {d N : ℕ} {f : Configuration d N → ℝ}
      (hf : f ∈ SmoothCore d N) : Continuous f := by
    apply (configurationLift_quotient d N).continuous_comp_iff.mp
    exact (show ContDiff ℝ ∞ (fun y => f (ConfigurationLift d N y)) from hf).continuous
  
  have smoothCore_bounded {d N : ℕ} {f : Configuration d N → ℝ}
      (hf : f ∈ SmoothCore d N) : ∃ C : ℝ, ∀ X, |f X| ≤ C := by
    have hc := (smoothCore_continuous hf).abs
    rcases isCompact_univ.exists_isMaxOn Set.univ_nonempty hc.continuousOn with ⟨X0,hX0,hmax⟩
    exact ⟨|f X0|, fun X => hmax (Set.mem_univ X)⟩
  
  -- Derivative descent is the only remaining topological step.
  have lift_translation_eq {d N : ℕ} (y z : EuclideanSpace ℝ (Fin N × Fin d))
      (h : ConfigurationLift d N y = ConfigurationLift d N z)
      (x : EuclideanSpace ℝ (Fin N × Fin d)) :
      ConfigurationLift d N (x + (z-y)) = ConfigurationLift d N x := by
    funext i j
    have hj := congrFun (congrFun h i) j
    change (y (i,j) : AddCircle (1 : ℝ)) = (z (i,j) : AddCircle (1 : ℝ)) at hj
    simp only [ConfigurationLift, PiLp.add_apply, PiLp.sub_apply]
    rw [AddCircle.coe_add, AddCircle.coe_sub, ← hj, sub_self, add_zero]
  
  have lift_fderiv_eq {d N : ℕ} (f : Configuration d N → ℝ)
      (y z : EuclideanSpace ℝ (Fin N × Fin d))
      (h : ConfigurationLift d N y = ConfigurationLift d N z) :
      fderiv ℝ (fun x => f (ConfigurationLift d N x)) y =
        fderiv ℝ (fun x => f (ConfigurationLift d N x)) z := by
    let q := fun x => f (ConfigurationLift d N x)
    have hfun : (fun x => q (x+(z-y))) = q := by
      funext x
      exact congrArg f (lift_translation_eq y z h x)
    have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := q) (x := y) (z-y)
    rw [hfun] at hd
    simpa using hd
  
  have coordinateGradient_on_lift {d N : ℕ} (f : Configuration d N → ℝ)
      (y : EuclideanSpace ℝ (Fin N × Fin d)) (ij : Fin N × Fin d) :
      CoordinateGradient f (ConfigurationLift d N y) ij =
        fderiv ℝ (fun x => f (ConfigurationLift d N x)) y
          (EuclideanSpace.single ij 1) := by
    let z : EuclideanSpace ℝ (Fin N × Fin d) := WithLp.toLp 2
      (fun ij => (AddCircle.equivIco (1 : ℝ) 0 (ConfigurationLift d N y ij.1 ij.2) : ℝ))
    have hz : ConfigurationLift d N z = ConfigurationLift d N y := by
      funext i j
      simp [ConfigurationLift, z, AddCircle.coe_equivIco]
    change fderiv ℝ (fun x => f (ConfigurationLift d N x)) z (EuclideanSpace.single ij 1) = _
    rw [lift_fderiv_eq f z y hz]
  
  have coordinateGradient_continuous {d N : ℕ} {f : Configuration d N → ℝ}
      (hf : f ∈ SmoothCore d N) : Continuous (CoordinateGradient f) := by
    apply (configurationLift_quotient d N).continuous_comp_iff.mp
    have hF : ContDiff ℝ ∞ (fun y => f (ConfigurationLift d N y)) := hf
    have hc : Continuous (fun y : EuclideanSpace ℝ (Fin N × Fin d) =>
        WithLp.toLp 2 (fun ij => fderiv ℝ (fun x => f (ConfigurationLift d N x)) y
          (EuclideanSpace.single ij 1))) := by
      apply (PiLp.continuous_toLp 2 (fun _ : Fin N × Fin d => ℝ)).comp
      apply continuous_pi
      intro ij
      exact (hF.continuous_fderiv_apply (by simp)).comp
        (continuous_id.prodMk continuous_const)
    have he : (fun y => CoordinateGradient f (ConfigurationLift d N y)) =
        (fun y : EuclideanSpace ℝ (Fin N × Fin d) =>
          WithLp.toLp 2 (fun ij => fderiv ℝ (fun x => f (ConfigurationLift d N x)) y
            (EuclideanSpace.single ij 1))) := by
      funext y
      ext ij
      exact coordinateGradient_on_lift f y ij
    have hg : Continuous (fun y => CoordinateGradient f (ConfigurationLift d N y)) := by
      rw [he]
      exact hc
    exact hg
  
  have smooth_memLp {d N:ℕ}(P:Measure (Configuration d N))[IsProbabilityMeasure P]
      {f:Configuration d N→ℝ}(hf:f∈SmoothCore d N) :
      MemLp f 2 P ∧ MemLp (CoordinateGradient f) 2 P := by
    exact ⟨(smoothCore_continuous hf).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _),
      (coordinateGradient_continuous hf).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)⟩
  have coordinateGradient_mul {d N:ℕ}(f χ:Configuration d N→ℝ)
      (hf:f∈SmoothCore d N)(hχ:χ∈SmoothCore d N)(X:Configuration d N) :
      CoordinateGradient (fun X=>f X*χ X) X =
        f X • CoordinateGradient χ X + χ X • CoordinateGradient f X := by
    obtain ⟨y,rfl⟩ := (configurationLift_quotient d N).surjective X
    ext ij
    rw [coordinateGradient_on_lift]
    have hfl : ContDiff ℝ ∞ (fun y=>f (ConfigurationLift d N y)) := hf
    have hχl : ContDiff ℝ ∞ (fun y=>χ (ConfigurationLift d N y)) := hχ
    have hd := (hfl.differentiable (by simp) y).hasFDerivAt.mul
      (hχl.differentiable (by simp) y).hasFDerivAt
    change HasFDerivAt (fun y=>f (ConfigurationLift d N y)*χ (ConfigurationLift d N y)) _ y at hd
    rw [hd.fderiv]
    simp only [PiLp.add_apply,PiLp.smul_apply,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply,smul_eq_mul]
    rw [coordinateGradient_on_lift,coordinateGradient_on_lift]

  have integral_domination {d N:ℕ}(P:Measure (Configuration d N))(R:ℝ)(hR:0≤R)
      (hdom:P≤ENNReal.ofReal R • volume)(h:Configuration d N→ℝ)
      (hh:Continuous h)(hn:∀X,0≤h X) : (∫X,h X∂P)≤R*(∫X,h X) := by
    have hi : Integrable h volume := hh.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hm := integral_mono_measure hdom (Eventually.of_forall hn)
      (hi.smul_measure ENNReal.ofReal_ne_top)
    simpa only [integral_smul_measure,ENNReal.toReal_ofReal hR,smul_eq_mul] using hm
  have product_cutoff_errors {d N:ℕ}(P:Measure (Configuration d N))(R:ℝ)(hR:0≤R)
      (hdom:P≤ENNReal.ofReal R • volume)(f χ:Configuration d N→ℝ)
      (hf:f∈SmoothCore d N)(hχ:χ∈SmoothCore d N)(F H:ℝ)(hF:0≤F)(hH:0≤H)
      (hfb:∀X,|f X|≤F)(hgb:∀X,‖CoordinateGradient f X‖^2≤H) :
      (∫X,(f X*χ X-f X)^2∂P)+
        (∫X,‖CoordinateGradient (fun X=>f X*χ X) X-CoordinateGradient f X‖^2∂P) ≤
        R*(3*F^2+2*H)*((∫X,(χ X-1)^2)+(∫X,‖CoordinateGradient χ X‖^2)) := by
    let u:=fun X=>f X*χ X
    have hul : u∈SmoothCore d N := (show ContDiff ℝ ∞ (fun y=>f (ConfigurationLift d N y)) from hf).mul
      (show ContDiff ℝ ∞ (fun y=>χ (ConfigurationLift d N y)) from hχ)
    have hF2 (X) : (f X)^2≤F^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (f X)) (hfb X) 2
    have hfun (X) : (u X-f X)^2≤F^2*(χ X-1)^2 := by
      have he : u X-f X=f X*(χ X-1) := by dsimp[u];ring
      rw [he,mul_pow]
      exact mul_le_mul_of_nonneg_right (hF2 X) (sq_nonneg _)
    have hgrad (X) : ‖CoordinateGradient u X-CoordinateGradient f X‖^2≤
        2*F^2*‖CoordinateGradient χ X‖^2+2*H*(χ X-1)^2 := by
      have he : CoordinateGradient u X-CoordinateGradient f X =
          f X • CoordinateGradient χ X+(χ X-1) • CoordinateGradient f X := by
        rw [coordinateGradient_mul f χ hf hχ]
        module
      rw [he]
      have hh := norm_add_le (f X • CoordinateGradient χ X) ((χ X-1) • CoordinateGradient f X)
      have hs := pow_le_pow_left₀ (norm_nonneg _) hh 2
      have hsq := sq_nonneg (‖f X • CoordinateGradient χ X‖-‖(χ X-1) • CoordinateGradient f X‖)
      have hb : ‖f X • CoordinateGradient χ X+(χ X-1) • CoordinateGradient f X‖^2≤
        2*‖f X • CoordinateGradient χ X‖^2+2*‖(χ X-1) • CoordinateGradient f X‖^2 := by nlinarith
      simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] at hb
      have hb1 := mul_le_mul_of_nonneg_right (hF2 X) (sq_nonneg ‖CoordinateGradient χ X‖)
      have hb2 := mul_le_mul_of_nonneg_left (hgb X) (sq_nonneg (χ X-1))
      nlinarith
    have hdefcont : Continuous (fun X=>(χ X-1)^2) := ((smoothCore_continuous hχ).sub continuous_const).pow 2
    have henergycont : Continuous (fun X=>‖CoordinateGradient χ X‖^2) := (coordinateGradient_continuous hχ).norm.pow 2
    have hdefi : Integrable (fun X=>(χ X-1)^2) volume :=
      hdefcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have henergyi : Integrable (fun X=>‖CoordinateGradient χ X‖^2) volume :=
      henergycont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hfi := integral_mono_of_nonneg (Eventually.of_forall fun X=>sq_nonneg (u X-f X))
      (hdefi.const_mul (F^2)) (Eventually.of_forall hfun)
    rw [integral_const_mul] at hfi
    have hgi := integral_mono_of_nonneg
      (Eventually.of_forall fun X=>sq_nonneg ‖CoordinateGradient u X-CoordinateGradient f X‖)
      ((henergyi.const_mul (2*F^2)).add (hdefi.const_mul (2*H))) (Eventually.of_forall hgrad)
    change (∫ X, ‖CoordinateGradient u X-CoordinateGradient f X‖^2) ≤
      (∫ X, 2*F^2*‖CoordinateGradient χ X‖^2+2*H*(χ X-1)^2) at hgi
    rw [integral_add (henergyi.const_mul _) (hdefi.const_mul _),integral_const_mul,integral_const_mul] at hgi
    have hfp := integral_domination P R hR hdom _
      (((smoothCore_continuous hul).sub (smoothCore_continuous hf)).pow 2)
      (fun X=>sq_nonneg (u X-f X))
    have hgp := integral_domination P R hR hdom _
      (((coordinateGradient_continuous hul).sub (coordinateGradient_continuous hf)).norm.pow 2)
      (fun X=>sq_nonneg ‖CoordinateGradient u X-CoordinateGradient f X‖)
    have hdp : 0≤∫X,(χ X-1)^2 := integral_nonneg fun _=>sq_nonneg _
    have hep : 0≤∫X,‖CoordinateGradient χ X‖^2 := integral_nonneg fun _=>sq_nonneg _
    have hRfi := mul_le_mul_of_nonneg_left hfi hR
    have hRgi := mul_le_mul_of_nonneg_left hgi hR
    have hRH : 0≤R*H := mul_nonneg hR hH
    have hRF : 0≤R*F^2 := mul_nonneg hR (sq_nonneg F)
    dsimp[u] at *
    nlinarith [mul_nonneg hRH hep,mul_nonneg hRF hdp,mul_nonneg hRF hep]

  have lp_norm_square {Ω E:Type}[MeasurableSpace Ω][NormedAddCommGroup E][InnerProductSpace ℝ E]
      (P:Measure Ω)(f:Ω→E)(hf:MemLp f 2 P) : ‖hf.toLp f‖^2=∫x,‖f x‖^2∂P := by
    rw [←real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx,real_inner_self_eq_norm_sq]
  have smooth_graph_approximation (d N:ℕ)(hd:2≤d)(hN:2≤N)
      (P:Measure (Configuration d N))[IsProbabilityMeasure P](R:ℝ)(hR:0≤R)
      (hdom:P≤ENNReal.ofReal R • volume)(f:Configuration d N→ℝ)(hf:f∈SmoothCore d N)
      (hfP:MemLp f 2 P)(hDfP:MemLp (CoordinateGradient f) 2 P) :
      (hfP.toLp f,hDfP.toLp (CoordinateGradient f))∈GradientGraphClosure P true := by
    obtain ⟨C,hC,hcut⟩ := CollisionFreeSmoothCutoff d N hd hN
    obtain ⟨F,hF⟩ := smoothCore_bounded hf
    have hF0 : 0≤F := (abs_nonneg (f 0)).trans (hF 0)
    obtain ⟨H,hH⟩ := (ConfigurationCalculus d N).2.2.2 f hf |>.2.2.2.2.1
    have hH0 : 0≤H := (sq_nonneg ‖CoordinateGradient f 0‖).trans (hH 0)
    let A : ℝ := 3*F^2+2*H
    have hA : 0≤A := by dsimp[A];positivity
    apply Metric.mem_closure_iff.mpr
    intro δ hδ
    let T : ℝ := (R*A*C+1)/δ^2
    have hT : 0<T := by dsimp[T];positivity
    obtain ⟨χ,hχ,hχb,hcost⟩ := hcut T hT
    let u:=fun X=>f X*χ X
    have hul : u∈SmoothCore d N :=
      (show ContDiff ℝ ∞ (fun y=>f (ConfigurationLift d N y)) from hf).mul
        (show ContDiff ℝ ∞ (fun y=>χ (ConfigurationLift d N y)) from hχ.1)
    have huc : u∈CollisionFreeCore d N := ⟨hul,hχ.2.mono_left tsupport_mul_subset_right⟩
    obtain ⟨huP,hDuP⟩ := smooth_memLp P hul
    refine ⟨(huP.toLp u,hDuP.toLp (CoordinateGradient u)),?_,?_⟩
    · exact ⟨u,huP,hDuP,by simpa using huc,rfl⟩
    · have herr := product_cutoff_errors P R hR hdom f χ hf hχ.1 F H hF0 hH0 hF hH
      have hRC := mul_le_mul_of_nonneg_left hcost (mul_nonneg hR hA)
      have he : R*A*(C/T)=R*A*C/T := by ring
      rw [he] at hRC
      have hsmall : R*A*C/T<δ^2 := by
        apply (div_lt_iff₀ hT).mpr
        have hδsq : δ^2≠0 := ne_of_gt (sq_pos_of_pos hδ)
        have he : δ^2*T=R*A*C+1 := by dsimp[T];field_simp
        rw [he]
        linarith
      have htotal : (∫X,(u X-f X)^2∂P)+
          (∫X,‖CoordinateGradient u X-CoordinateGradient f X‖^2∂P)<δ^2 :=
        herr.trans hRC |>.trans_lt hsmall
      have hnonf : 0≤∫X,(u X-f X)^2∂P := integral_nonneg fun _=>sq_nonneg _
      have hnong : 0≤∫X,‖CoordinateGradient u X-CoordinateGradient f X‖^2∂P := integral_nonneg fun _=>sq_nonneg _
      have hfsq : ‖huP.toLp u-hfP.toLp f‖^2=∫X,(u X-f X)^2∂P := by
        rw [←huP.toLp_sub hfP]
        simpa only [Pi.sub_apply,Real.norm_eq_abs,sq_abs] using lp_norm_square P (u-f) (huP.sub hfP)
      have hgsq : ‖hDuP.toLp (CoordinateGradient u)-hDfP.toLp (CoordinateGradient f)‖^2=
          ∫X,‖CoordinateGradient u X-CoordinateGradient f X‖^2∂P := by
        rw [←hDuP.toLp_sub hDfP]
        exact lp_norm_square P (CoordinateGradient u-CoordinateGradient f) (hDuP.sub hDfP)
      have hfnorm : ‖huP.toLp u-hfP.toLp f‖<δ := by nlinarith [hfsq,norm_nonneg (huP.toLp u-hfP.toLp f)]
      have hgnorm : ‖hDuP.toLp (CoordinateGradient u)-hDfP.toLp (CoordinateGradient f)‖<δ := by
        nlinarith [hgsq,norm_nonneg (hDuP.toLp (CoordinateGradient u)-hDfP.toLp (CoordinateGradient f))]
      rw [Prod.dist_eq]
      apply max_lt
      · simpa only [dist_eq_norm,norm_sub_rev] using hfnorm
      · simpa only [dist_eq_norm,norm_sub_rev] using hgnorm

  dsimp only
  let P := CanonicalLaw (N:=N) (RieszKernel d s a ε) q.density β
  obtain ⟨L,M,hL,hM,hall⟩ := CanonicalLawUniformBounds d N hd hN s a l u β hs hsd ha q hβ
  obtain ⟨hwm,hwi,hZ,hW,hP⟩ := hall ε hε
  letI : IsProbabilityMeasure P := hP
  let W := GibbsWeight (N:=N) (RieszKernel d s a ε) q.density β
  let Z := ∫X,W X
  have hZpos : 0<Z := hL.trans_le hZ
  let R := M/L
  have hR : 0≤R := div_nonneg hM hL.le
  have hdom : P ≤ ENNReal.ofReal R • volume := by
    change volume.withDensity (fun X=>ENNReal.ofReal (W X/Z)) ≤ ENNReal.ofReal R • volume
    rw [←withDensity_const]
    apply withDensity_mono
    filter_upwards [hW] with X hX
    apply ENNReal.ofReal_le_ofReal
    exact div_le_div₀ hM hX.2 hL hZ
  intro f hf hfP hDfP
  exact smooth_graph_approximation d N hd hN P R hR hdom f hf hfP hDfP
