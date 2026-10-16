module

public import Tablet.CenteredPairEnergy
public import Tablet.ProductDensityMeasureIdentity
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
-- [TABLET NODE: CenteredPairEnergyAEDecomposition]
theorem CenteredPairEnergyAEDecomposition (d N:ℕ)(g h k r:UnitAddTorus (Fin d)→ℝ)
    (hg:Measurable g)(hh:Measurable h)(hk:Measurable k)
    (hgi:Integrable g volume)(hhi:Integrable h volume)(hki:Integrable k volume)
    (hr:Measurable r)(M c:ℝ)(hM:0≤M)(hrb:∀ᵐx∂volume,0≤r x∧r x≤M)
    (hrmass:∫x,r x=1)(heq:g=ᵐ[volume]fun x=>h x+k x-c) :
    (∀x,BackgroundPotential g r x=BackgroundPotential h r x+BackgroundPotential k r x-c) ∧
    BackgroundPairMean g r=BackgroundPairMean h r+BackgroundPairMean k r-c ∧
    (CenteredPairEnergy (N:=N) g r =ᵐ[volume] fun X=>CenteredPairEnergy h r X+CenteredPairEnergy k r X) ∧
    (CenteredPairEnergy (N:=N) g r =ᵐ[Measure.pi (fun _:Fin N=>(volume:Measure (UnitAddTorus (Fin d))).withDensity (fun x=>ENNReal.ofReal (r x)))]
      fun X=>CenteredPairEnergy h r X+CenteredPairEnergy k r X) := by
-- BODY
  have hpot_integral {d : ℕ} (v w : UnitAddTorus (Fin d)→ℝ) :
      BackgroundPotential v w = fun x => ∫y,v (x-y)*w y := by
    funext x
    unfold BackgroundPotential convolution
    change (∫y,w y*v (x-y)) = ∫y,v (x-y)*w y
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => mul_comm _ _)
  classical
  have unit_probability (d:ℕ) : IsProbabilityMeasure (volume:Measure (UnitAddTorus (Fin d))) := by
    haveI : IsProbabilityMeasure (volume:Measure (AddCircle (1:ℝ))) := by
      rw [AddCircle.volume_eq_smul_haarAddCircle];simp;infer_instance
    infer_instance
  have background_integrable (d:ℕ)(f r:UnitAddTorus (Fin d)→ℝ)
      (hf:Measurable f)(hfi:Integrable f volume)(hr:Measurable r)(M:ℝ)(hM:0≤M)
      (hrb:∀ᵐx∂volume,0≤r x∧r x≤M) :
      (∀x,Integrable (fun y=>f (x-y)*r y) volume) ∧
      Integrable (fun x=>BackgroundPotential f r x*r x) volume := by
    haveI := unit_probability d
    have hrnorm : ∀ᵐx∂volume,‖r x‖≤M := by
      filter_upwards [hrb] with x hx
      simpa only [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2
    have hji (x) : Integrable (fun y=>f (x-y)*r y) volume :=
      (hfi.comp_sub_left x).mul_bdd hr.aestronglyMeasurable hrnorm
    have hjm : Measurable (fun p:UnitAddTorus (Fin d)×UnitAddTorus (Fin d)=>f (p.1-p.2)*r p.2) :=
      (hf.comp (measurable_fst.sub measurable_snd)).mul (hr.comp measurable_snd)
    have hm : Measurable (BackgroundPotential f r) := by
      rw [hpot_integral]
      exact hjm.stronglyMeasurable.integral_prod_right.measurable
    have hb (x) : |BackgroundPotential f r x|≤M*(∫y,|f y|) := by
      calc
        _ ≤ ∫y,‖f (x-y)*r y‖ := by
          simpa only [hpot_integral,Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y=>f (x-y)*r y)
        _ ≤ ∫y,M*|f (x-y)| := by
          apply integral_mono_ae (hji x).norm ((hfi.abs.comp_sub_left x).const_mul M)
          filter_upwards [hrb] with y hy
          rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hy.1]
          nlinarith [abs_nonneg (f (x-y))]
        _ = _ := by rw [integral_const_mul,integral_sub_left_eq_self (fun y:UnitAddTorus (Fin d)=>|f y|) volume x]
    have hip : Integrable (BackgroundPotential f r) volume :=
      Integrable.of_bound hm.aestronglyMeasurable _ (Eventually.of_forall fun x=> by
        simpa only [Real.norm_eq_abs] using hb x)
    exact ⟨hji,hip.mul_bdd hr.aestronglyMeasurable hrnorm⟩
  have background_decomposition (d:ℕ)(g h k r:UnitAddTorus (Fin d)→ℝ)
      (hg:Measurable g)(hh:Measurable h)(hk:Measurable k)
      (hgi:Integrable g volume)(hhi:Integrable h volume)(hki:Integrable k volume)
      (hr:Measurable r)(M c:ℝ)(hM:0≤M)(hrb:∀ᵐx∂volume,0≤r x∧r x≤M)
      (hrmass:∫x,r x=1)(heq:g=ᵐ[volume]fun x=>h x+k x-c) :
      (∀x,BackgroundPotential g r x=BackgroundPotential h r x+BackgroundPotential k r x-c) ∧
      BackgroundPairMean g r=BackgroundPairMean h r+BackgroundPairMean k r-c := by
    haveI := unit_probability d
    obtain ⟨hgiw,hgir⟩ := background_integrable d g r hg hgi hr M hM hrb
    obtain ⟨hhiw,hhir⟩ := background_integrable d h r hh hhi hr M hM hrb
    obtain ⟨hkiw,hkir⟩ := background_integrable d k r hk hki hr M hM hrb
    have hrnorm : ∀ᵐx∂volume,‖r x‖≤M := by
      filter_upwards [hrb] with x hx
      simpa only [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2
    have hri : Integrable r volume := Integrable.of_bound hr.aestronglyMeasurable M hrnorm
    have hp (x) : BackgroundPotential g r x=BackgroundPotential h r x+BackgroundPotential k r x-c := by
      have heqx := (volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae_eq_comp heq
      simp only [hpot_integral]
      calc
        (∫y,g (x-y)*r y) = ∫y,h (x-y)*r y+k (x-y)*r y-c*r y := by
          apply integral_congr_ae
          filter_upwards [heqx] with y hy
          change g (x-y)=h (x-y)+k (x-y)-c at hy
          rw [hy];ring
        _ = _ := by
          have hiadd : Integrable (fun y=>h (x-y)*r y+k (x-y)*r y) volume := (hhiw x).add (hkiw x)
          rw [integral_sub hiadd (hri.const_mul c),
            integral_add (hhiw x) (hkiw x),integral_const_mul,hrmass,mul_one]
    refine ⟨hp,?_⟩
    unfold BackgroundPairMean
    calc
      (∫x,BackgroundPotential g r x*r x) =
        ∫x,BackgroundPotential h r x*r x+BackgroundPotential k r x*r x-c*r x := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x=>by dsimp only;rw [hp x];ring
      _ = _ := by
        have hiadd : Integrable (fun x=>BackgroundPotential h r x*r x+BackgroundPotential k r x*r x) volume := hhir.add hkir
        rw [integral_sub hiadd (hri.const_mul c), integral_add hhir hkir,
          integral_const_mul,hrmass,mul_one]
  have configuration_pair_measurePreserving (d N : ℕ) (i j : Fin N) (hij : i ≠ j) :
      MeasurePreserving (fun X : Configuration d N => (X i, X j))
        volume (volume.prod volume) := by
    haveI := unit_probability d
    have hi := (iIndepFun_pi (μ := fun _ : Fin N =>
      (volume : Measure (UnitAddTorus (Fin d)))) (X := fun _ => id)
      (fun _ => aemeasurable_id)).indepFun hij
    refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), ?_⟩
    change Measure.map (fun X : Configuration d N => (X i, X j))
      (Measure.pi (fun _ : Fin N => (volume : Measure (UnitAddTorus (Fin d))))) = _
    have h := hi.map_prod_eq_prod_map_map
      (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
    simpa only [(measurePreserving_eval (fun _ : Fin N =>
      (volume : Measure (UnitAddTorus (Fin d)))) i).map_eq,
      (measurePreserving_eval (fun _ : Fin N =>
      (volume : Measure (UnitAddTorus (Fin d)))) j).map_eq] using h
  
  
  have configuration_difference_measurePreserving (d N : ℕ) (i j : Fin N) (hij : i ≠ j) :
      MeasurePreserving (fun X : Configuration d N => X i - X j) volume volume := by
    haveI := unit_probability d
    have hp := configuration_pair_measurePreserving d N i j hij
    have hs : MeasurePreserving (fun p : UnitAddTorus (Fin d) × UnitAddTorus (Fin d) => p.1 - p.2)
        (volume.prod volume) volume :=
      measurePreserving_fst.comp (measurePreserving_sub_prod volume volume)
    exact hs.comp hp

  haveI := unit_probability d
  obtain ⟨hp,hb⟩ := background_decomposition d g h k r hg hh hk hgi hhi hki hr M c hM hrb hrmass heq
  have hterm (i j:Fin N) : ∀ᵐX:Configuration d N∂volume,
      (if i<j then CenteredKernel g r (X i) (X j) else 0)=
      (if i<j then CenteredKernel h r (X i) (X j) else 0)+
      (if i<j then CenteredKernel k r (X i) (X j) else 0) := by
    by_cases hij:i<j
    · have hdiff := (configuration_difference_measurePreserving d N i j (ne_of_lt hij)).quasiMeasurePreserving.ae_eq_comp heq
      filter_upwards [hdiff] with X hX
      simp only [hij,ite_true]
      unfold CenteredKernel
      change g (X i-X j)=h (X i-X j)+k (X i-X j)-c at hX
      rw [hX,hp (X i),hp (X j),hb]
      ring
    · exact Eventually.of_forall fun X=>by simp[hij]
  have hHaar : CenteredPairEnergy (N:=N) g r =ᵐ[volume] fun X=>CenteredPairEnergy h r X+CenteredPairEnergy k r X := by
    filter_upwards [ae_all_iff.mpr fun i=>ae_all_iff.mpr fun j=>hterm i j] with X hX
    unfold CenteredPairEnergy
    calc
      _ = (N:ℝ)⁻¹*∑i:Fin N,∑j:Fin N,
          ((if i<j then CenteredKernel h r (X i) (X j) else 0)+
           (if i<j then CenteredKernel k r (X i) (X j) else 0)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact hX i j
      _ = _ := by simp only [Finset.sum_add_distrib,mul_add]
  refine ⟨hp,hb,hHaar,?_⟩
  have hrnorm : ∀ᵐx∂volume,‖r x‖≤M := by
    filter_upwards [hrb] with x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2
  have hri : Integrable r volume := Integrable.of_bound hr.aestronglyMeasurable M hrnorm
  rw [(ProductDensityMeasureIdentity d N r hr (hrb.mono fun _ hx=>hx.1) hri hrmass).1]
  exact (withDensity_absolutelyContinuous volume _).ae_eq hHaar
