import Tablet.AtomicPotentialFormBound
import Tablet.RieszStrictSourceDomination
import Tablet.RieszCoulombTranslatedFormBound
import Tablet.RieszHeatSourceTransfer
import Tablet.HeatSourceRegularity
import Tablet.RieszWeakSource
import Tablet.RieszL1Foundation
import Tablet.RieszLocalStructure
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Constructions
open MeasureTheory
open scoped ContDiff
-- [TABLET NODE: RieszAtomicPotentialBounds]
theorem RieszAtomicPotentialBounds (d : ℕ) (hd : 2 ≤ d) (s a B : ℝ)
    (hs : 0 ≤ s) (hsd : s ≤ (d : ℝ)-2) (hL : s < (d : ℝ)/2)
    (ha : 0 < a) (hB : 0 ≤ B) :
    ∃ c M A θ C : ℝ, 0 ≤ c ∧ 0 ≤ M ∧ 0 ≤ A ∧ 0 ≤ θ ∧ 0 ≤ C ∧
      (s < (d : ℝ)-2 → A=0) ∧ (s=(d : ℝ)-2 → θ=0) ∧
      ∀ (n : ℕ) (w : Fin n → ℝ) (y : Fin n → UnitAddTorus (Fin d)),
        (∀ j, 0 ≤ w j) → (∑ j, w j) ≤ B → ∀ ε : ℝ, 0 < ε →
        let U := AtomicPotential (RieszKernel d s a ε) w y
        TorusSmooth U ∧ (∀ x, -c ≤ U x) ∧
        (∀ x, TorusLaplacian U x ≤ M*B) ∧
        (∀ x, TorusLaplacian U x = M*(∑ j, w j)-
          ∑ j, w j*HeatSourceDensity d ε (RieszSourceMeasure d s a 1 M) (x-y j)) ∧
        ∀ u : UnitAddTorus (Fin d) → ℝ, TorusSmooth u →
          (∫ x, U x*(u x)^2) ≤ A*(∫ x, ‖TorusGradient u x‖^2)+
            θ*(∫ x, (M*B-TorusLaplacian U x)*(u x)^2)+C*(∫ x, (u x)^2) := by
-- BODY
  classical
  have continuous {d : ℕ} {f : UnitAddTorus (Fin d) → ℝ}
      (hf : TorusSmooth f) : Continuous f := by
    have hc : IsOpenQuotientMap ((↑) : ℝ → AddCircle (1 : ℝ)) :=
      QuotientAddGroup.isOpenQuotientMap_mk
    have hp : IsOpenQuotientMap
        (Pi.map (fun _ : Fin d => ((↑) : ℝ → AddCircle (1 : ℝ)))) :=
      IsOpenQuotientMap.piMap (fun _ => hc)
    have hq : IsOpenQuotientMap (TorusLift d) :=
      hp.comp (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isOpenQuotientMap
    exact hq.continuous_comp_iff.mp hf.continuous
  have bounded {d : ℕ} {f : UnitAddTorus (Fin d) → ℝ}
      (hf : TorusSmooth f) : ∃ C : ℝ, ∀ x, |f x| ≤ C := by
    obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn (continuous hf).continuousOn
    exact ⟨C, fun x => by simpa only [Real.norm_eq_abs] using hC x (Set.mem_univ x)⟩
  have hslt : s < (d : ℝ) := by linarith
  obtain ⟨c₀, hc₀, hFoundation⟩ := RieszL1Foundation d hd s a hs hslt ha
  obtain ⟨M,A₀,θ,C₀,hM,hA₀,hθ,hC₀,hFinite,hMass,hWeak,hStrict,hEndpoint,hAtom⟩ :
      ∃ M A₀ θ C₀ : ℝ, 0 ≤ M ∧ 0 ≤ A₀ ∧ 0 ≤ θ ∧ 0 ≤ C₀ ∧
      IsFiniteMeasure (RieszSourceMeasure d s a 1 M) ∧
      (RieszSourceMeasure d s a 1 M) Set.univ = ENNReal.ofReal M ∧
      (∀ φ : UnitAddTorus (Fin d) → ℝ, TorusSmooth φ →
        -(∫ x, RieszKernel d s a 0 x*TorusLaplacian φ x)+M*(∫ x, φ x) =
          ∫ x, φ x ∂RieszSourceMeasure d s a 1 M) ∧
      (s < (d : ℝ)-2 → A₀=0) ∧ (s=(d : ℝ)-2 → θ=0) ∧
      ∀ ε : ℝ, 0 < ε → ∀ z : UnitAddTorus (Fin d),
        ∀ u : UnitAddTorus (Fin d) → ℝ, TorusSmooth u →
        (∫ x, max (RieszKernel d s a ε (x-z)) 0*(u x)^2) ≤
          A₀*(∫ x, ‖TorusGradient u x‖^2)+
          θ*(∫ x, HeatSourceDensity d ε (RieszSourceMeasure d s a 1 M) (x-z)*(u x)^2)+
          C₀*(∫ x, (u x)^2) := by
    by_cases hstrict : s < (d : ℝ)-2
    · obtain ⟨M,hM,hPositive,hFinite,hMass,hWeak,hForm⟩ :=
        RieszStrictSourceDomination d hd s a 1 hs hstrict ha (by norm_num)
      obtain ⟨C,hC,hRaw,hHeat⟩ := hForm 1 (by norm_num)
      refine ⟨M,0,1,C,hM,le_rfl,by norm_num,hC,hFinite,hMass,hWeak,fun _ => rfl,?_,?_⟩
      · intro heq; linarith
      · intro ε hε z u hu
        letI : IsFiniteMeasure (RieszSourceMeasure d s a 1 M) := hFinite
        have hGc := continuous ((RieszLocalStructure d hd s a hs hslt ha).2.1 ε hε)
        have hHc := (HeatSourceRegularity d ε hε (RieszSourceMeasure d s a 1 M)).1
        have hu2 := (continuous hu).pow 2
        have hui : Integrable (fun x => (u x)^2) volume :=
          hu2.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
        have hleft : Integrable
            (fun x => max (RieszKernel d s a ε (x-z)) 0*(u x)^2) volume :=
          (((hGc.comp (continuous_id.sub continuous_const)).max continuous_const).mul hu2).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
        have hright : Integrable
            (fun x => HeatSourceDensity d ε (RieszSourceMeasure d s a 1 M) (x-z)*(u x)^2)
            volume :=
          ((hHc.comp (continuous_id.sub continuous_const)).mul hu2).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
        have hmono := integral_mono hleft (hright.add (hui.const_mul C)) (fun x => by
          have h := mul_le_mul_of_nonneg_right (hHeat ε hε (x-z)) (sq_nonneg (u x))
          simpa only [one_mul, add_mul, Pi.add_apply] using h)
        change (∫ x, max (RieszKernel d s a ε (x-z)) 0*(u x)^2) ≤
          ∫ x, HeatSourceDensity d ε (RieszSourceMeasure d s a 1 M) (x-z)*(u x)^2+
            C*(u x)^2 at hmono
        rw [integral_add hright (hui.const_mul C), integral_const_mul] at hmono
        simpa only [zero_mul, one_mul, zero_add] using hmono
    · have heq : s = (d : ℝ)-2 := le_antisymm hsd (le_of_not_gt hstrict)
      obtain ⟨M,hM,hCrit,hSub,hFinite,hMass,hWeak⟩ :=
        RieszWeakSource d hd s a 1 hs hsd ha (by norm_num)
      obtain ⟨A,C,hA,hC,hForm⟩ := (RieszCoulombTranslatedFormBound d hd s a hs ha heq hL).2
      refine ⟨M,A,0,C,hM,hA,le_rfl,hC,hFinite,hMass,hWeak,?_,fun _ => rfl,?_⟩
      · intro hh; exact (hstrict hh).elim
      · intro ε hε z u hu
        simpa only [zero_mul, add_zero] using hForm ε hε.le z u hu
  refine ⟨B*c₀,M,B*A₀,θ,B*C₀,mul_nonneg hB hc₀,hM,mul_nonneg hB hA₀,hθ,
    mul_nonneg hB hC₀,?_,hEndpoint,?_⟩
  · intro hstrict; rw [hStrict hstrict, mul_zero]
  · intro n w y hw hmass ε hε
    let G := RieszKernel d s a ε
    let H := HeatSourceDensity d ε (RieszSourceMeasure d s a 1 M)
    have hG : TorusSmooth G := (RieszLocalStructure d hd s a hs hslt ha).2.1 ε hε
    letI : IsFiniteMeasure (RieszSourceMeasure d s a 1 M) := hFinite
    have hHc : Continuous H := (HeatSourceRegularity d ε hε _).1
    have hSource := RieszHeatSourceTransfer d hd s a hs hslt ha M hM
      (RieszSourceMeasure d s a 1 M) hFinite hMass hWeak ε hε
    have hLap : ∀ x, TorusLaplacian G x = M-H x := by
      intro x; have h := hSource.2.2.1 x; dsimp [G,H]; linarith
    exact AtomicPotentialFormBound d B c₀ M A₀ θ C₀ hB hc₀ hM hA₀ hθ hC₀
      G H hG hHc (hFoundation ε hε.le).2.2.2.2.1 hSource.1 hLap
      (hAtom ε hε) n w y hw hmass
