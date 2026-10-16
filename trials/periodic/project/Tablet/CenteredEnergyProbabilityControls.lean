module

public import Tablet.CenteredDeletionPotentialControls
public import Tablet.CenteredDeletionEnergySum
public import Tablet.CenteredCanonicalLaw
public import Tablet.BoundedGibbsRelativeEntropy

@[expose] public section
open MeasureTheory InformationTheory

-- [TABLET NODE: CenteredEnergyProbabilityControls]
theorem CenteredEnergyProbabilityControls (d N : ℕ) (l u C β : ℝ)
    (r : BoundedBackground d l u) (g : UnitAddTorus (Fin d) → ℝ)
    (hg : Measurable g) (hgi : Integrable g volume) (heven : ∀ z, g (-z)=g z)
    (hC : 0 ≤ C) (hgb : ∀ z, |g z| ≤ C) :
    Measurable (fun X : Configuration d N => β*CenteredPairEnergy g r.density X) ∧
    (∃ Q : ℝ, ∀ X : Configuration d N, |β*CenteredPairEnergy g r.density X| ≤ Q) ∧
    IsProbabilityMeasure (CenteredCanonicalLaw (N := N) g r.density β) := by
-- BODY
  let μ := (volume : Measure (UnitAddTorus (Fin d))).withDensity (fun z => ENNReal.ofReal (r.density z))
  let U := CenteredDeletionPotential (N := N) g r.density β
  let H := u * ∫ z,|g z|∂volume
  let Q := |β/(N:ℝ)| * (N:ℝ)*(C+3*H)
  obtain ⟨hp,hmU,hbU,hzero⟩ := CenteredDeletionPotentialControls d N l u C β r g hg hgi heven hC hgb
  haveI : IsProbabilityMeasure μ := hp
  have hpair (X : Configuration d N) :
      (∑ i : Fin N, U i ((fun j => X j),(fun j => X j))) = 2*(β*CenteredPairEnergy g r.density X) := by
    have hh := (CenteredDeletionEnergySum g r.density heven X β).2
    simpa only [U,mul_assoc] using hh
  let F := fun (i : Fin N) (X : Configuration d N) =>
    ((fun j : (Finset.univ : Finset (Fin N)).erase i => X j), (fun j : ({i} : Finset (Fin N)) => X j))
  have hmF (i : Fin N) : Measurable (F i) :=
    (measurable_pi_lambda _ fun j => measurable_pi_apply j.val).prodMk
      (measurable_pi_lambda _ fun j => measurable_pi_apply j.val)
  have hmV : Measurable (fun X : Configuration d N => β*CenteredPairEnergy g r.density X) := by
    have hh := (Finset.measurable_fun_sum Finset.univ fun i _ => (hmU i).comp (hmF i)).div_const 2
    convert hh using 1
    funext X
    dsimp only [Function.comp_apply]
    have hh := hpair X
    change β*CenteredPairEnergy g r.density X = (∑ i : Fin N,U i (F i X))/2
    linarith
  have hbV (X : Configuration d N) : |β*CenteredPairEnergy g r.density X| ≤ (N:ℝ)*Q := by
    have ha := Finset.abs_sum_le_sum_abs (fun i : Fin N => U i (F i X)) Finset.univ
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hbU i (F i X))
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
    have he := congrArg abs (hpair X)
    rw [abs_mul] at he
    rw [abs_of_pos (by norm_num : (0:ℝ)<2)] at he
    have hh : 2*|β*CenteredPairEnergy g r.density X| ≤ (N:ℝ)*Q := by
      rw [← he]
      exact ha.trans hs
    linarith [abs_nonneg (β*CenteredPairEnergy g r.density X)]
  refine ⟨hmV,⟨(N:ℝ)*Q,hbV⟩,?_⟩
  have hs : klDiv (Measure.pi (fun _ : Fin N => μ)) (Measure.pi (fun _ : Fin N => μ)) ≠ ⊤ := by simp
  simpa only [CenteredCanonicalLaw, neg_mul] using (BoundedGibbsRelativeEntropy (Measure.pi (fun _ : Fin N => μ))
    (Measure.pi (fun _ : Fin N => μ)) _ hmV _ hbV hs).2.1
