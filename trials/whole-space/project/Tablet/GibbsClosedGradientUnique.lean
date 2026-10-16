import Tablet.WeightedGradientClosability
import Tablet.GibbsLocalDensityBounds
import Tablet.CollisionNull
import Tablet.ClosedGradientGraph
open MeasureTheory Filter Set
open scoped Topology ContDiff

-- [TABLET NODE: GibbsClosedGradientUnique]
theorem GibbsClosedGradientUnique {d N : ℕ} (hd : 0 < d) (V b : OneParticle d → ℝ)
    (κ L : ℝ) (hκ : 0 < κ) (hV : PotentialBounds d κ V)
    (hb : BoundedMultiplier d L b) (s coupling ε : ℝ)
    (hs : 0 < s) (hc : 0 ≤ coupling) (hε : 0 ≤ ε)
    (f : Lp ℝ 2 (GibbsLaw (N := N) (ReferenceLaw V b) s coupling ε))
    (v w : Lp (ParticleConfig d N) 2 (GibbsLaw (N := N) (ReferenceLaw V b) s coupling ε))
    (hv : (f, v) ∈ ClosedGradientGraph (GibbsLaw (N := N) (ReferenceLaw V b) s coupling ε))
    (hw : (f, w) ∈ ClosedGradientGraph (GibbsLaw (N := N) (ReferenceLaw V b) s coupling ε)) :
    v = w := by
-- BODY
  classical
  let r := GibbsLebesgueDensity (N := N) V b s coupling ε
  let U := (CollisionSet d N)ᶜ
  have hlocal : ∀ K : Set (ParticleConfig d N), IsCompact K → K ⊆ U →
      ∃ m : ℝ, 0 < m ∧ ∀ᵐ x ∂(volume : Measure (ParticleConfig d N)), x ∈ K → m ≤ r x := by
    intro K hK hKU
    obtain ⟨m, hm, hbound⟩ := (GibbsLocalDensityBounds hd V b κ L hκ hV hb s coupling ε hs hc hε).2 K hK hKU
    exact ⟨m, hm, Eventually.of_forall (fun X hX => hbound X hX)⟩
  have hU : IsOpen U := by
    change IsOpen (CollisionSet d N)ᶜ
    apply isOpen_compl_iff.mpr
    simp only [CollisionSet, ofPred_exists]
    apply isClosed_iUnion_of_finite
    intro i
    apply isClosed_iUnion_of_finite
    intro j
    by_cases hij : i < j
    · simp only [hij, true_and]
      have hp (k : Fin N) : Continuous (fun X : ParticleConfig d N => ParticlePosition X k) := by
        unfold ParticlePosition
        fun_prop
      exact isClosed_eq (hp i) (hp j)
    · simp only [hij, false_and, ofPred_false]
      exact isClosed_empty
  have hfull : ∀ᵐ x ∂(volume.withDensity (fun y => ENNReal.ofReal (r y))), x ∈ U := by
    rw [ae_iff]
    simpa only [U, Set.mem_compl_iff, not_not, Set.ofPred_mem_eq] using
      (withDensity_absolutelyContinuous volume (fun y => ENNReal.ofReal (r y))) (CollisionNull d N hd)
  have hlaw := GibbsRawDensity (N := N) hd V b κ L hκ hV hb s coupling ε hs hc hε
  generalize hP : GibbsLaw (N := N) (ReferenceLaw V b) s coupling ε = P at f v w hv hw ⊢
  have he : P = volume.withDensity (fun X => ENNReal.ofReal (r X)) := hP.symm.trans hlaw
  cases he
  change (f, v) ∈ closure (SmoothGradientCore (volume.withDensity (fun X => ENNReal.ofReal (r X)))) at hv
  change (f, w) ∈ closure (SmoothGradientCore (volume.withDensity (fun X => ENNReal.ofReal (r X)))) at hw
  have EuclideanGradient_sub (g k : ParticleConfig d N → ℝ)
      (hgs : ContDiff ℝ ∞ g) (hks : ContDiff ℝ ∞ k) :
      EuclideanGradient (fun X => g X - k X) =
        fun X => EuclideanGradient g X - EuclideanGradient k X := by
    funext X
    rw [(EuclideanDerivativeCoordinates _ X).1, (EuclideanDerivativeCoordinates g X).1,
      (EuclideanDerivativeCoordinates k X).1]
    ext j
    change fderiv ℝ (g - k) X (EuclideanSpace.basisFun (Fin N × Fin d) ℝ j) = _
    rw [fderiv_sub ((hgs.differentiable (by simp)).differentiableAt)
      ((hks.differentiable (by simp)).differentiableAt)]
    rfl
  rw [mem_closure_iff_seq_limit] at hv hw
  obtain ⟨x,hx,hxt⟩ := hv
  obtain ⟨y,hy,hyt⟩ := hw
  have hx' : ∀ n, ∃ (g : ParticleConfig d N → ℝ), ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      ∃ hg : MemLp g 2 (volume.withDensity (fun x => ENNReal.ofReal (r x))),
      ∃ hD : MemLp (EuclideanGradient g) 2 (volume.withDensity (fun x => ENNReal.ofReal (r x))),
        x n = (hg.toLp g,hD.toLp (EuclideanGradient g)) := by simpa [SmoothGradientCore] using hx
  have hy' : ∀ n, ∃ (g : ParticleConfig d N → ℝ), ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      ∃ hg : MemLp g 2 (volume.withDensity (fun x => ENNReal.ofReal (r x))),
      ∃ hD : MemLp (EuclideanGradient g) 2 (volume.withDensity (fun x => ENNReal.ofReal (r x))),
        y n = (hg.toLp g,hD.toLp (EuclideanGradient g)) := by simpa [SmoothGradientCore] using hy
  choose g hgs hgc hg hD hxe using hx'
  choose k hks hkc hk hE hye using hy'
  let z := fun n X => g n X - k n X
  have hzs : ∀ n, ContDiff ℝ ∞ (z n) := fun n => (hgs n).sub (hks n)
  have hz : ∀ n, MemLp (z n) 2 (volume.withDensity (fun x => ENNReal.ofReal (r x))) := fun n => (hg n).sub (hk n)
  have hDz : ∀ n, MemLp (EuclideanGradient (z n)) 2
      (volume.withDensity (fun x => ENNReal.ofReal (r x))) := by
    intro n
    rw [show EuclideanGradient (z n) =
      fun X => EuclideanGradient (g n) X - EuclideanGradient (k n) X
      from EuclideanGradient_sub (g n) (k n) (hgs n) (hks n)]
    exact (hD n).sub (hE n)
  have hfun : Tendsto (fun n => (hz n).toLp (z n)) atTop (𝓝 0) := by
    have h := hxt.fst_nhds.sub hyt.fst_nhds
    simp only [sub_self] at h
    convert h using 1
    funext n
    rw [hxe,hye]
    simp only [← MemLp.toLp_sub]
    apply MemLp.toLp_congr
    exact Eventually.of_forall (fun X => rfl)
  have hgrad : Tendsto (fun n => (hDz n).toLp (EuclideanGradient (z n))) atTop (𝓝 (v-w)) := by
    have h := hxt.snd_nhds.sub hyt.snd_nhds
    convert h using 1
    funext n
    rw [hxe,hye]
    simp only [← MemLp.toLp_sub]
    apply MemLp.toLp_congr
    exact Eventually.of_forall (fun X => congrFun (EuclideanGradient_sub (g n) (k n) (hgs n) (hks n)) X)
  have hzw := WeightedGradientClosability r U hU hfull hlocal z hzs hz hDz (v-w) hfun hgrad
  exact sub_eq_zero.mp hzw
