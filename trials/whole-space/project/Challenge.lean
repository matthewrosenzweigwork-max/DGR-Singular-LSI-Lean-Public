module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Strong
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.Order.Compact
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/- Whole-space Riesz Poincare challenge.
The definitions and three complete theorem statements below are reproduced from
accepted snapshot 933ab9a859aaa54a26246a4aeac1d92972c20c2d, with only the module
interface migration. Each theorem is a comparator hole; all definitions are fixed.
The Solution imports the accepted proofs and does not import this Challenge. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ContDiff ENNReal
noncomputable section

/-- The one-particle space ℝ^d, realized as the real Euclidean space indexed by `Fin d`. -/
abbrev OneParticle (d : ℕ) :=
  EuclideanSpace ℝ (Fin d)

/-- The N-particle configuration space (ℝ^d)^N with its Euclidean product norm,
indexed by particle-coordinate pairs in `Fin N × Fin d`. -/
abbrev ParticleConfig (d N : ℕ) :=
  EuclideanSpace ℝ (Fin N × Fin d)

/-- The Lebesgue integral of the one-particle density `b(x) exp(-V(x))`.
Its positivity and finiteness are established under the potential/multiplier hypotheses. -/
noncomputable def ReferencePartition {d : ℕ} (V b : OneParticle d → ℝ) : ℝ :=
  ∫ x, b x * Real.exp (-V x)

/-- The measure with Lebesgue density `ofReal (Z⁻¹ b(x) exp(-V(x)))`, where
`Z = ReferencePartition V b`. The definition is total; the endpoint hypotheses ensure normalization. -/
noncomputable def ReferenceLaw {d : ℕ} (V b : OneParticle d → ℝ) :
    MeasureTheory.Measure (OneParticle d) :=
  MeasureTheory.volume.withDensity (fun x =>
    ENNReal.ofReal ((ReferencePartition V b)⁻¹ * (b x * Real.exp (-V x))))

/-- The image of the N-fold independent product of μ under row flattening
into the Euclidean configuration space. -/
noncomputable def ConfigurationReference (d N : ℕ)
    (μ : MeasureTheory.Measure (OneParticle d)) :
    MeasureTheory.Measure (ParticleConfig d N) :=
  MeasureTheory.Measure.map
    (fun Y : Fin N → OneParticle d => WithLp.toLp 2 (fun ik : Fin N × Fin d =>
      Y ik.1 ik.2)) (MeasureTheory.Measure.pi (fun _ : Fin N => μ))

/-- The Riesz interaction `‖x‖^(-s)/s` at zero cutoff and the softened interaction
`(‖x‖² + ε²)^(-s/2)/s` otherwise. Real powers use Mathlib’s total convention at zero. -/
noncomputable def RieszKernel {d : ℕ} (s ε : ℝ) (x : OneParticle d) : ℝ :=
  if ε = 0 then ‖x‖ ^ (-s) / s else (‖x‖ ^ 2 + ε ^ 2) ^ (-s / 2) / s

/-- The d-dimensional position of particle i, extracted from a configuration X. -/
noncomputable def ParticlePosition {d N : ℕ} (X : ParticleConfig d N)
    (i : Fin N) : OneParticle d :=
  WithLp.toLp 2 (fun k => X (i, k))

/-- The mean-field interaction energy `(coupling/N) ∑_{i<j} RieszKernel s ε (Xᵢ-Xⱼ)`;
each unordered pair is counted once. -/
noncomputable def PairInteraction {d N : ℕ} (s coupling ε : ℝ)
    (X : ParticleConfig d N) : ℝ :=
  (coupling / (N : ℝ)) * ∑ i : Fin N, ∑ j : Fin N,
    if i < j then RieszKernel s ε (ParticlePosition X i - ParticlePosition X j) else 0

/-- The configurations containing two distinct particle indices with the same position. -/
def CollisionSet (d N : ℕ) : Set (ParticleConfig d N) :=
  {X | ∃ i j : Fin N, i < j ∧ ParticlePosition X i = ParticlePosition X j}

/-- The Boltzmann interaction weight: one at zero coupling, zero on collisions
when ε = 0 and coupling is nonzero, and `exp(-PairInteraction)` in every other case. -/
noncomputable def InteractionWeight {d N : ℕ} (s coupling ε : ℝ)
    (X : ParticleConfig d N) : ℝ := by
  classical
  exact if coupling = 0 then 1 else
    if ε = 0 ∧ X ∈ CollisionSet d N then 0 else Real.exp (-PairInteraction s coupling ε X)

/-- The integral of the interaction weight against the independent configuration
reference law. This is the N-particle Gibbs normalizing constant. -/
noncomputable def GibbsPartition {d N : ℕ}
    (μ : MeasureTheory.Measure (OneParticle d)) (s coupling ε : ℝ) : ℝ :=
  ∫ X, InteractionWeight s coupling ε X ∂ConfigurationReference d N μ

/-- The reference configuration measure tilted by the density
`ofReal (GibbsPartition⁻¹ * InteractionWeight)`. Probability normalization follows from the hypotheses. -/
noncomputable def GibbsLaw {d N : ℕ}
    (μ : MeasureTheory.Measure (OneParticle d)) (s coupling ε : ℝ) :
    MeasureTheory.Measure (ParticleConfig d N) :=
  (ConfigurationReference d N μ).withDensity (fun X =>
    ENNReal.ofReal ((GibbsPartition (N := N) μ s coupling ε)⁻¹ * InteractionWeight s coupling ε X))

/-- Mathlib’s variance of f under P (the integral of the squared deviation from its mean
when f is square-integrable under a probability law), using Mathlib’s total definition. -/
noncomputable def LawVariance {α : Type*} [MeasurableSpace α]
    (P : MeasureTheory.Measure α) (f : α → ℝ) : ℝ :=
  ProbabilityTheory.variance f P

/-- Mathlib’s real Euclidean gradient of f at x, using its total derivative convention. -/
noncomputable def EuclideanGradient {ι : Type*} [Fintype ι]
    (f : EuclideanSpace ℝ ι → ℝ) (x : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι :=
  gradient f x

/-- The Dirichlet energy `∫ ‖∇f‖² dP` of a real function on configuration space. -/
noncomputable def PhysicalEnergy {d N : ℕ}
    (P : MeasureTheory.Measure (ParticleConfig d N)) (f : ParticleConfig d N → ℝ) : ℝ :=
  ∫ X, ‖EuclideanGradient f X‖ ^ 2 ∂P

/-- Pairs `(f, ∇f)` in the product of scalar and configuration-valued L²(P) spaces,
represented by smooth compactly supported f with both f and its gradient in L²(P). -/
def SmoothGradientCore {d N : ℕ}
    (P : MeasureTheory.Measure (ParticleConfig d N)) :
    Set (MeasureTheory.Lp ℝ 2 P × MeasureTheory.Lp (ParticleConfig d N) 2 P) :=
  {q | ∃ f : ParticleConfig d N → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    ∃ hf : MeasureTheory.MemLp f 2 P,
    ∃ hg : MeasureTheory.MemLp (EuclideanGradient f) 2 P,
      q = (hf.toLp f, hg.toLp (EuclideanGradient f))}

/-- The closure of the smooth gradient core in `L²(P; ℝ) × L²(P; configuration)`.
Its elements pair a scalar L² function with a gradient obtained by graph closure. -/
def ClosedGradientGraph {d N : ℕ}
    (P : MeasureTheory.Measure (ParticleConfig d N)) :
    Set (MeasureTheory.Lp ℝ 2 P × MeasureTheory.Lp (ParticleConfig d N) 2 P) :=
  closure (SmoothGradientCore P)

/-- The squared L²(P) norm of the gradient component of q. On the closed gradient
graph this is the closed physical Dirichlet energy of the pair. -/
noncomputable def ClosedPhysicalEnergy {d N : ℕ}
    {P : MeasureTheory.Measure (ParticleConfig d N)}
    (q : MeasureTheory.Lp ℝ 2 P × MeasureTheory.Lp (ParticleConfig d N) 2 P) : ℝ :=
  ‖q.2‖ ^ 2

/-- A measurable multiplier b bounded everywhere between positive constants
`bmin ≤ bmax` with contrast `bmax/bmin ≤ L`. -/
structure BoundedMultiplier (d : ℕ) (L : ℝ) (b : OneParticle d → ℝ) : Prop where
  measurable : Measurable b
  bounds : ∃ bmin bmax : ℝ, 0 < bmin ∧ bmin ≤ bmax ∧
    bmax / bmin ≤ L ∧ ∀ x, bmin ≤ b x ∧ b x ≤ bmax

/-- The bilinear Hessian form obtained by applying the second Fréchet derivative
of V at x to the ordered directions u and v. -/
noncomputable def EuclideanHessian {ι : Type*} [Fintype ι]
    (V : EuclideanSpace ℝ ι → ℝ) (x u v : EuclideanSpace ℝ ι) : ℝ :=
  (fderiv ℝ (fderiv ℝ V) x u) v

/-- Mathlib’s Euclidean Laplacian of V at x, the trace of its Hessian when V is C². -/
noncomputable def EuclideanLaplacian {ι : Type*} [Fintype ι]
    (V : EuclideanSpace ℝ ι → ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  Laplacian.laplacian V x

/-- A C² potential whose Hessian satisfies `κ ‖u‖² ≤ Hess V(x)[u,u]`
at every point and direction. Positive κ is imposed separately by the endpoints. -/
structure PotentialBounds (d : ℕ) (κ : ℝ) (V : OneParticle d → ℝ) : Prop where
  regularity : ContDiff ℝ 2 V
  lower : ∀ x u, κ * ‖u‖ ^ 2 ≤ EuclideanHessian V x u u

/-- A potential with the C² lower Hessian bound κ and the upper quadratic-form
bound `Hess V(x)[u,u] ≤ K ‖u‖²` for every point and direction. -/
structure TwoSidedPotential (d : ℕ) (κ K : ℝ)
    (V : OneParticle d → ℝ) : Prop extends PotentialBounds d κ V where
  upper : ∀ x u, EuclideanHessian V x u u ≤ K * ‖u‖ ^ 2

/-- The growth exponent `2/(s+1)` used to compare the Laplacian with the force magnitude. -/
noncomputable def ForceExponent (s : ℝ) : ℝ :=
  2 / (s + 1)

/-- The translated potential `x ↦ V(x+m)-V(m)` and multiplier `x ↦ b(x+m)`,
so that the potential is centered at m and has zero value there. -/
def ShiftedReference {d : ℕ} (V b : OneParticle d → ℝ)
    (m : OneParticle d) : (OneParticle d → ℝ) × (OneParticle d → ℝ) :=
  (fun x => V (x + m) - V m, fun x => b (x + m))

/-- A C² potential with lower Hessian bound κ, a global minimizer m with
`V(x+m)-V(m) ≤ M(R)` whenever `R > 0` and `‖x‖ ≤ R`, and the global bounds
`ΔV(x) ≤ a ‖∇V(x)‖^(2/(s+1)) + C(a)` for every `a > 0` and x. -/
structure GrowthClassPotential (d : ℕ) (s κ : ℝ) (M C : ℝ → ℝ)
    (V : OneParticle d → ℝ) : Prop extends PotentialBounds d κ V where
  localData : ∃ m : OneParticle d, (∀ x, V m ≤ V x) ∧
    ∀ R : ℝ, 0 < R → ∀ x : OneParticle d, ‖x‖ ≤ R →
      (ShiftedReference V (fun _ => 1) m).1 x ≤ M R
  growth : ∀ a : ℝ, 0 < a → ∀ x : OneParticle d,
    EuclideanLaplacian V x ≤ a * ‖EuclideanGradient V x‖ ^ ForceExponent s + C a

theorem BoundedHessianAllCutoffsClosedPI (d : ℕ) (hd : 3 ≤ d) (s B κ K L : ℝ)
    (hs : 0 < s) (hsd : s ≤ (d:ℝ)-2) (hB : 0 ≤ B)
    (hκ : 0 < κ) (hκK : κ ≤ K) (hL : 1 ≤ L) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ V : OneParticle d → ℝ, TwoSidedPotential d κ K V →
      ∀ b : OneParticle d → ℝ, BoundedMultiplier d L b →
      ∀ N : ℕ, 2 ≤ N → ∀ coupling ε : ℝ,
        0 ≤ coupling → coupling ≤ B → 0 ≤ ε →
      ∀ q ∈ ClosedGradientGraph (GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε),
        ρ*LawVariance (GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε) q.1 ≤
          ClosedPhysicalEnergy q := by
  sorry

theorem GrowthClassPositiveCutoffClosedPI (d : ℕ) (hd : 3 ≤ d) (s B : ℝ)
    (hs : 0 < s) (hsd : s ≤ (d:ℝ)-2) (hB : 0 ≤ B) :
    (∀ (κ L : ℝ), 0 < κ → 1 ≤ L → ∀ (Ca Mloc : ℝ → ℝ),
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ V : OneParticle d → ℝ,
      GrowthClassPotential d s κ Mloc Ca V →
      ∀ b : OneParticle d → ℝ, BoundedMultiplier d L b →
      ∀ N : ℕ, 2 ≤ N → ∀ coupling ε : ℝ,
        0 ≤ coupling → coupling ≤ B → 0 < ε →
      ∀ q ∈ ClosedGradientGraph (GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε),
        ρ*LawVariance (GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε) q.1 ≤
          ClosedPhysicalEnergy q) ∧
    (∀ (κ L : ℝ), 0 < κ → 1 ≤ L →
    ∀ (V : OneParticle d → ℝ) (hV : ContDiff ℝ 2 V)
    (hH : ∀ x u, κ*‖u‖^2 ≤ EuclideanHessian V x u u)
    (hGrowth : ∀ a : ℝ, 0 < a → ∃ C : ℝ, ∀ x,
      EuclideanLaplacian V x ≤ a*‖EuclideanGradient V x‖^(2/(s+1))+C),
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ b : OneParticle d → ℝ, BoundedMultiplier d L b →
      ∀ coupling ε : ℝ, 0 ≤ coupling → coupling ≤ B → 0 < ε →
      ∀ q ∈ ClosedGradientGraph (GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε),
        ρ*LawVariance (GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε) q.1 ≤
          ClosedPhysicalEnergy q) ∧
    (    ∃ ρ : ℝ, 0 < ρ ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ coupling ε : ℝ, 0 ≤ coupling → coupling ≤ B → 0 < ε →
      ∀ q ∈ ClosedGradientGraph
        (GibbsLaw (N:=N) (ProbabilityTheory.stdGaussian (OneParticle d)) s coupling ε),
        ρ*LawVariance
          (GibbsLaw (N:=N) (ProbabilityTheory.stdGaussian (OneParticle d)) s coupling ε) q.1 ≤
            ClosedPhysicalEnergy q) := by
  sorry

theorem GrowthClassZeroCutoffClosedPI (d : ℕ) (hd : 3 ≤ d) (s B : ℝ)
    (hs : 0 < s) (hsd : s ≤ (d:ℝ)-2) (hB : 0 ≤ B) :
    (∀ (κ L : ℝ), 0 < κ → 1 ≤ L → ∀ (Ca Mloc : ℝ → ℝ),
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ V : OneParticle d → ℝ,
      GrowthClassPotential d s κ Mloc Ca V →
      ∀ b : OneParticle d → ℝ, BoundedMultiplier d L b →
      ∀ N : ℕ, 2 ≤ N → ∀ coupling ε : ℝ,
        0 ≤ coupling → coupling ≤ B → ε = 0 →
      ∀ q ∈ ClosedGradientGraph (GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε),
        ρ*LawVariance (GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε) q.1 ≤
          ClosedPhysicalEnergy q) ∧
    (∀ (κ L : ℝ), 0 < κ → 1 ≤ L →
    ∀ (V : OneParticle d → ℝ) (hV : ContDiff ℝ 2 V)
    (hH : ∀ x u, κ*‖u‖^2 ≤ EuclideanHessian V x u u)
    (hGrowth : ∀ a : ℝ, 0 < a → ∃ C : ℝ, ∀ x,
      EuclideanLaplacian V x ≤ a*‖EuclideanGradient V x‖^(2/(s+1))+C),
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ b : OneParticle d → ℝ, BoundedMultiplier d L b →
      ∀ coupling ε : ℝ, 0 ≤ coupling → coupling ≤ B → ε = 0 →
      ∀ q ∈ ClosedGradientGraph (GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε),
        ρ*LawVariance (GibbsLaw (N:=N) (ReferenceLaw V b) s coupling ε) q.1 ≤
          ClosedPhysicalEnergy q) ∧
    (    ∃ ρ : ℝ, 0 < ρ ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ coupling ε : ℝ, 0 ≤ coupling → coupling ≤ B → ε = 0 →
      ∀ q ∈ ClosedGradientGraph
        (GibbsLaw (N:=N) (ProbabilityTheory.stdGaussian (OneParticle d)) s coupling ε),
        ρ*LawVariance
          (GibbsLaw (N:=N) (ProbabilityTheory.stdGaussian (OneParticle d)) s coupling ε) q.1 ≤
            ClosedPhysicalEnergy q) := by
  sorry
