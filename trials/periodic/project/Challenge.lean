module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Tactic
public import Mathlib.Analysis.Convolution

/-!
Compact periodic Riesz statement surface for Palomar.
Definitions are reproduced verbatim from the accepted source (apart from comments).
The three statements preserve all quantifiers, hypotheses, and conclusions.
Only their Challenge proof holes are replaced by the accepted Solution proofs.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set

/-- Ordered configurations of `N` particles on the `d`-dimensional unit additive
torus. Particle labels lie in `Fin N`; each torus coordinate has period one. -/
abbrev Configuration (d N : ℕ) :=
  Fin N → UnitAddTorus (Fin d)

/-- Quotient map from Euclidean coordinates indexed by particle and spatial
coordinate to torus configurations, reducing every real coordinate modulo one. -/
def ConfigurationLift (d N : ℕ)
    (y : EuclideanSpace ℝ (Fin N × Fin d)) : Configuration d N :=
  fun i j => (y (i, j) : AddCircle (1 : ℝ))

/-- Spectral heat kernel on the unit torus, expressed by its real Fourier series
over the integer lattice, with eigenvalues `4π² |k|²` and real cosine characters. -/
noncomputable def HeatKernel (d : ℕ) (t : ℝ) (x : UnitAddTorus (Fin d)) : ℝ :=
  ∑' k : Fin d → ℤ,
    Real.exp (-4 * Real.pi ^ 2 * t * ∑ j, (k j : ℝ) ^ 2) *
      Real.cos (2 * Real.pi * ∑ j,
        (k j : ℝ) * (AddCircle.equivIco (1 : ℝ) 0 (x j) : ℝ))

/-- Periodic Riesz interaction from the Gamma-normalized Mellin integral of the
centered heat kernel at time `t + ε`, with coefficient `a`. The singular diagonal
`ε = 0 ∧ x = 0` is assigned the value zero. The real integral is the totalized
Bochner integral; integrability in the theorem's parameter range is proved in
the Solution rather than assumed in this definition. -/
noncomputable def RieszKernel (d : ℕ) (s a ε : ℝ) (x : UnitAddTorus (Fin d)) : ℝ :=
  if ε = 0 ∧ x = 0 then 0 else
    a / Real.Gamma (((d : ℝ) - s) / 2) *
      ∫ t in Set.Ioi (0 : ℝ),
        Real.rpow t (((d : ℝ) - s) / 2 - 1) * (HeatKernel d (t + ε) x - 1)

/-- A measurable probability density on the unit torus with positive prescribed
lower bound at most one and upper bound at least one. The density bounds hold
almost everywhere with respect to torus volume, and its volume integral is one. -/
structure BoundedBackground (d : ℕ) (lower upper : ℝ) where
  density : UnitAddTorus (Fin d) → ℝ
  measurable : Measurable density
  lower_pos : 0 < lower
  lower_le_one : lower ≤ 1
  one_le_upper : 1 ≤ upper
  bounds : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d))), lower ≤ density x ∧ density x ≤ upper
  mass : ∫ x, density x ∂(MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin d))) = 1

/-- Measure obtained by weighting `μ` by the nonnegative real density
`w / ∫ w dμ`, converted to `ENNReal`. If the real normalizing integral is zero,
real division gives zero and hence the resulting measure is zero. Probability
normalization under the endpoint hypotheses is a property proved in Solution. -/
noncomputable def NormalizedTilt {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (w : Ω → ℝ) : MeasureTheory.Measure Ω :=
  μ.withDensity (fun x => ENNReal.ofReal (w x / ∫ y, w y ∂μ))

/-- Mean-field interaction energy: `1/N` times the sum of the pair kernel over
unordered distinct particle pairs, each counted once using `i < j`. The real
inverse uses Lean's totalized convention at `N = 0`; endpoints require `N ≥ 2`. -/
noncomputable def PairEnergy {d N : ℕ} (g : UnitAddTorus (Fin d) → ℝ)
    (X : Configuration d N) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i : Fin N, ∑ j : Fin N,
    if i < j then g (X i - X j) else 0

/-- Independent-product background weight of a configuration, the product of the
one-particle density at every labeled particle position. -/
noncomputable def ProductDensity {d N : ℕ} (q : UnitAddTorus (Fin d) → ℝ)
    (X : Configuration d N) : ℝ :=
  ∏ i : Fin N, q (X i)

/-- Unnormalized canonical Gibbs weight: the exponential of minus inverse
temperature times the pair energy, multiplied by the product background density. -/
noncomputable def GibbsWeight {d N : ℕ} (g q : UnitAddTorus (Fin d) → ℝ)
    (β : ℝ) (X : Configuration d N) : ℝ :=
  Real.exp (-β * PairEnergy g X) * ProductDensity q X

/-- Canonical Gibbs measure relative to configuration volume, obtained by applying
`NormalizedTilt` to `GibbsWeight`. This includes the full partition-function
normalization rather than taking an unspecified probability law as input. -/
noncomputable def CanonicalLaw {d N : ℕ} (g q : UnitAddTorus (Fin d) → ℝ)
    (β : ℝ) : MeasureTheory.Measure (Configuration d N) :=
  NormalizedTilt (MeasureTheory.volume : MeasureTheory.Measure (Configuration d N)) (GibbsWeight g q β)

open MeasureTheory
/-- Mean potential generated by the background density, namely its torus
convolution with the interaction kernel using real scalar multiplication. -/
noncomputable def BackgroundPotential {d : ℕ}
    (g r : UnitAddTorus (Fin d) → ℝ) (x : UnitAddTorus (Fin d)) : ℝ :=
  MeasureTheory.convolution r g (ContinuousLinearMap.mul ℝ ℝ) volume x

open MeasureTheory
/-- Background pair-interaction mean: the volume integral of the background
potential multiplied by the same background density. -/
noncomputable def BackgroundPairMean {d : ℕ}
    (g r : UnitAddTorus (Fin d) → ℝ) : ℝ :=
  ∫ x, BackgroundPotential g r x * r x ∂volume

open scoped ContDiff
/-- Smooth test functions on configuration space: their pullback by the
Euclidean quotient map is infinitely continuously differentiable. -/
def SmoothCore (d N : ℕ) : Set (Configuration d N → ℝ) :=
  {f | ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin N × Fin d) =>
    f (ConfigurationLift d N y))}

/-- Collision configurations, where at least two distinct particle labels occupy
the same torus point; `i < j` lists each possible colliding pair once. -/
def CollisionSet (d N : ℕ) : Set (Configuration d N) :=
  {X | ∃ i j : Fin N, i < j ∧ X i = X j}

/-- Smooth test functions whose topological support is disjoint from the
collision set. This requires vanishing on a neighborhood of every collision. -/
def CollisionFreeCore (d N : ℕ) : Set (Configuration d N → ℝ) :=
  {f | f ∈ SmoothCore d N ∧ Disjoint (tsupport f) (CollisionSet d N)}

/-- Euclidean coordinate gradient of the lifted function, evaluated at the
canonical representatives of all torus coordinates in `[0,1)`. Each component
is the Fréchet derivative applied to its coordinate unit vector. The definition
uses the totalized Fréchet derivative; its smooth-core properties are proved. -/
noncomputable def CoordinateGradient {d N : ℕ}
    (f : Configuration d N → ℝ) (X : Configuration d N) :
    EuclideanSpace ℝ (Fin N × Fin d) :=
  let y : EuclideanSpace ℝ (Fin N × Fin d) := WithLp.toLp 2
    (fun ij => (AddCircle.equivIco (1 : ℝ) 0 (X ij.1 ij.2) : ℝ))
  WithLp.toLp 2 (fun ij =>
    fderiv ℝ (fun z => f (ConfigurationLift d N z)) y
      (EuclideanSpace.single ij 1))

/-- Closure in the product of scalar and vector `L²(P)` spaces of the graph of
the coordinate gradient on the chosen smooth core. `collisionFree = true` uses
the collision-free core and `false` uses the full smooth core; both the function
and its gradient must belong to `L²(P)` before entering the graph. -/
noncomputable def GradientGraphClosure {d N : ℕ}
    (P : MeasureTheory.Measure (Configuration d N)) (collisionFree : Bool) :
    Set (MeasureTheory.Lp ℝ 2 P ×
      MeasureTheory.Lp (EuclideanSpace ℝ (Fin N × Fin d)) 2 P) :=
  closure {v | ∃ (f : Configuration d N → ℝ)
    (hf : MeasureTheory.MemLp f 2 P)
    (hD : MeasureTheory.MemLp (CoordinateGradient f) 2 P),
    f ∈ (if collisionFree then CollisionFreeCore d N else SmoothCore d N) ∧
    v = (hf.toLp f, hD.toLp (CoordinateGradient f))}

/-- Scalar `L²(P)` elements that have some vector partner in the selected closed
gradient graph. Uniqueness of that partner is a theorem conclusion, not a
condition built into the domain definition. -/
noncomputable def GradientFormDomain {d N : ℕ}
    (P : MeasureTheory.Measure (Configuration d N)) (collisionFree : Bool) :
    Set (MeasureTheory.Lp ℝ 2 P) :=
  {f | ∃ v, (f, v) ∈ GradientGraphClosure P collisionFree}

/-- Dirichlet energy of a closed-gradient vector: its squared norm in the
Euclidean-vector-valued `L²(P)` space. -/
noncomputable def ClosedGradientEnergy {d N : ℕ}
    {P : MeasureTheory.Measure (Configuration d N)}
    (v : MeasureTheory.Lp (EuclideanSpace ℝ (Fin N × Fin d)) 2 P) : ℝ :=
  ‖v‖ ^ 2

/-- Nonnegative extended-valued entropy functional. For real mass `b = ∫ u dμ`,
it is zero when `b = 0`; otherwise it is the lower integral of
`ENNReal.ofReal (u log (u / b) - u + b)`. Endpoint statements apply it to the
nonnegative square of an `L²` function, allowing infinite entropy. -/
noncomputable def ExtendedEntropy {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (u : Ω → ℝ) : ENNReal :=
  let b := ∫ x, u x ∂μ
  if b = 0 then 0 else
    ∫⁻ x, ENNReal.ofReal (u x * Real.log (u x / b) - u x + b) ∂μ

open MeasureTheory ProbabilityTheory Set
theorem UniformFullGradientInequalities (d:ℕ)(hd:2≤d)(s a B l u:ℝ)
    (hs:0≤s)(hsd:s≤(d:ℝ)-2)(ha:0<a)(hl:0<l)(hl1:l≤1)(hu:1≤u) :
    ∃lambdaRate:ℝ,0<lambdaRate ∧
      (∀N:ℕ,2≤N→∀β:ℝ,0≤β→β≤B→∀q:BoundedBackground d l u,∀ε:ℝ,0≤ε→
        let P:=CanonicalLaw (N:=N) (RieszKernel d s a ε) q.density β
        ∀(f:Lp ℝ 2 P)(v:Lp (EuclideanSpace ℝ (Fin N×Fin d)) 2 P),
          (f,v)∈GradientGraphClosure P false→
          variance (f:Configuration d N→ℝ) P≤lambdaRate⁻¹*ClosedGradientEnergy v) ∧
      (s<(d:ℝ)/2→∃ρ:ℝ,0<ρ ∧
        ∀N:ℕ,2≤N→∀β:ℝ,0≤β→β≤B→∀q:BoundedBackground d l u,∀ε:ℝ,0≤ε→
          let P:=CanonicalLaw (N:=N) (RieszKernel d s a ε) q.density β
          ∀(f:Lp ℝ 2 P)(v:Lp (EuclideanSpace ℝ (Fin N×Fin d)) 2 P),
            (f,v)∈GradientGraphClosure P false→
            ExtendedEntropy P (fun X=>f X^2)≤ENNReal.ofReal ((2/ρ)*ClosedGradientEnergy v)) ∧
      (∀N:ℕ,2≤N→∀β:ℝ,0≤β→β≤B→∀q:BoundedBackground d l u,∀ε:ℝ,0≤ε→
        let P:=CanonicalLaw (N:=N) (RieszKernel d s a ε) q.density β
        GradientGraphClosure P false=GradientGraphClosure P true ∧
        GradientFormDomain P false=GradientFormDomain P true ∧
        ∀f:Lp ℝ 2 P,f∈GradientFormDomain P false→
          ∃!v:Lp (EuclideanSpace ℝ (Fin N×Fin d)) 2 P,(f,v)∈GradientGraphClosure P false) := by
  sorry

open MeasureTheory ProbabilityTheory Set
theorem ModulatedFullGradientInequalities (d:ℕ)(hd:2≤d)(s a B l u:ℝ)
    (hs:0≤s)(hsd:s≤(d:ℝ)-2)(ha:0<a)(hl:0<l)(hl1:l≤1)(hu:1≤u) :
    ∃lambdaRate:ℝ,0<lambdaRate ∧
      (∀N:ℕ,2≤N→∀β:ℝ,0≤β→β≤B→∀ε:ℝ,0≤ε→∀r:BoundedBackground d l u,
        let g:=RieszKernel d s a ε
        let h:=BackgroundPotential g r.density
        let J:=BackgroundPairMean g r.density
        let P:=NormalizedTilt (volume:Measure (Configuration d N))
          (fun X=>Real.exp (-β*(PairEnergy g X-(∑i:Fin N,h (X i))+(N:ℝ)*(J/2)))*ProductDensity r.density X)
        ∀(f:Lp ℝ 2 P)(v:Lp (EuclideanSpace ℝ (Fin N×Fin d)) 2 P),
          (f,v)∈GradientGraphClosure P false→
          variance (f:Configuration d N→ℝ) P≤lambdaRate⁻¹*ClosedGradientEnergy v) ∧
      (s<(d:ℝ)/2→∃ρ:ℝ,0<ρ ∧
        ∀N:ℕ,2≤N→∀β:ℝ,0≤β→β≤B→∀ε:ℝ,0≤ε→∀r:BoundedBackground d l u,
          let g:=RieszKernel d s a ε
          let h:=BackgroundPotential g r.density
          let J:=BackgroundPairMean g r.density
          let P:=NormalizedTilt (volume:Measure (Configuration d N))
            (fun X=>Real.exp (-β*(PairEnergy g X-(∑i:Fin N,h (X i))+(N:ℝ)*(J/2)))*ProductDensity r.density X)
          ∀(f:Lp ℝ 2 P)(v:Lp (EuclideanSpace ℝ (Fin N×Fin d)) 2 P),
            (f,v)∈GradientGraphClosure P false→
            ExtendedEntropy P (fun X=>f X^2)≤ENNReal.ofReal ((2/ρ)*ClosedGradientEnergy v)) ∧
      (∀N:ℕ,2≤N→∀β:ℝ,0≤β→β≤B→∀ε:ℝ,0≤ε→∀r:BoundedBackground d l u,
        let g:=RieszKernel d s a ε
        let h:=BackgroundPotential g r.density
        let J:=BackgroundPairMean g r.density
        let P:=NormalizedTilt (volume:Measure (Configuration d N))
          (fun X=>Real.exp (-β*(PairEnergy g X-(∑i:Fin N,h (X i))+(N:ℝ)*(J/2)))*ProductDensity r.density X)
        GradientGraphClosure P false=GradientGraphClosure P true ∧
        GradientFormDomain P false=GradientFormDomain P true ∧
        ∀f:Lp ℝ 2 P,f∈GradientFormDomain P false→
          ∃!v:Lp (EuclideanSpace ℝ (Fin N×Fin d)) 2 P,(f,v)∈GradientGraphClosure P false) := by
  sorry

open MeasureTheory ProbabilityTheory Set
theorem ExternalPotentialFullGradientInequalities (d : ℕ) (hd : 2≤d) (s a B L : ℝ)
    (hs : 0≤s) (hsd : s≤(d:ℝ)-2) (ha : 0<a) (hL : 0≤L) :
    (∃ rate : ℝ, 0 < rate ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ β : ℝ, 0 ≤ β → β ≤ B → ∀ ε : ℝ, 0 ≤ ε →
      ∀ A : ℝ, ∀ V : UnitAddTorus (Fin d) → ℝ, Measurable V →
      (∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), A ≤ V x ∧ V x ≤ A+L) →
      let P := NormalizedTilt (volume : Measure (Configuration d N))
        (fun X => Real.exp (-β*(∑ i : Fin N, V (X i))-β*PairEnergy (RieszKernel d s a ε) X))
      GradientGraphClosure P false = GradientGraphClosure P true ∧
      GradientFormDomain P false = GradientFormDomain P true ∧
      (∀ f : Lp ℝ 2 P, f ∈ GradientFormDomain P false →
        ∃! v : Lp (EuclideanSpace ℝ (Fin N×Fin d)) 2 P,
          (f,v) ∈ GradientGraphClosure P false) ∧
      (∀ (f : Lp ℝ 2 P) (v : Lp (EuclideanSpace ℝ (Fin N×Fin d)) 2 P),
        (f,v) ∈ GradientGraphClosure P false →
        variance (f : Configuration d N → ℝ) P ≤ rate⁻¹*ClosedGradientEnergy v)) ∧
    (s<(d:ℝ)/2 → ∃ rate : ℝ, 0 < rate ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ β : ℝ, 0 ≤ β → β ≤ B → ∀ ε : ℝ, 0 ≤ ε →
      ∀ A : ℝ, ∀ V : UnitAddTorus (Fin d) → ℝ, Measurable V →
      (∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), A ≤ V x ∧ V x ≤ A+L) →
      let P := NormalizedTilt (volume : Measure (Configuration d N))
        (fun X => Real.exp (-β*(∑ i : Fin N, V (X i))-β*PairEnergy (RieszKernel d s a ε) X))
      ∀ (f : Lp ℝ 2 P) (v : Lp (EuclideanSpace ℝ (Fin N×Fin d)) 2 P),
        (f,v) ∈ GradientGraphClosure P false →
        ExtendedEntropy P (fun X => f X^2) ≤ ENNReal.ofReal ((2/rate)*ClosedGradientEnergy v)) := by
  sorry
