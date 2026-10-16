# Periodic Challenge design

`trials/periodic/project/Challenge.lean` is a standalone statement surface for
Palomar, with only canonical Mathlib imports. It contains **279 physical lines**
and **16,133 UTF-8 bytes**, below both the preferred 300-line/32-KiB size and the
hard 1,000-line/100-KiB size.

## Scope and correspondence

The selected theorem names are the existing public endpoints:

- `UniformFullGradientInequalities`
- `ModulatedFullGradientInequalities`
- `ExternalPotentialFullGradientInequalities`

Each complete statement was copied without changing its hypotheses, binder order,
quantifiers, rates, constants, law, or conclusions from the accepted joint
snapshot `933ab9a859aaa54a26246a4aeac1d92972c20c2d`. This includes the restrictions
`2 ≤ d`, `0 ≤ s ≤ d - 2`, positive kernel coefficient, the finite temperature
cap, all particle numbers `N ≥ 2`, every regularization `ε ≥ 0`, and the additional
`s < d/2` condition for LSI. The background version retains its full measurable,
normalized, upper/lower bounded background structure. The external-potential
version retains measurability, arbitrary additive baseline, and almost-everywhere
oscillation bounds. No new analytic assumption is introduced.

All three families include the accepted closed-gradient Poincaré/LSI statements;
their original placement of core equality, form-domain equality and unique
closed-gradient clauses is preserved. This is a periodic result and makes no
whole-space Riesz LSI claim.

## Full primitive definitions

The Challenge reproduces all 20 project definitions reached by these theorem
statements, including the Fourier-series heat kernel, Gamma-weighted Riesz
integral, the diagonal value convention, the mean-field pair energy, normalized
Gibbs law, background convolution and pair mean, Euclidean lift and coordinate
derivative, smooth and collision-free cores, topological graph closure, its form
domain, squared L² gradient norm, and extended entropy. The definitions are
verbatim accepted declaration text apart from comments. Their names are unchanged
so Comparator can compare the full declaration closure against the source proof.
There are no abstract surrogate physics laws or freely variable energy forms.

`Solution.lean` public-imports the three existing endpoint modules and adds no
mathematical declarations. It does not import Challenge. `comparator.json` lists
all three theorems, sets `definition_names` to the empty list, enables NanoDa, and
permits only `propext`, `Quot.sound`, and `Classical.choice`. Thus no definition
body is a Comparator hole. The only `sorry` occurrences are the three named
Challenge theorem proof holes; Solution's proofs remain the accepted proofs.

## Validation performed

A static comparison against Git object
`933ab9a859aaa54a26246a4aeac1d92972c20c2d` confirmed all 20 definition declarations
and all three complete theorem statement strings occur unchanged in Challenge.
The Challenge import list was checked to contain only `Mathlib.*` modules. JSON
parsing and the exact selected declaration list passed. No local Lean compilation
or kernel verification was run during this preparation.

The project Lake configuration must expose `Challenge` and `Solution` as build
roots, and Linux CI must compile and run the pinned full Palomar workflow on the
exact submitted commit before any registry claim. Lean elaboration, Comparator
declaration equality, axiom closure, and external-kernel verification remain
CI obligations. Importing a larger set of canonical Mathlib modules changes no
intended project definitions, but only actual Comparator evidence establishes the
elaborated declaration correspondence.

## Mathematical descriptions

Each of the 20 reproduced primitive definitions has a docstring describing its
ordinary mathematical role. These explicitly describe the zero singular-diagonal
convention, totalized normalization and derivative conventions, mean-field pair
counting, canonical coordinate representatives, the distinction between the two
smooth cores, product-L² graph closure and form domains, and extended entropy.
Only comments were added; all definition bodies and endpoint statements remain
the accepted strings.
