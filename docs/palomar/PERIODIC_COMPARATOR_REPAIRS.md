# Periodic Comparator investigation

## Actual full-preflight result

Full preflight [run 38942746877](https://github.com/matthewrosenzweigwork-max/DGR-Singular-LSI-Lean-Public/actions/runs/38942746877),
at migration commit prefix `4d4fa1c`, compiled the periodic `Solution` and then
failed at Comparator with:

```text
Const does not match between challenge and target 'ClosedGradientEnergy'
```

This is not a successful Palomar verification. It is a strict declaration
correspondence failure after successful Lean source compilation. The report does
not identify which elaborated field differs or establish the reason for it.

## Mathematical reconstruction retained

The periodic Challenge reproduces the 20 concrete project objects needed by the
three selected endpoint families: uniform canonical backgrounds, modulated
backgrounds, and bounded external potentials. This includes the actual torus
heat/Riesz kernel, normalized particle laws, coordinate gradients, smooth and
collision-free cores, product-L² graph closure, form domain, squared L² gradient
energy, and extended entropy. Its complete statements and primitive definition
text were compared against the accepted snapshot
`933ab9a859aaa54a26246a4aeac1d92972c20c2d`; the mathematical design is recorded in
`PERIODIC_CHALLENGE_DESIGN.md`.

`ClosedGradientEnergy` is the squared L² norm of the gradient vector. The
Challenge and Solution must agree on this exact declaration and its dependency
closure; its body is not configured as a Comparator hole. Source-text equality
alone cannot establish equality of all elaborated constant fields.

No Challenge definition, theorem statement, proof, axiom permission, or Comparator
selection has been changed in response to this failure. We first inspect the
actual compiled data so any eventual repair can be limited to the identified
representation difference and preserve mathematical meaning.

## Read-only compiled-constant diagnostic

The shared `scripts/compare_whole_space_constants.lean` now accepts a third
positional argument `periodic`. From the compiled periodic project:

```sh
lake env lean --run ../../../scripts/compare_whole_space_constants.lean Challenge Solution periodic
```

The default component remains `whole-space`, with its original 26 fixed roots
and three selected theorems. The periodic selection has 20 fixed roots and the
three theorem names in the periodic Comparator configuration. In both modes,
the script also enumerates every constant originating in the compiled Challenge
module, including generated declarations; hand-listed roots are not the extent
of the inspection.

Challenge and Solution are imported into separate environments. The diagnostic
compares complete constant data, except that configured theorem proof values are
allowed to differ as in Lake's named-theorem comparison. JSON Lines report
constants, differing fields (including types, values, universe parameters,
reducibility hints and safety), and totals. The script does not modify either
environment or any source and does not replace the official Comparator. Raw
output remains required before choosing a correspondence repair.
