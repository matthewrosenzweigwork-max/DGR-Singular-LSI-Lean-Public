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

The mathematical Challenge definitions, theorem statements, proof holes, axiom
permissions, and Comparator selections remain unchanged. The administrative
cache-boundary repair below targets generated proof names and leaves the full
fixed-definition comparison in force.

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
output is used to distinguish representation differences from mathematical ones;
the periodic output and official full preflight remain required to confirm the
cache-boundary repair described below.

## Auxiliary-proof cache boundaries

The independent whole-space raw diagnostic at commit prefix `392b80e` compared
69 Challenge-origin or fixed/named declarations: 60 matched and nine differed.
The differences were only auxiliary-proof constant names, reused from earlier
Challenge declarations rather than regenerated under the definition's own name.
For example, `ClosedPhysicalEnergy` referred to earlier Challenge proofs while
its separately compiled Solution definition referred to its own `_proof_1`,
`_proof_2`, and `_proof_3`. This provided a concrete explanation for the same
class of squared-L²-energy correspondence failure in the periodic project.

Pinned Lean's [AuxLemma implementation](https://github.com/leanprover/lean4/blob/v4.35.0-rc2/src/Lean/Meta/Tactic/AuxLemma.lean)
maintains `Lean.Meta.auxLemmasExt`, a cache keyed by proof type and export status.
It is not serialized in `.olean` files. Each original source file therefore
starts with an empty cache, while consecutive copied definitions in the single
Challenge can reuse earlier cached names. Standard `section/end` and local
`Elab.async` options did not reset it in a tiny Lean-only reproduction. A separate
tiny reproduction confirmed that clearing this cache recreates the original
per-file auxiliary names.

Before each of the 20 copied original declarations, Challenge now uses exactly:

```lean
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
```

The command clears only the elaborator's auxiliary-proof cache. It does not add,
remove, replace, or alter any logical constant; it changes no kernel option,
axiom permission, proof, mathematical definition body, or theorem statement. The
two added canonical Lean imports are `public meta import Lean.Meta.Tactic.AuxLemma`
and `public meta import Lean.Elab.Command`, exposing only the administrative
command and cache API to module elaboration. Every reset precedes its object's
docstring, preserving the docstring attachment.

A static comparison with the immediately preceding Challenge confirms identical
text after removing these administrative additions and ignoring blank lines.
The repaired Challenge has 286 physical lines and 17,774 UTF-8 bytes, still within
the preferred 300-line/32-KiB size. No definition body has become a Comparator
hole. This is a candidate compatibility repair supported by the whole-space
raw-data diagnosis and the tiny reproduction; the periodic raw diagnostic and
the exact-commit full Palomar run must establish the actual result. No success
is claimed from source-text matching or the tiny test alone.

The completed periodic inspection at `48542c28390b03bd9b72a350250442732f185306`, run `38945456939`, checked 53 constants: 43 equal and 10 different/missing. Seven fixed root values differ only in references to reused auxiliary proofs; the other reported differences are shifted generated helper declarations. Root raw-expression normalization confirmed identical fixed-root expressions after replacing auxiliary-proof names and formatting. This confirms the same cache-boundary cause as the whole-space diagnostic. It does not replace the next exact-commit full Comparator and kernel run.
