module

import Lean

/-! Read-only diagnostic for strict Challenge/Solution constant correspondence.
Run from either built project with:
  lake env lean --run ../../../scripts/compare_whole_space_constants.lean
Optional positional arguments replace the Challenge and Solution module names.
The third positional argument selects `whole-space` (default) or `periodic`:
  lake env lean --run ../../../scripts/compare_whole_space_constants.lean Challenge Solution periodic
Output is JSON Lines; mismatches are findings, not a nonzero diagnostic exit.
This imports the modules into separate environments and never mixes their
identically named declarations into one environment. No declarations are changed.
-/

open Lean

private def wholeSpaceFixedNames : Array Name := #[
  `OneParticle, `ParticleConfig, `ReferencePartition, `ReferenceLaw,
  `ConfigurationReference, `RieszKernel, `ParticlePosition, `PairInteraction,
  `CollisionSet, `InteractionWeight, `GibbsPartition, `GibbsLaw, `LawVariance,
  `EuclideanGradient, `PhysicalEnergy, `SmoothGradientCore, `ClosedGradientGraph,
  `ClosedPhysicalEnergy, `BoundedMultiplier, `EuclideanHessian,
  `EuclideanLaplacian, `PotentialBounds, `TwoSidedPotential, `ForceExponent,
  `ShiftedReference, `GrowthClassPotential]

private def wholeSpaceTheoremNames : Array Name := #[
  `BoundedHessianAllCutoffsClosedPI, `GrowthClassPositiveCutoffClosedPI,
  `GrowthClassZeroCutoffClosedPI]

private def periodicFixedNames : Array Name := #[
  `Configuration, `ConfigurationLift, `HeatKernel, `RieszKernel, `BoundedBackground,
  `NormalizedTilt, `PairEnergy, `ProductDensity, `GibbsWeight, `CanonicalLaw,
  `BackgroundPotential, `BackgroundPairMean, `SmoothCore, `CollisionSet,
  `CollisionFreeCore, `CoordinateGradient, `GradientGraphClosure,
  `GradientFormDomain, `ClosedGradientEnergy, `ExtendedEntropy]

private def periodicTheoremNames : Array Name := #[
  `UniformFullGradientInequalities, `ModulatedFullGradientInequalities,
  `ExternalPotentialFullGradientInequalities]

private def namesJson (ns : List Name) : Json :=
  toJson (ns.map toString)

private def hintsJson : ReducibilityHints → Json
  | .opaque => Json.mkObj [("kind", toJson "opaque")]
  | .abbrev => Json.mkObj [("kind", toJson "abbrev")]
  | .regular h => Json.mkObj [("kind", toJson "regular"), ("height", toJson h.toNat)]

private def kindName : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def fields (c : ConstantInfo) : List (String × Json) := Id.run do
  let common := [
    ("kind", toJson (kindName c)),
    ("name", toJson (toString c.name)),
    ("levelParams", namesJson c.levelParams),
    ("type", toJson (reprStr c.type))]
  let extra := match c with
    | .defnInfo v => [
        ("value", toJson (reprStr v.value)), ("hints", hintsJson v.hints),
        ("safety", toJson (reprStr v.safety)), ("all", namesJson v.all)]
    | .thmInfo v => [("value", toJson (reprStr v.value)), ("all", namesJson v.all)]
    | .opaqueInfo v => [
        ("value", toJson (reprStr v.value)), ("isUnsafe", toJson v.isUnsafe),
        ("all", namesJson v.all)]
    | .axiomInfo v => [("isUnsafe", toJson v.isUnsafe)]
    | .inductInfo v => [
        ("numParams", toJson v.numParams), ("numIndices", toJson v.numIndices),
        ("all", namesJson v.all), ("ctors", namesJson v.ctors),
        ("numNested", toJson v.numNested), ("isRec", toJson v.isRec),
        ("isUnsafe", toJson v.isUnsafe), ("isReflexive", toJson v.isReflexive)]
    | .ctorInfo v => [
        ("induct", toJson (toString v.induct)), ("cidx", toJson v.cidx),
        ("numParams", toJson v.numParams), ("numFields", toJson v.numFields),
        ("isUnsafe", toJson v.isUnsafe)]
    | .recInfo v => [
        ("all", namesJson v.all), ("numParams", toJson v.numParams),
        ("numIndices", toJson v.numIndices), ("numMotives", toJson v.numMotives),
        ("numMinors", toJson v.numMinors), ("k", toJson v.k),
        ("isUnsafe", toJson v.isUnsafe),
        ("rules", Json.arr (v.rules.toArray.map fun r => Json.mkObj [
          ("ctor", toJson (toString r.ctor)), ("nfields", toJson r.nfields),
          ("rhs", toJson (reprStr r.rhs))]))]
    | .quotInfo v => [("quotKind", toJson (match v.kind with
        | .type => "type" | .ctor => "constructor" | .lift => "lift" | .ind => "induction"))]
  return common ++ extra

private def emit (xs : List (String × Json)) : IO Unit :=
  IO.println (Json.mkObj xs).compress

private def moduleOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => toString (env.header.moduleNames[i.toNat]!)
  | none => "<unrecorded>"

private def compareOne (challenge solution : Environment) (n : Name)
    (namedTheorem : Bool) : IO Bool := do
  let some c := challenge.find? n
    | emit [("event", toJson "missing_challenge"), ("name", toJson (toString n))]; return false
  let some s := solution.find? n
    | emit [("event", toJson "missing_solution"), ("name", toJson (toString n)),
        ("challenge_module", toJson (moduleOf challenge n))]; return false
  -- Configured theorem proofs intentionally differ. Match the same ConstantVal
  -- boundary that Lake.Check.compareAt uses, then inspect all other fields.
  let same := if namedTheorem then
      kindName c == kindName s && c.toConstantVal == s.toConstantVal
    else c == s
  emit [("event", toJson "constant"), ("name", toJson (toString n)),
    ("equal", toJson same), ("named_theorem", toJson namedTheorem),
    ("challenge_module", toJson (moduleOf challenge n)),
    ("solution_module", toJson (moduleOf solution n))]
  if !same then
    let cf := fields c
    let sf := fields s
    let mut keys := cf.map Prod.fst
    for (k, _) in sf do
      if !keys.contains k then keys := keys ++ [k]
    let mut explained := false
    for k in keys do
      if namedTheorem && (k == "value" || k == "all") then continue
      let cv := cf.lookup k
      let sv := sf.lookup k
      if cv != sv then
        explained := true
        emit [("event", toJson "field_mismatch"), ("name", toJson (toString n)),
          ("field", toJson k), ("challenge", cv.getD Json.null),
          ("solution", sv.getD Json.null)]
    if !explained then
      emit [("event", toJson "unexplained_raw_mismatch"), ("name", toJson (toString n)),
        ("challenge", Json.mkObj cf), ("solution", Json.mkObj sf)]
  return same

public def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let challengeModule := (args[0]?.getD "Challenge").toName
  let solutionModule := (args[1]?.getD "Solution").toName
  let component := args[2]?.getD "whole-space"
  let (fixedNames, theoremNames) ← match component with
    | "whole-space" => pure (wholeSpaceFixedNames, wholeSpaceTheoremNames)
    | "periodic" => pure (periodicFixedNames, periodicTheoremNames)
    | _ => throw (IO.userError s!"Unknown component {component}; expected whole-space or periodic")
  let challenge ← importModules #[{ module := challengeModule }] {}
  let solution ← importModules #[{ module := solutionModule }] {}
  emit [("event", toJson "environments"),
    ("challenge", toJson (toString challengeModule)),
    ("solution", toJson (toString solutionModule)),
    ("separate_environments", toJson true)]
  let mut names := fixedNames ++ theoremNames
  -- Include every generated field, constructor, recursor, instance and helper
  -- belonging to the Challenge module, not merely the selected hand-listed roots.
  let some challengeIdx := challenge.getModuleIdx? challengeModule
    | throw (IO.userError s!"No module index for {challengeModule}")
  for (n, _) in challenge.constants.toList do
    if challenge.getModuleIdxFor? n == some challengeIdx && !names.contains n then
      names := names.push n
  names := names.qsort (fun a b => a.toString < b.toString)
  let mut equal := 0
  let mut different := 0
  for n in names do
    if ← compareOne challenge solution n (theoremNames.contains n) then
      equal := equal + 1
    else different := different + 1
  emit [("event", toJson "summary"), ("checked", toJson names.size),
    ("equal", toJson equal), ("different_or_missing", toJson different),
    ("fixed_roots", toJson fixedNames.size)]
