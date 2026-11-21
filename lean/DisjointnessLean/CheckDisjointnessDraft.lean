import DisjointnessDraft
import Lean.Util.CollectAxioms

/-! Audit the transitive axioms of the project's theorems and safe definitions.
The test also rejects any local axiom, including one unused by another theorem. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  let mut draftCount := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`DisjointnessDraft).isPrefixOf mod || (`DisjointnessFoundations).isPrefixOf mod do continue
    let checked : Bool := match info with
      | .thmInfo _ => true
      | .axiomInfo a => !a.isUnsafe
      | .defnInfo d => match d.safety with | .safe => true | _ => false
      | .opaqueInfo o => !o.isUnsafe
      | _ => false
    if checked then
      names := names.push name
      if (`DisjointnessDraft).isPrefixOf mod then draftCount := draftCount + 1
  if names.isEmpty then throwError "No project theorems found."
  let (_, state) := ((names.forM CollectAxioms.collect).run env).run {}
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let extra := state.axioms.filter fun n => !allowed.contains n
  unless extra.isEmpty do throwError "Unexpected axioms: {extra}"
  logInfo m!"Audited {draftCount} declarations from this draft and {names.size - draftCount} from its local foundations. Axioms {state.axioms}"

open Lean Elab Command in
private def localProofClosure (env : Environment) (root : Name) : NameSet := Id.run do
  let mut todo := #[root]
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some c := env.find? n | continue
    let some i := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[i.toNat]!
    unless (`DisjointnessDraft).isPrefixOf m || (`DisjointnessFoundations).isPrefixOf m do continue
    for dep in c.getUsedConstantsAsSet do
      unless seen.contains dep do todo := todo.push dep
  return seen

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots := #[
    `DisjointnessDraft.Native.main, `DisjointnessDraft.Native.maximum,
    `DisjointnessDraft.Transfer.Auxiliary.polynomial, `DisjointnessDraft.Transfer.Auxiliary.interleaved_polynomial,
    `DisjointnessDraft.Transfer.Compiler.polynomial,
    `DisjointnessDraft.Transfer.Compiler.lower, `DisjointnessDraft.Transfer.Compiler.rel_lower,
    `DisjointnessDraft.Reachability.directed, `DisjointnessDraft.Reachability.fixed_source,
    `DisjointnessDraft.Applications.GraphCosts.lower, `DisjointnessDraft.Applications.ReachCount.lower,
    `DisjointnessDraft.Applications.BooleanTargets.graphs, `DisjointnessDraft.Applications.BooleanTargets.sets,
    `DisjointnessDraft.Applications.DistanceLower.lower, `DisjointnessDraft.Applications.SubgraphCosts.lower,
    `DisjointnessDraft.Applications.MatchingGraph.lower, `DisjointnessDraft.Applications.DensityGraph.lower,
    `DisjointnessDraft.Applications.PlanarTarget.lower, `DisjointnessDraft.Applications.UnitTarget.lower,
    `DisjointnessDraft.Applications.WeightedGirth.lower, `DisjointnessDraft.Applications.UnitGirthNative.lower,
    `DisjointnessDraft.Applications.DiameterGraph.lower, `DisjointnessDraft.Applications.DiameterEmpty.lower,
    `DisjointnessDraft.Applications.MatchingLower.lower, `DisjointnessDraft.Applications.MatchingLower.planar_lower,
    `DisjointnessDraft.Applications.SetDisjointness.lower, `DisjointnessDraft.Applications.Langerman.lower,
    `DisjointnessDraft.Applications.Pagh.lower, `DisjointnessDraft.Applications.Erickson.lower,
    `DisjointnessDraft.Applications.RangeMode.lower, `DisjointnessDraft.Applications.MatrixStringLower.matrices,
    `DisjointnessDraft.Applications.MaximaCosts.lower, `DisjointnessDraft.Applications.GeometricCosts.lower,
    `DisjointnessDraft.Applications.HullClassification.integer_lower, `DisjointnessDraft.Applications.MatrixStringLower.strings,
    `DisjointnessDraft.Streaming.selector_lower, `DisjointnessDraft.Streaming.some_symbol,
    `DisjointnessDraft.Streaming.Binary.lower, `DisjointnessDraft.Streaming.Binary.Indexed.uniform_lower]
  for root in roots do
    unless (env.find? root).isSome do throwError "Missing theorem {root}."
    let proof := localProofClosure env root
    for name in #[`DisjointnessDraft.Native.physical_lower, `DisjointnessDraft.PhysicalProtocol.Snapshot.acceptance_upper,
        `DisjointnessDraft.Corruption.product_corruption, `DisjointnessDraft.Corruption.chain_with_source_rows] do
      unless proof.contains name do throwError "Missing dependency {name} in {root}."
  logInfo m!"Checked {roots.size} principal results and application bounds against the native simulation, communication and corruption proof."
