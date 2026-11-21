import AmortizedBound
import Lean.Util.CollectAxioms

open Lean Elab Command in
private def amortizedProofDependencies (env : Environment) (root : Name) : NameSet := Id.run do
  let mut todo := #[root]
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some decl := env.find? name | continue
    let some i := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[i.toNat]! == `AmortizedBound do continue
    for dep in decl.getUsedConstantsAsSet do
      unless seen.contains dep do todo := todo.push dep
  return seen

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  let mut thms := 0
  for (name, c) in env.constants.toList do
    let some i := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[i.toNat]! == `AmortizedBound do continue
    match c with
    | .axiomInfo a => unless a.isUnsafe do throwError "Local axiom {name}"
    | .thmInfo _ => names := names.push name; thms := thms + 1
    | .defnInfo d => if d.safety matches .safe then names := names.push name
    | .opaqueInfo o => unless o.isUnsafe do names := names.push name
    | _ => pure ()
  if thms < 150 then throwError "Insufficient source coverage"
  let (_, state) := ((names.forM CollectAxioms.collect).run env).run {}
  let allowed := #[`propext,`Classical.choice,`Quot.sound]
  let extra := state.axioms.filter fun n => !allowed.contains n
  unless extra.isEmpty do throwError "Unexpected axioms {extra}"
  logInfo m!"Checked {names.size} declarations ({thms} theorems including generated lemmas), axioms {state.axioms}."
  let shared := #[`AmortizedBound.Communication.robust_communication,`AmortizedBound.Intersection.intersection_bound,
    `AmortizedBound.Protocol.Snapshot.fixed_snapshot,`AmortizedBound.PublicScore.select,`AmortizedBound.GameBound.excludes,
    `AmortizedBound.ActualCharge.cost_bound,`AmortizedBound.Simulation.Accounting.actual_disjoint,
    `AmortizedBound.Dynamic.Epoch.snapshot_query_common,`AmortizedBound.Protocol.Snapshot.accepted_iff,
    `AmortizedBound.PublicTapes.compressed_error,`AmortizedBound.Conclusions.fourth_root,`AmortizedBound.Parameters.encoded_budgets]
  for (root, individual) in [( `AmortizedBound.total_work,`AmortizedBound.SpendingLimits.mixed),
                              ( `AmortizedBound.query_tradeoff,`AmortizedBound.SpendingLimits.single)] do
    let chain := amortizedProofDependencies env root
    for d in shared.push individual do
      unless chain.contains d do throwError "Missing dependency {d} in {root}"
    logInfo m!"Verified {root} depends on the operational budget, physical word simulation, public-tape selection, communication, and entropy-intersection arguments."

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (root, deps) in [
      (`AmortizedBound.GraphCorollaries.disjointness_maximum, #[`AmortizedBound.query_tradeoff]),
      (`AmortizedBound.GraphCorollaries.total_work, #[`AmortizedBound.total_work,`AmortizedBound.GraphReductions.history_map]),
      (`AmortizedBound.GraphCorollaries.query_tradeoff, #[`AmortizedBound.query_tradeoff,`AmortizedBound.GraphReductions.history_map]),
      (`AmortizedBound.GraphCorollaries.maximum, #[`AmortizedBound.total_work,`AmortizedBound.GraphReductions.history_map]),
      (`AmortizedBound.TriangleCorollary.maximum_vertices, #[`AmortizedBound.TriangleCorollary.triangle_vertices,`AmortizedBound.GraphReductions.triangle_counts]),
      (`AmortizedBound.TriangleCorollary.triangle_vertices,
        #[`AmortizedBound.total_work,`AmortizedBound.TriangleReduction.sequence_exec,`AmortizedBound.TriangleGraph.true_answer,
          `AmortizedBound.TriangleCorollary.work_source])] do
    unless (env.find? root).isSome do throwError "Missing result {root}"
    let chain := amortizedProofDependencies env root
    for dep in deps do
      unless chain.contains dep do throwError "Missing proof dependency {dep} in {root}"
  logInfo "Verified the maximum-cost consequence and graph corollaries descend from the dynamic theorems and the concrete graph simulations."
