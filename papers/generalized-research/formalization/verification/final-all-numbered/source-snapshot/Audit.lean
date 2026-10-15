import GeneralizedResearch
import Lean.Util.CollectAxioms

/-! Re-runnable exhaustive census of every theorem in the new namespace.
The aggregate import must first compile successfully. This check rejects every
transitive axiom outside Lean's ordinary propext/choice/quotient foundations,
and prints each exact theorem type for statement-correspondence review. -/

set_option pp.fullNames true
set_option pp.universes true
set_option pp.funBinderTypes true

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let declarations := env.constants.toList.filter fun (name, info) =>
    (`GeneralizedResearch).isPrefixOf name && info.isTheorem
  let declarations := declarations.toArray.qsort fun x y => x.1.lt y.1
  logInfo m!"THEOREM_CENSUS_COUNT {declarations.size}"
  for (name, info) in declarations do
    let axioms ← Lean.collectAxioms name
    let forbidden := axioms.filter fun axiomName =>
      axiomName != `propext && axiomName != `Classical.choice && axiomName != `Quot.sound
    if !forbidden.isEmpty then
      throwError m!"Nonstandard axioms for {name}: {forbidden.toList}"
    logInfo m!"THEOREM {name}"
    logInfo m!"TYPE {info.type}"
    logInfo m!"AXIOMS {axioms.toList}"
  for (name, info) in env.constants.toList do
    if (`GeneralizedResearch).isPrefixOf name then
      match info with
      | .axiomInfo _ => throwError m!"New axiom declaration: {name}"
      | _ => pure ()
