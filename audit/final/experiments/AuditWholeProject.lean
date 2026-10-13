import OQ7
import PrescribedExtinction
open Lean Elab Command
def auditorDeps (env : Environment) (roots : Array Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack : Array Name := roots
  while h : stack.size > 0 do
    let n := stack.back
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let mut used := ci.type.getUsedConstants
    match ci with
    | .defnInfo d => used := used ++ d.value.getUsedConstants
    | .thmInfo t => used := used ++ t.value.getUsedConstants
    | .opaqueInfo o => used := used ++ o.value.getUsedConstants
    | .inductInfo i => used := used ++ i.ctors.toArray ++ i.all.toArray
    | .ctorInfo c => used := used.push c.induct
    | .recInfo r =>
        used := used ++ r.all.toArray
        for rule in r.rules do used := used ++ rule.rhs.getUsedConstants
    | .quotInfo _ => pure ()
    | .axiomInfo _ => pure ()
    for u in used do
      unless seen.contains u do stack := stack.push u
  return seen


elab "#auditor_whole_project" : command => do
  let env ← getEnv
  let mut roots : Array Name := #[]
  for (n, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let m := env.header.moduleNames[idx.toNat]!
      let top := (m.components.headD `none).toString
      if top == "OQ7" || top == "PrescribedExtinction" then roots := roots.push n
  let all := auditorDeps env roots
  let mut axs : Array Name := #[]
  for n in all do
    if let some (.axiomInfo _) := env.find? n then axs := axs.push n
  let priv := roots.filter isPrivateName
  logInfo m!"project constants (roots): {roots.size}; private: {priv.size}; union of transitive deps: {all.size}"
  logInfo m!"axioms reachable from ANY project constant: {axs}"
#auditor_whole_project
