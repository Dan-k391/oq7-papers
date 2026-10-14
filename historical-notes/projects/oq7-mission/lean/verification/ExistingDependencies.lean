import OQ7
import Lean.Util.FoldConsts

/- Read-only proof/type dependency traversal, starting at the saved theorem51.
   The traversal expands every reachable OQ7 constant. Mathlib/Lean constants are
   recorded as direct external edges; their full dependency closure is not claimed. -/
run_cmd do
  let env ← Lean.getEnv
  let mut seen : Lean.NameSet := {}
  let mut work := #[`OQ7.theorem51]
  while !work.isEmpty do
    let name := work.back!
    work := work.pop
    if !seen.contains name then
      seen := seen.insert name
      let some info := env.find? name | throwError "Missing constant {name}"
      let kind := match info with
        | .thmInfo _ => "theorem"
        | .axiomInfo _ => "axiom"
        | .defnInfo _ => "definition"
        | .opaqueInfo _ => "opaque"
        | _ => "other"
      Lean.logInfo m!"OQ7EXISTING-NODE {kind} {name}"
      for dep in info.type.getUsedConstants do
        Lean.logInfo m!"OQ7EXISTING-EDGE {name} type {dep}"
        if dep.toString.startsWith "OQ7." then
          work := work.push dep
      if let some proof := info.value? (allowOpaque := true) then
        for dep in proof.getUsedConstants do
          Lean.logInfo m!"OQ7EXISTING-EDGE {name} value {dep}"
          if dep.toString.startsWith "OQ7." then
            work := work.push dep

