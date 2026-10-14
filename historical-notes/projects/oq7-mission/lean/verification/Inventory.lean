import OQ7Mission
import Lean.Util.FoldConsts

run_cmd do
  let env ← Lean.getEnv
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "OQ7Mission." ||
        name.toString.startsWith "_private.OQ7Mission." then
      let kind := match info with
        | .thmInfo _ => "theorem"
        | .axiomInfo _ => "axiom"
        | .defnInfo _ => "definition"
        | .opaqueInfo _ => "opaque"
        | _ => "other"
      Lean.logInfo m!"OQ7MISSION-NODE {kind} {name}"
      for dep in info.type.getUsedConstants do
        Lean.logInfo m!"OQ7MISSION-EDGE {name} type {dep}"
      if let some proof := info.value? (allowOpaque := true) then
        for dep in proof.getUsedConstants do
          Lean.logInfo m!"OQ7MISSION-EDGE {name} value {dep}"
