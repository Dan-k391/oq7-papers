import OQ7

run_cmd do
  let env ← Lean.getEnv
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "OQ7." then
      match info with
      | .thmInfo _ => Lean.logInfo m!"OQ7-AUDIT-THEOREM {name}"
      | .axiomInfo _ => Lean.logInfo m!"OQ7-AUDIT-AXIOM {name}"
      | _ => pure ()
