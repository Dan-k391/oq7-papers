import OQ7
import PrescribedExtinction

run_cmd do
  let env ← Lean.getEnv
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "OQ7." || name.toString.startsWith "OQ7Prescribed." then
      Lean.logInfo m!"AUDIT-CONSTANT {name}"
      match info with
      | .thmInfo _ => Lean.logInfo m!"AUDIT-THEOREM {name}"
      | .axiomInfo _ => Lean.logInfo m!"AUDIT-CUSTOM-AXIOM {name}"
      | _ => pure ()
