import OQ7
import PrescribedExtinction

/-! Exhaustive project inventory, including private Newton heat helpers.
The preceding inventory file is preserved unchanged. -/
run_cmd do
  let env ← Lean.getEnv
  for (name, info) in env.constants.toList do
    let s := name.toString
    if s.startsWith "OQ7." || s.startsWith "OQ7Prescribed." ||
        s.startsWith "_private.OQ7." || s.startsWith "_private.PrescribedExtinction." then
      Lean.logInfo m!"AUDIT-CONSTANT {name}"
      match info with
      | .thmInfo _ => Lean.logInfo m!"AUDIT-THEOREM {name}"
      | .axiomInfo _ => Lean.logInfo m!"AUDIT-CUSTOM-AXIOM {name}"
      | _ => pure ()
