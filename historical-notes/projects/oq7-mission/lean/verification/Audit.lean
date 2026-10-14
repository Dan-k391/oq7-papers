import OQ7Mission
import Lean.Util.CollectAxioms

run_cmd do
  let env ← Lean.getEnv
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "OQ7Mission." ||
        name.toString.startsWith "_private.OQ7Mission." then
      let axioms ← Lean.collectAxioms name
      if axioms.isEmpty then
        Lean.logInfo m!"'{name}' does not depend on any axioms"
      else
        let names := String.intercalate ", " (axioms.toList.map Lean.Name.toString)
        Lean.logInfo m!"'{name}' depends on axioms: [{names}]"
