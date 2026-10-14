import OQ7

namespace OQ7IntegrityScratch
theorem admitted_false : False := by
  admit
#print axioms admitted_false
end OQ7IntegrityScratch

run_cmd do
  let env ← Lean.getEnv
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "OQ7IntegrityScratch." then
      match info with
      | .thmInfo _ =>
          Lean.logInfo m!"INTEGRITY-THEOREM {name}"
          let axioms ← Lean.collectAxioms name
          for ax in axioms do
            Lean.logInfo m!"INTEGRITY-DEPENDENCY {name} {ax}"
          Lean.logInfo m!"INTEGRITY-CENSUS-DONE {name}"
      | .axiomInfo _ => Lean.logInfo m!"INTEGRITY-AXIOM {name}"
      | _ => pure ()