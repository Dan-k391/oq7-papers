import OQ7

namespace OQ7IntegrityScratch
axiom injected_false : False
theorem intermediate_false : False := injected_false
theorem inherited_invalid_arithmetic : (1 : Nat) = 0 := False.elim intermediate_false
#print axioms inherited_invalid_arithmetic
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