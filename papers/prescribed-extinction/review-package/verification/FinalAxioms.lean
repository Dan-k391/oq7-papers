import PrescribedExtinction
example : OQ7Prescribed.PhysicalTheorem11Statement := OQ7Prescribed.theorem11_complete
#print axioms OQ7Prescribed.theorem11_complete
run_cmd do
  let env ← Lean.getEnv
  match env.find? `OQ7Prescribed.theorem11_complete with
  | some (.thmInfo info) =>
      unless info.type == Lean.mkConst `OQ7Prescribed.PhysicalTheorem11Statement do
        throwError "Final theorem has an unexpected type"
      let axioms ← Lean.collectAxioms `OQ7Prescribed.theorem11_complete
      for name in axioms do
        unless name == `propext || name == `Classical.choice || name == `Quot.sound do
          throwError "Disallowed transitive axiom: {name}"
      Lean.logInfo "STRICT-AXIOM-AND-EXACT-TYPE-PASS"
  | _ => throwError "Final declaration is not a kernel theorem"
