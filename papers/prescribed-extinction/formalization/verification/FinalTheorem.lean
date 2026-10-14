import PrescribedExtinction

example : OQ7Prescribed.Theorem11Statement := OQ7Prescribed.theorem11
#check OQ7Prescribed.theorem11
#print axioms OQ7Prescribed.theorem11

run_cmd do
  let env ← Lean.getEnv
  match env.find? `OQ7Prescribed.theorem11 with
  | some (.thmInfo info) =>
    unless info.type == Lean.mkConst `OQ7Prescribed.Theorem11Statement do
      throwError "Final proof declaration has a different statement"
    let axioms ← Lean.collectAxioms `OQ7Prescribed.theorem11
    for name in axioms do
      unless name == `propext || name == `Classical.choice || name == `Quot.sound do
        throwError "Unexpected transitive final-theorem axiom: {name}"
    Lean.logInfo "VERIFIED-FINAL-THEOREM: kernel theorem declaration with exactly Theorem11Statement"
  | _ => throwError "Final declaration is missing or is not a theorem"
