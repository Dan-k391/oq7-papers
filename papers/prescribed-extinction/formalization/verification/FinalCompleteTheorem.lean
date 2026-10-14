import PrescribedExtinction

example : OQ7Prescribed.PhysicalTheorem11Statement := OQ7Prescribed.theorem11_complete
#check OQ7Prescribed.theorem11_complete
#print OQ7Prescribed.PhysicalTheorem11Statement
#print OQ7Prescribed.FullPhysicalOpticalStatement
#print axioms OQ7Prescribed.theorem11_complete

run_cmd do
  let env ← Lean.getEnv
  match env.find? `OQ7Prescribed.theorem11_complete with
  | some (.thmInfo info) =>
    unless info.type == Lean.mkConst `OQ7Prescribed.PhysicalTheorem11Statement do
      throwError "Complete proof declaration has a different statement"
    let axioms ← Lean.collectAxioms `OQ7Prescribed.theorem11_complete
    for name in axioms do
      unless name == `propext || name == `Classical.choice || name == `Quot.sound do
        throwError "Unexpected transitive complete-theorem axiom: {name}"
    Lean.logInfo "VERIFIED-COMPLETE-PHYSICAL-THEOREM11: kernel theorem declaration with exactly PhysicalTheorem11Statement"
  | _ => throwError "Complete physical declaration is missing or is not a theorem"
