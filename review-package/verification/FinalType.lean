import PrescribedExtinction
set_option pp.all true
set_option pp.universes true
set_option pp.fullNames true
#print OQ7Prescribed.PhysicalTheorem11Statement
#print OQ7Prescribed.Theorem11Statement
#print OQ7Prescribed.FullPhysicalOpticalStatement
#print OQ7Prescribed.MaterialAdmissible
#print OQ7Prescribed.TwoLayerBody
#print OQ7Prescribed.ScatteringState
run_cmd do
  let env ← Lean.getEnv
  match env.find? `OQ7Prescribed.theorem11_complete with
  | some (.thmInfo info) =>
      Lean.logInfo m!"FULLY-ELABORATED-FINAL-THEOREM-TYPE: {info.type}"
  | _ => throwError "Final declaration is missing or is not a theorem"
