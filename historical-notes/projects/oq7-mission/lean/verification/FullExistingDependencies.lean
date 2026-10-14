import OQ7
import Lean.Util.FoldConsts
set_option maxHeartbeats 0

/- The original source/build remains untouched. Only its saved kernel terms
   are read, with all imported dependencies recursively expanded. -/
run_cmd do
  let env := (← Lean.getEnv).setExporting false
  let roots : Array Lean.Name := #[`OQ7.theorem51]
  let mut seen : Lean.NameSet := {}
  let mut work := roots
  let mut nodes : Array Lean.Json := #[]
  while !work.isEmpty do
    let name := work.back!
    work := work.pop
    if !seen.contains name then
      seen := seen.insert name
      let some info := env.find? name | throwError "Missing referenced kernel constant {name}"
      let kind := match info with
        | .thmInfo _ => "theorem"
        | .axiomInfo _ => "axiom"
        | .defnInfo _ => "definition"
        | .opaqueInfo _ => "opaque"
        | _ => "other"
      let typeDeps := info.type.getUsedConstants
      let valueDeps := match info.value? (allowOpaque := true) with
        | some proof => proof.getUsedConstants
        | none => #[]
      nodes := nodes.push (Lean.Json.mkObj [
        ("name", Lean.Json.str name.toString),
        ("kind", Lean.Json.str kind),
        ("typeConstants", Lean.Json.arr (typeDeps.map (fun n => Lean.Json.str n.toString))),
        ("valueConstants", Lean.Json.arr (valueDeps.map (fun n => Lean.Json.str n.toString)))])
      work := work ++ typeDeps ++ valueDeps
  let result := Lean.Json.mkObj [
    ("roots", Lean.Json.arr (roots.map (fun n => Lean.Json.str n.toString))),
    ("nodes", Lean.Json.arr nodes)]
  Lean.logInfo m!"OQ7FULL-JSON {result.compress}"

